{-# LANGUAGE OverloadedStrings #-}

module RLPx (
  runEthCryptM
  ) where

import Control.Monad.Trans.State
import Crypto.Cipher.AES
import Crypto.Hash.SHA256
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Data.Binary
import Data.Binary.Get
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.HMAC
import Data.Maybe
import Data.Word
import Network
import qualified Network.Haskoin.Internals as H

import Blockchain.ExtendedECDSA
import Blockchain.ExtWord

import qualified AESCTR as AES
import Frame

--import Debug.Trace

theCurve::Curve
theCurve = getCurveByName SEC_p256k1

intToBytes::Integer->[Word8]
intToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

pointToBytes::Point->[Word8]
pointToBytes (Point x y) = intToBytes x ++ intToBytes y
pointToBytes PointO = error "pointToBytes got value PointO, I don't know what to do here"

{-
showPoint::Point->String
showPoint (Point x y) =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""
showPoint PointO = error "showPoint got value PointO, I don't know what to do here"

hShowPoint::H.Point->String
hShowPoint point =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
-}

ctr::[Word8]
ctr=[0,0,0,1]

--z = replicate 32 0

s1::[Word8]
s1 = []

hPointToBytes::H.Point->[Word8]
hPointToBytes point =
  word256ToBytes (fromIntegral x) ++ word256ToBytes (fromIntegral y)
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point

pubKeyToBytes::H.PubKey->[Word8]
pubKeyToBytes (H.PubKey point) = hPointToBytes point
pubKeyToBytes (H.PubKeyU _) = error "Missing case in showPubKey: PubKeyU"

bytesToPoint::[Word8]->Point
bytesToPoint x | length x == 64 =
  Point (toInteger $ bytesToWord256 $ take 32 x) (toInteger $ bytesToWord256 $ drop 32 x)
bytesToPoint _ = error "bytesToPoint called with the wrong number of bytes"


sigToBytes::ExtendedSignature->[Word8]
sigToBytes (ExtendedSignature signature yIsOdd) =
  word256ToBytes (fromIntegral $ H.sigR signature) ++
  word256ToBytes (fromIntegral $ H.sigS signature) ++
  [if yIsOdd then 1 else 0]

bXor::B.ByteString->B.ByteString->B.ByteString
bXor x y | B.length x == B.length y = B.pack $ B.zipWith xor x y
bXor _ _ = error "bXor called with two ByteStrings of different length"

data ECEISMessage =
  ECEISMessage {
    eceisMysteryByte::Word8,
    eceisPubKey::Point,
    eceisCipherIV::Word128,
    eceisCipher::B.ByteString,
    eceisMac::[Word8]
    } deriving (Show)

instance Binary ECEISMessage where
  get = do
    mysteryByte <- getWord8
    pubKeyX <- fmap toInteger $ getWord32be
    pubKeyY <- fmap toInteger getWord32be
    cipherIV <- fmap fromIntegral $ getWord16be
    cipher <- getByteString 97
    mac <- sequence $ replicate 32 getWord8
    return $ ECEISMessage mysteryByte (Point pubKeyX pubKeyY) cipherIV cipher mac

  put = undefined

eceisMsgToBytes::ECEISMessage->[Word8]
eceisMsgToBytes msg =
  [eceisMysteryByte msg] ++
  pointToBytes (eceisPubKey msg) ++
  word128ToBytes (eceisCipherIV msg) ++
  B.unpack (eceisCipher msg) ++
  eceisMac msg

bytesToECEISMsg::[Word8]->ECEISMessage
bytesToECEISMsg (mysteryByte:rest) | cipherLen >= 0 =
  ECEISMessage {
    eceisMysteryByte=mysteryByte,
    eceisPubKey=bytesToPoint $ take 64 rest,
    eceisCipherIV=bytesToWord128 $ take 16 $ drop 64 rest,
    eceisCipher=B.pack $ take cipherLen $ drop 80 rest,
    eceisMac=drop (length rest - 32) rest
    }
  where cipherLen = length rest - 64 - 16 - 32
bytesToECEISMsg _ = error "empty byte list in call to bytesToECEISMsg"

data AckMessage =
  AckMessage {
    ackEphemeralPubKey::Point,
    ackNonce::Word256,
    ackKnownPeer::Bool
    } deriving (Show)

bytesToAckMsg::[Word8]->AckMessage
bytesToAckMsg bytes | length bytes == 97 =
  AckMessage {
    ackEphemeralPubKey=bytesToPoint $ take 64 bytes,
    ackNonce=bytesToWord256 $ take 32 $ drop 64 bytes,
    ackKnownPeer=
      case bytes !! 96 of
        0 -> False
        1 -> True
        _ -> error "known peer byte in ackMessage is neither 0 nor 1"
    }
bytesToAckMsg _ = error "wrong number of bytes in call to bytesToECEISMsg"



encrypt::B.ByteString->B.ByteString->B.ByteString->B.ByteString
encrypt key cipherIV input = encryptCTR (initAES key) cipherIV input 

encryptECEIS::PrivateNumber->PublicPoint->Word128->B.ByteString->ECEISMessage
encryptECEIS myPrvKey otherPubKey cipherIV msg =
  ECEISMessage {
    eceisMysteryByte = 2,
    eceisPubKey=calculatePublic theCurve myPrvKey,
    eceisCipherIV=cipherIV,
    eceisCipher=cipher,
    eceisMac=hmac (HashMethod (B.unpack . hash . B.pack) 512) (B.unpack mKey) cipherWithIV
    }
  where
    SharedKey sharedKey = getShared theCurve myPrvKey otherPubKey
    key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
    eKey = B.take 16 key
    mKeyMaterial = B.take 16 $ B.drop 16 key
    mKey = hash mKeyMaterial
    cipher = encrypt eKey (B.pack $ word128ToBytes cipherIV) msg
    cipherWithIV = word128ToBytes cipherIV ++ B.unpack cipher

decryptECEIS::PrivateNumber->ECEISMessage->B.ByteString
decryptECEIS myPrvKey msg =
  decryptCTR (initAES eKey) (B.pack $ word128ToBytes $ eceisCipherIV msg) (eceisCipher msg)
  where
    SharedKey sharedKey = getShared theCurve myPrvKey (eceisPubKey msg)
    key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
    eKey = B.take 16 key

runEthCryptM::PrivateNumber->PublicPoint->EthCryptM a->IO a
runEthCryptM myPriv otherPubKey f = do
  let myPublic = calculatePublic theCurve myPriv
  h <- connectTo "127.0.0.1" $ PortNumber 30303

  let
      SharedKey sharedKey = getShared theCurve myPriv otherPubKey
  
      cipherIV = 0::Word128 --TODO- Important!  Is this really supposed to be zero?
      myNonce = B.pack $ word256ToBytes 20 --TODO- Important!  Don't hardcode this
      msg = fromIntegral sharedKey `xor` (bytesToWord256 $ B.unpack myNonce)
  
  sig <- H.withSource H.devURandom $ extSignMsg msg (H.PrvKey $ fromIntegral myPriv)

  let ephemeral = getPubKeyFromSignature sig msg
  
      hepubk = SHA3.hash 256 $ B.pack $ pubKeyToBytes ephemeral
      pubk = B.pack $ pointToBytes myPublic
      theData = B.pack (sigToBytes sig) `B.append`
                hepubk `B.append`
                pubk `B.append`
                myNonce `B.append`
                B.singleton 0

      eceisMessage = encryptECEIS myPriv otherPubKey cipherIV theData 

  BL.hPut h $ BL.pack $ eceisMsgToBytes eceisMessage

  replyBytes <- B.hGet h 210
--  let replyECEISMsg = decode $ BL.fromStrict replyBytes
  let replyECEISMsg = bytesToECEISMsg $ B.unpack replyBytes

  let ackMsg = bytesToAckMsg $ B.unpack $ decryptECEIS myPriv replyECEISMsg


------------------------------

  let m_originated=False -- hardcoded for now, I can only connect as client
      add::B.ByteString->B.ByteString->B.ByteString
      add acc val | B.length acc ==32 && B.length val == 32 = SHA3.hash 256 $ val `B.append` acc
      add _ _ = error "add called with ByteString of length not 32"

      otherNonce=B.pack $ word256ToBytes $ ackNonce ackMsg

      m_authCipher=B.pack $ eceisMsgToBytes eceisMessage
  
      SharedKey shared' = getShared theCurve myPriv (ackEphemeralPubKey ackMsg)
      shared = B.pack $ intToBytes shared'

      frameDecKey = myNonce `add` otherNonce `add` shared `add` shared
      macEncKey = frameDecKey `add` shared

      ingressCipher = if m_originated then m_authCipher else replyBytes
      egressCipher = if m_originated then replyBytes else m_authCipher
  let cState =
        EthCryptState {
          handle = h,
          encryptState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0,
          decryptState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0,
          egressMAC=SHA3.update (SHA3.init 256) $
                    (macEncKey `bXor` otherNonce) `B.append` egressCipher,
          egressKey=macEncKey,
          ingressMAC=SHA3.update (SHA3.init 256) $ 
                     (macEncKey `bXor` myNonce) `B.append` ingressCipher,
          ingressKey=macEncKey
          }

  (ret, _) <- flip runStateT cState f

  return ret
  
