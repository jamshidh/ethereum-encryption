{-# LANGUAGE OverloadedStrings #-}

module Main (
  main
  ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Crypto.Cipher.AES
import Crypto.Hash.SHA256
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Crypto.Random
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import Data.HMAC
import Data.Maybe
import Data.Word
import Network
import qualified Network.Haskoin.Internals as H
import Numeric

import Blockchain.ExtendedECDSA
import Blockchain.ExtWord
import Blockchain.Data.RLP
import Blockchain.Data.Wire

import qualified AESCTR as AES
import Frame
import UDP

--import Debug.Trace

theCurve::Curve
theCurve = getCurveByName SEC_p256k1

intToBytes::Integer->[Word8]
intToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

pointToBytes::Point->[Word8]
pointToBytes (Point x y) = intToBytes x ++ intToBytes y

showPoint::Point->String
showPoint (Point x y) =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""

hShowPoint::H.Point->String
hShowPoint point =
  "Point " ++ showHex x "" ++ " " ++ showHex y ""
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point


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
bXor x y | B.length x == B.length y =
  B.pack $ map (uncurry xor) $ zip (B.unpack x) (B.unpack y) 
bXor _ _ = error "bXor called with two ByteStrings of different length"

data ECEISMessage =
  ECEISMessage {
    eceisMysteryByte::Word8,
    eceisPubKey::Point,
    eceisCipherIV::Word128,
    eceisCipher::B.ByteString,
    eceisMac::[Word8]
    } deriving (Show)

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
    ackKnownPeer=case bytes !! 96 of 0 -> False;  1 -> True
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

--sendFrame::B.ByteString->IO ()
sendFrame handle state ingressMac macEncKey frameDecKey frameData = do
  let 
      bufferedFrameData = frameData `B.append` B.replicate ((16 - (B.length frameData `mod` 16)) `mod` 16) 0
      (state'', frameCipher) = AES.encrypt state' bufferedFrameData
      frameSize = B.length frameData
      bufferedCipherData = frameCipher --  `B.append` B.replicate (16*(ceiling (fromIntegral frameSize/16.0)) - frameSize) 0

      (state', headerData) = AES.encrypt state $
               B.pack [fromIntegral $ frameSize `shiftR` 16,
                       fromIntegral $ frameSize `shiftR` 8,
                       fromIntegral frameSize,
                       0xc2,
                       0x80,
                       0x80,
                       0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    
      ingressMac' = SHA3.update ingressMac $ headerData `bXor` (encryptECB (initAES macEncKey) (B.take 16 $ SHA3.finalize ingressMac))

      thing2 = B.take 16 $ SHA3.finalize ingressMac'

  B.hPut handle $ headerData `B.append` thing2

-------------------

  let 

      
      oldDigest = B.take 16 $ SHA3.finalize ingressMac''
      prePreUpdateData = B.take 16 $ SHA3.finalize ingressMac''
      preUpdateData = encryptECB (initAES macEncKey) (B.take 16 $ SHA3.finalize ingressMac'')
      updateData = oldDigest `bXor` (encryptECB (initAES macEncKey) (B.take 16 $ SHA3.finalize ingressMac''))
      ingressMac'' = SHA3.update ingressMac' bufferedCipherData
      ingressMac''' = SHA3.update ingressMac'' updateData
      thing2' = B.take 16 $ SHA3.finalize ingressMac'''
      payload = bufferedCipherData `B.append` thing2'

  B.hPut handle payload

  return (state'', ingressMac''')


main::IO ()    
main = do

  serverPubKey <- getServerPubKey "127.0.0.1" 30303
  
  handle <- connectTo "127.0.0.1" $ PortNumber 30303

  putStrLn "Connected"
  entropyPool <- createEntropyPool
  let g = cprgCreate entropyPool :: SystemRNG
  let 
      (myPriv, g') = generatePrivate g theCurve
      myPublic = calculatePublic theCurve myPriv
      H.PubKey point = serverPubKey
      x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
      y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
      otherPublic = Point (fromIntegral x) (fromIntegral y)
      SharedKey sharedKey = getShared theCurve myPriv otherPublic
  
  putStrLn $ "priv: " ++ showHex myPriv ""
  putStrLn $ "shared: " ++ showHex sharedKey ""
  let (Point x' y') = myPublic
  putStrLn $ "public: " ++ hShowPoint point

  putStrLn $ "serverPubKey: " ++ showPoint otherPublic

  let 
      cipherIV = 0::Word128

      nonce = 20::Word256
      msg = fromIntegral sharedKey `xor` nonce
  

  putStrLn $ "msg: " ++ showHex msg ""
  sig <- H.withSource H.devURandom $ extSignMsg msg (H.PrvKey $ fromIntegral myPriv)

  let ephemeral = getPubKeyFromSignature sig (fromInteger sharedKey `xor` nonce)
  
      hepubk = SHA3.hash 256 $ B.pack $ pubKeyToBytes ephemeral
      pubk = pointToBytes myPublic
      theData = sigToBytes sig ++ B.unpack hepubk ++ pubk ++ word256ToBytes nonce ++ [0] -- [1..306-64-16-32]

  putStrLn $ "sigToBytes sig: " ++ show (length $ sigToBytes sig) ++ " " ++ show (sigToBytes sig)
  putStrLn $ "B.unpack hepubk: " ++ show (length $ B.unpack hepubk) ++ ", " ++ show (B.unpack hepubk)
  putStrLn $ "pubk: " ++ show (length pubk) ++ ", " ++ show pubk
  putStrLn $ "word256ToBytes nonce: " ++ show (length $ word256ToBytes nonce) ++ ", " ++ show (word256ToBytes nonce)

  let eceisMessage = encryptECEIS myPriv otherPublic cipherIV $ B.pack theData 

  BL.hPut handle $ BL.pack $ eceisMsgToBytes eceisMessage

  --reply <- BL.hGet handle 386
  reply <- BL.hGet handle 210

  let replyECEISMsg = bytesToECEISMsg $ BL.unpack reply

  let ackMsg = bytesToAckMsg $ B.unpack $ decryptECEIS myPriv replyECEISMsg

  putStrLn $ "decrypted reply: " ++ show ackMsg
  putStrLn $ "ackEphemeralPubKey: " ++ showPoint (ackEphemeralPubKey ackMsg)
  putStrLn $ "ackNonce: " ++ showHex (ackNonce ackMsg) ""


------------------------------

  let m_originated=False
      add::B.ByteString->B.ByteString->B.ByteString
      add acc val | B.length acc ==32 && B.length val == 32 = SHA3.hash 256 $ val `B.append` acc
      add _ _ = error "add called with ByteString of length not 32"

      m_remoteNonce=word256ToBytes nonce
      m_nonce=B.pack $ word256ToBytes $ ackNonce ackMsg

      m_authCipher=B.pack $ eceisMsgToBytes eceisMessage
      m_ackCipher=BL.toStrict reply
  

  putStrLn $ "m_originated=" ++ show m_originated
--  putStrLn $ "m_remoteEphemeral=" ++ show m_remoteEphemeral
  putStrLn $ "m_nonce=" ++ BC.unpack (B16.encode m_nonce)
  putStrLn $ "m_remoteNonce=" ++ BC.unpack (B16.encode $ B.pack m_remoteNonce)
  putStrLn $ "m_authCipher=" ++ BC.unpack (B16.encode m_authCipher)
  putStrLn $ "m_ackCipher=" ++ BC.unpack (B16.encode m_ackCipher)
--  putStrLn $ "secret=0x" ++ showHex secret ""


  let 
--      SharedKey shared' = getShared theCurve secret m_remoteEphemeral
      SharedKey shared' = getShared theCurve myPriv (ackEphemeralPubKey ackMsg)
      shared = B.pack $ intToBytes shared'

  putStrLn $ "server public: " ++ showPoint (eceisPubKey replyECEISMsg)
  putStrLn $ "myPublic=" ++ showPoint myPublic
  putStrLn $ "shared=0x" ++ BC.unpack (B16.encode shared)

  
  let macEncKey = 
        (B.pack m_remoteNonce) `add`
        m_nonce `add`
        shared `add`
        shared `add`
        shared

  let frameDecKey = 
        (B.pack m_remoteNonce) `add`
        m_nonce `add`
        shared `add`
        shared

      egressCipher = if m_originated then m_authCipher else m_ackCipher
      ingressCipher = if m_originated then m_ackCipher else m_authCipher


  let egressMac = SHA3.update (SHA3.init 256) $
                   (macEncKey `bXor` (B.pack m_remoteNonce)) `B.append` egressCipher

  let ingressMac = SHA3.update (SHA3.init 256) $ 
                    (macEncKey `bXor` (m_nonce)) `B.append` ingressCipher

-------------------------------

  let eState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0
  let dState = AES.AESCTRState (initAES frameDecKey) (aesIV_ $ B.replicate 16 0) 0

  (eState', ingressMac') <-
    sendFrame handle eState ingressMac macEncKey frameDecKey $
    B.pack [0x80] `B.append` rlpSerialize (RLPArray [rlpEncode (3::Integer), rlpEncode (0::Integer), rlpEncode (0::Integer), rlpEncode (0::Integer)])

  let state =
        EthCryptState {
          handle = handle,
          encryptState = eState',
          decryptState = dState
          }
  
  flip runStateT state $ do
    frameData <- getAndDecryptFrame
  
    liftIO $ print $ B.take 1 frameData
    liftIO $ print $ rlpDeserialize $ B.drop 1 frameData

---------------------

  let msg = Hello {version=3, clientId="qqqq", capability=[], port=30303, nodeId=0x1}

  _ <-
    sendFrame handle eState' ingressMac' macEncKey frameDecKey $
    B.pack [0x2] `B.append` rlpSerialize (wireMessage2Obj msg)


  qqqq <- BL.hGet handle 1000

  --print qqqq

  return ()
