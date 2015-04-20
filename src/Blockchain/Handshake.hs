{-# LANGUAGE OverloadedStrings #-}

module Blockchain.Handshake (
  AckMessage(..),
  getHandshakeBytes,
  bytesToAckMsg,
  decryptECEIS
  ) where

import Crypto.Cipher.AES
import Crypto.Hash.SHA256
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.HMAC
import Data.Maybe
import qualified Network.Haskoin.Internals as H

import Blockchain.ExtendedECDSA
import Blockchain.ExtWord

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

data ECEISMessage =
  ECEISMessage {
    eceisMysteryByte::Word8,
    eceisPubKey::Point,
    eceisCipherIV::B.ByteString,
    eceisCipher::B.ByteString,
    eceisMac::[Word8]
    } deriving (Show)

instance Binary ECEISMessage where
  get = do
    mysteryByte <- getWord8
    pubKeyX <- fmap (toInteger . bytesToWord256 . B.unpack) $ getByteString 32
    pubKeyY <- fmap (toInteger . bytesToWord256 . B.unpack) $ getByteString 32
    cipherIV <- getByteString 16
    cipher <- getByteString 97
    mac <- sequence $ replicate 32 getWord8
    return $ ECEISMessage mysteryByte (Point pubKeyX pubKeyY) cipherIV cipher mac

  put (ECEISMessage mysteryByte (Point pubKeyX pubKeyY) cipherIV cipher mac) = do
    putWord8 mysteryByte
    putByteString (B.pack . word256ToBytes . fromInteger $ pubKeyX)
    putByteString (B.pack . word256ToBytes . fromInteger $ pubKeyY)
    putByteString cipherIV
    putByteString cipher
    sequence_ $ map putWord8 mac
  put x = error $ "unsupported case in call to put for ECEISMessage: " ++ show x

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

encryptECEIS::PrivateNumber->PublicPoint->B.ByteString->B.ByteString->ECEISMessage
encryptECEIS myPrvKey otherPubKey cipherIV msg =
  ECEISMessage {
    eceisMysteryByte = 4,
    eceisPubKey=calculatePublic theCurve myPrvKey,
    eceisCipherIV=cipherIV,
    eceisCipher=cipher,
    eceisMac=hmac (HashMethod (B.unpack . hash . B.pack) 512) (B.unpack mKey) (B.unpack cipherWithIV)
    }
  where
    SharedKey sharedKey = getShared theCurve myPrvKey otherPubKey
    key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
    eKey = B.take 16 key
    mKeyMaterial = B.take 16 $ B.drop 16 key
    mKey = hash mKeyMaterial
    cipher = encrypt eKey cipherIV msg
    cipherWithIV = cipherIV `B.append` cipher

decryptECEIS::PrivateNumber->ECEISMessage->B.ByteString
decryptECEIS myPrvKey msg =
  decryptCTR (initAES eKey) (eceisCipherIV msg) (eceisCipher msg)
  where
    SharedKey sharedKey = getShared theCurve myPrvKey (eceisPubKey msg)
    key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
    eKey = B.take 16 key

getHandshakeBytes::PrivateNumber->PublicPoint->B.ByteString->IO B.ByteString
getHandshakeBytes myPriv otherPubKey myNonce = do
  let
    myPublic = calculatePublic theCurve myPriv
    SharedKey sharedKey = getShared theCurve myPriv otherPubKey
    cipherIV = B.replicate 16 0 --TODO- Important!  Is this really supposed to be zero?
    msg = fromIntegral sharedKey `xor` (bytesToWord256 $ B.unpack myNonce)
  sig <- H.withSource H.devURandom $ extSignMsg msg (H.PrvKey $ fromIntegral myPriv)
  let
    ephemeral = getPubKeyFromSignature sig msg
    hepubk = SHA3.hash 256 $ B.pack $ pubKeyToBytes ephemeral
    pubk = B.pack $ pointToBytes myPublic
    theData = B.pack (sigToBytes sig) `B.append`
                hepubk `B.append`
                pubk `B.append`
                myNonce `B.append`
                B.singleton 0


  return $ BL.toStrict $ encode $ encryptECEIS myPriv otherPubKey cipherIV theData 


