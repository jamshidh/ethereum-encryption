{-# LANGUAGE OverloadedStrings #-}

module Blockchain.Handshake (
  AckMessage(..),
  getHandshakeBytes,
  bytesToAckMsg,
  bytesToPoint,
  pointToBytes,
  decryptECEIS,
  encryptECEIS,
  ECEISMessage(..)
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
-- import Debug.Trace

theCurve::Curve
theCurve = getCurveByName SEC_p256k1

intToBytes::Integer->[Word8]
intToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

pointToBytes::Point->[Word8]
pointToBytes (Point x y) = intToBytes x ++ intToBytes y
pointToBytes PointO = error "pointToBytes got value PointO, I don't know what to do here"

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
    eceisForm::Word8, --See ansi x9.62 section 4.3.6 (I currently only handle form=4)
    eceisPubKey::Point,
    eceisCipherIV::B.ByteString,
    eceisCipher::B.ByteString,
    eceisMac::[Word8]
    } deriving (Show)

instance Binary ECEISMessage where
  get = do
    bs <- getRemainingLazyByteString
    let bsStrict = BL.toStrict $ bs
        length  =  B.length $ bsStrict
        form = head . B.unpack $ bsStrict
        pubKeyX =  toInteger . bytesToWord256 . B.unpack $ B.take 32 $ B.drop 1 $ bsStrict
        pubKeyY =  toInteger . bytesToWord256 . B.unpack $ B.take 32 $ B.drop 33 $ bsStrict
        cipherIV = B.take 16 $ B.drop 65 $ bsStrict
        cipher = B.take (length - 113) $ B.drop 81 $ bsStrict
        mac = B.unpack $ B.take 32 $ B.drop (length-32) bsStrict
    -- form <- getWord8
    -- pubKeyX <- fmap (toInteger . bytesToWord256 . B.unpack) $ getByteString 32
    -- pubKeyY <- fmap (toInteger . bytesToWord256 . B.unpack) $ getByteString 32
    -- cipherIV <- getByteString 16
    -- cipher <- getByteString (length - (113))  
    -- mac <- sequence $ replicate 32 getWord8
    return $ ECEISMessage form (Point pubKeyX pubKeyY) cipherIV cipher mac

  put (ECEISMessage form (Point pubKeyX pubKeyY) cipherIV cipher mac) = do
    putWord8 form
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


knownPeer :: Word8 -> Bool
knownPeer b =
  case b of
    0 -> False
    1 -> True
    _ -> error "byte is neither 0 nor 1"

boolToWord8 :: Bool -> Word8
boolToWord8 True = 1
boolToWord8 False = 0


instance Binary AckMessage where
  get = do
    point <- fmap (bytesToPoint . B.unpack) $ getByteString 64
    nonce <- fmap (bytesToWord256 . B.unpack) $ getByteString 32                   
    kp <- fmap (knownPeer . head . B.unpack) $ getByteString 1
    return $ (AckMessage point nonce kp)
    
  put (AckMessage point nonce kp) = do
    putByteString $ (B.pack . pointToBytes) $ point
    putByteString (B.pack . word256ToBytes $ nonce)
    putByteString (B.pack $ [(boolToWord8 kp)])
  put x = error $ "unsupported case in call to put for AckMessage: " ++ show x
    
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
    eceisForm = 4, --form=4 indicates pubkey is not compressed
    eceisPubKey=calculatePublic theCurve myPrvKey,
    eceisCipherIV=cipherIV,
    eceisCipher=cipher,
    eceisMac= --trace ("################### mkey: " ++ show mKey) $
	--trace ("################### cipherWithIV: " ++ show cipherWithIV) $
        hmac (HashMethod (B.unpack . hash . B.pack) 512) (B.unpack mKey) (B.unpack cipherWithIV)
    }
  where
    SharedKey sharedKey = --trace ("##################### sharedKey: " ++ show (getShared theCurve myPrvKey otherPubKey)) $
                          getShared theCurve myPrvKey otherPubKey
    key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
    eKey = B.take 16 key
    mKeyMaterial = -- trace ("##################### sharedKey: " ++ show (B.take 16 $ B.drop 16 key)) $
                   (B.take 16 $ B.drop 16 key)
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


 --  putStrLn $ "sharedKey: " ++ show sharedKey
  -- putStrLn $ "msg:       " ++ show msg
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
  -- putStrLn $ "ephemeral: " ++ show ephemeral
  -- putStrLn $ "hepubk: " ++ show hepubk
  -- putStrLn $ "pubk: " ++ show pubk
  -- putStrLn $ "theData: " ++ show theData

  let eceisMsg = encryptECEIS myPriv otherPubKey cipherIV theData 
  let eceisMsgBytes = BL.toStrict $ encode eceisMsg
  
  -- putStrLn $ "eceisMsg: "
  -- putStrLn $ show eceisMsg

  -- putStrLn $ "length ciphertext: " ++ (show . B.length $ eceisCipher eceisMsg)
  -- putStrLn $ "length of wire message: " ++ (show . B.length $ eceisMsgBytes)
  
  return $ eceisMsgBytes


