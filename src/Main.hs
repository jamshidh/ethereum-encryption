{-# LANGUAGE OverloadedStrings #-}

module Main (
  main
  ) where

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
import Data.HMAC
import Data.Maybe
import Data.Word
import Network
import qualified Network.Haskoin.Internals as H
import Numeric

import Blockchain.ExtendedECDSA
import Blockchain.ExtWord

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

  BL.hPut handle $ BL.pack $ replicate 100 0

  qqqq <- BL.hGet handle 386

  print qqqq

------------------------------

  let m_originated=False
      add::B.ByteString->B.ByteString->B.ByteString
      add acc val | B.length acc ==32 && B.length val == 32 = SHA3.hash 256 $ val `B.append` acc
      add _ _ = error "add called with ByteString of length not 32"

--      m_nonce=B.pack $ word256ToBytes nonce
--      m_remoteNonce=word256ToBytes $ ackNonce ackMsg
      m_remoteNonce=word256ToBytes nonce
      m_nonce=B.pack $ word256ToBytes $ ackNonce ackMsg

--      m_authCipher=B.pack theData --eceisCipher eceisMessage
--      m_ackCipher=decryptECEIS myPriv replyECEISMsg -- eceisCipher replyECEISMsg
  
      m_authCipher=B.pack $ eceisMsgToBytes eceisMessage
      m_ackCipher=BL.toStrict reply
  
{-
m_remoteEphemeral=Point 0xd68cf5d5268e8fa3abf5e235b749dc9255b29fb8f200d7ff1aa382a6656ecd28 0xb8f4baa263d2c01b2dd1f33e8ab7b37095a9d525f50a2f84c9cf5ec778ba2d52
m_nonce=fst $ B16.decode "3aa096cda02fb611f59590e7e1f913a9943b371214483c05e4a34528d5762e6b"
m_remoteNonce=fst $ B16.decode "0000000000000000000000000000000000000000000000000000000000000014"
m_authCipher=fst $ B16.decode "02d68cf5d5268e8fa3abf5e235b749dc9255b29fb8f200d7ff1aa382a6656ecd28b8f4baa263d2c01b2dd1f33e8ab7b37095a9d525f50a2f84c9cf5ec778ba2d52000000000000000000000000000000001a459d58e86fb0a74e3519cccb201d26e23f7a733b6187bfc7ece720d966329509fcd2f2dcd930c9d42aaf991270c8da7fa312bba42189c4ffff0c229eaaf60be6da018486c9dad3f0328a8f94e096aea2effb7796b26fe6ef1a3a1bd1502a6ebcca0300d113f24ccd2c007428654135e82d87007864c7fec3493e99cc1692748f55dee55d3480c68308d4f8734738e264c58b3743253ad83a955cac768ccaaca06fce24959a04aa1e2fe41874da3e772256cb9f24f1f8d231ba7779a9375e14a18bf379bf6e22e4e3c53d90ae06f79f19e0807b435ea045ec81ed02e9cc5973a3a1"
m_ackCipher=fst $ B16.decode "048af5d0207c418c5cd94bb83db97fa42bb230eab4f379fe26481c23b578b18f60261d20e24466ec9269da80c927bbb7a524a7669edf7547316ad9351f0d4b766e000000000000000000000000000000005593525c9c07aa4bd337fe6aa6a7d4e538f232b12f7de92ac21ea19699bae6cc70fee136f6b75f720a35b148f325e2853226c7d9bc0ecd6a46ccb9cd4f0c0d5c901ed195d122ebf027af7612cd6498aa9e71b04380fd7952df0c896de36b389fd48a604d962e6ed26da0c3608f0660478970dc6ce17c4def92dad6e1025eb7ed21"
secret=0xdfb39de778d7454cecc098a494220a8993dbd9a8ea059a8e628b3d4f9197862b
-}

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

      egressCipher = if m_originated then m_authCipher else m_ackCipher
      ingressCipher = if m_originated then m_ackCipher else m_authCipher


  let egressMac = SHA3.update (SHA3.init 256) $
                   (macEncKey `bXor` (B.pack m_remoteNonce)) `B.append` egressCipher

  let ingressMac = SHA3.update (SHA3.init 256) $ 
                    (macEncKey `bXor` (m_nonce)) `B.append` ingressCipher


  print $ B16.encode $ (macEncKey `bXor` (m_nonce)) `B.append` ingressCipher

  print $ B16.encode $ (B.pack m_remoteNonce) `add` m_nonce

  print $ B16.encode macEncKey
  print $ B16.encode $ SHA3.finalize egressMac
  print $ B16.encode $ SHA3.finalize ingressMac
