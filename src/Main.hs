{-# LANGUAGE OverloadedStrings #-}

module Main (
  main
  ) where

import Control.Monad.IO.Class
import Crypto.Cipher.AES
import Crypto.Hash.SHA256
import qualified Crypto.Hash.SHA3 as SHA3
import Crypto.PubKey.ECC.DH
import Crypto.Types.PubKey.ECC
import Crypto.Random
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Lazy as BL
import Data.HMAC
import Data.Maybe
import Data.Word
import Network
import qualified Network.Haskoin.Internals as H
import Numeric

import Blockchain.ExtendedECDSA
import Blockchain.ExtWord
import Blockchain.Format

import UDP

--import Debug.Trace

intToBytes::Integer->[Word8]
intToBytes x = map (fromIntegral . (x `shiftR`)) [256-8, 256-16..0]

pointToBytes::Point->[Word8]
pointToBytes (Point x y) = intToBytes x ++ intToBytes y

ctr=[0,0,0,1]

--z = replicate 32 0

s1 = []

encrypt::B.ByteString->B.ByteString->B.ByteString->B.ByteString
encrypt key cipherIV input = encryptCTR (initAES key) cipherIV input 

hPointToBytes::H.Point->[Word8]
hPointToBytes point =
  word256ToBytes (fromIntegral x) ++ word256ToBytes (fromIntegral y)
  where
    x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
    y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point

pubKeyToBytes::H.PubKey->[Word8]
pubKeyToBytes (H.PubKey point) = hPointToBytes point
pubKeyToByteString (H.PubKeyU _) = error "Missing case in showPubKey: PubKeyU"

sigToBytes::ExtendedSignature->[Word8]
sigToBytes (ExtendedSignature signature yIsOdd) =
  word256ToBytes (fromIntegral $ H.sigR signature) ++
  word256ToBytes (fromIntegral $ H.sigS signature) ++
  [if yIsOdd then 1 else 0]

main::IO ()    
main = do

  serverPubKey <- getServerPubKey "127.0.0.1" 30303
  
  handle <- connectTo "127.0.0.1" $ PortNumber 30303

  putStrLn "Connected"
  entropyPool <- createEntropyPool
  let g = cprgCreate entropyPool :: SystemRNG
  let theCurve = getCurveByName SEC_p256k1
      (myPriv, g') = generatePrivate g theCurve
      myPublic = calculatePublic theCurve myPriv
      H.PubKey point = serverPubKey
      x = fromMaybe (error "getX failed in prvKey2Address") $ H.getX point
      y = fromMaybe (error "getY failed in prvKey2Address") $ H.getY point
      otherPublic = Point (fromIntegral x) (fromIntegral y) -- Point 0xc5190919a93e477bb980498971c222c76ac8774ca735b107b3a380decf598a8e 0x569d4c7e29773934ae370e5128fc06087883053de83ec20b1ee2640571a03176
      SharedKey sharedKey = getShared theCurve myPriv otherPublic
  
  putStrLn $ "priv: " ++ showHex myPriv ""
  putStrLn $ "shared: " ++ showHex sharedKey ""
  let (Point x y) = myPublic
  putStrLn $ "public: Point " ++ showHex x "" ++ " " ++ showHex y ""

  let key = hash $ B.pack (ctr ++ intToBytes sharedKey ++ s1)
      eKey = B.take 16 key
      mKeyMaterial = B.take 16 $ B.drop 16 key
      mKey = hash mKeyMaterial
      cipherIV = replicate 16 0
      --msgMac = replicate 32 2

      nonce = 20::Word256
      msg = fromIntegral sharedKey `xor` nonce
  

  putStrLn $ "msg: " ++ showHex msg ""
  sig <- H.withSource H.devURandom $ extSignMsg msg (H.PrvKey $ fromIntegral myPriv)

  let ephemeral = getPubKeyFromSignature sig (fromInteger sharedKey `xor` nonce)
  
      hepubk = SHA3.hash 256 $ B.pack $ pubKeyToBytes ephemeral
      pubk = pointToBytes myPublic
      theData = sigToBytes sig ++ B.unpack hepubk ++ pubk ++ word256ToBytes nonce ++ [0] -- [1..306-64-16-32]

      cipher = B.unpack $ encrypt eKey (B.pack cipherIV) $ B.pack theData
      cipherWithIV = cipherIV ++ cipher
      mac =
        hmac (HashMethod (B.unpack . hash . B.pack) 512) (B.unpack mKey) cipherWithIV

  putStrLn $ "sigToBytes sig: " ++ show (length $ sigToBytes sig) ++ " " ++ show (sigToBytes sig)
  putStrLn $ "B.unpack hepubk: " ++ show (length $ B.unpack hepubk) ++ ", " ++ show (B.unpack hepubk)
  putStrLn $ "pubk: " ++ show (length pubk) ++ ", " ++ show pubk
  putStrLn $ "word256ToBytes nonce: " ++ show (length $ word256ToBytes nonce) ++ ", " ++ show (word256ToBytes nonce)


  
  BL.hPut handle $ BL.pack $ [2] ++ pointToBytes myPublic ++ cipherIV ++ cipher ++ mac

  qqqq <- BL.hGet handle 386

  print qqqq

  BL.hPut handle $ BL.pack $ replicate 100 0

  qqqq <- BL.hGet handle 386

  print qqqq

