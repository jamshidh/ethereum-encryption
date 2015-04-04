
module Frame (
  EthCryptState(..),
  encryptAndPutFrame,
  getAndDecryptFrame
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Crypto.Cipher.AES
import qualified Crypto.Hash.SHA3 as SHA3
import Data.Bits
import qualified Data.ByteString as B
import System.IO

import qualified AESCTR as AES

bXor::B.ByteString->B.ByteString->B.ByteString
bXor x y | B.length x == B.length y = B.pack $ B.zipWith xor x y 
bXor x y = error $
           "bXor called with two ByteStrings of different length: length string1 = " ++
           show (B.length x) ++ ", length string2 = " ++ show (B.length y)


data EthCryptState =
  EthCryptState {
    handle::Handle,
    encryptState::AES.AESCTRState,
    decryptState::AES.AESCTRState,
    egressMAC::SHA3.Ctx,
    ingressMAC::SHA3.Ctx,
    egressKey::B.ByteString,
    ingressKey::B.ByteString
    }

type EthCryptM = StateT EthCryptState IO

putBytes::B.ByteString->EthCryptM ()
putBytes bytes = do
  cState <- get
  liftIO $ B.hPut (handle cState) bytes

getBytes::Int->EthCryptM B.ByteString
getBytes size = do
  cState <- get
  liftIO $ B.hGet (handle cState) size
  
encrypt::B.ByteString->EthCryptM B.ByteString
encrypt input = do
  cState <- get
  let aesState = encryptState cState
  let (aesState', output) = AES.encrypt aesState input
  put cState{encryptState=aesState'}
  return output

decrypt::B.ByteString->EthCryptM B.ByteString
decrypt input = do
  cState <- get
  let aesState = decryptState cState
  let (aesState', output) = AES.decrypt aesState input
  put cState{decryptState=aesState'}
  return output

rawUpdateEgressMac::B.ByteString->EthCryptM B.ByteString
rawUpdateEgressMac value = do
  cState <- get
  let mac = egressMAC cState
  let mac' = SHA3.update mac value
  put cState{egressMAC=mac'}
  return $ B.take 16 $ SHA3.finalize mac'

updateEgressMac::B.ByteString->EthCryptM B.ByteString
updateEgressMac value = do
  cState <- get
  let mac = egressMAC cState
  rawUpdateEgressMac $
    value `bXor` (encryptECB (initAES $ egressKey cState) (B.take 16 $ SHA3.finalize mac))

rawUpdateIngressMac::B.ByteString->EthCryptM B.ByteString
rawUpdateIngressMac value = do
  cState <- get
  let mac = ingressMAC cState
  let mac' = SHA3.update mac value
  put cState{ingressMAC=mac'}
  return $ B.take 16 $ SHA3.finalize mac'

updateIngressMac::B.ByteString->EthCryptM B.ByteString
updateIngressMac value = do
  cState <- get
  let mac = ingressMAC cState
  rawUpdateIngressMac $
    value `bXor` (encryptECB (initAES $ ingressKey cState) (B.take 16 $ SHA3.finalize mac))

encryptAndPutFrame::B.ByteString->EthCryptM ()
encryptAndPutFrame bytes = do
  let frameSize = B.length bytes
      header =
        B.pack [fromIntegral $ frameSize `shiftR` 16,
                fromIntegral $ frameSize `shiftR` 8,
                fromIntegral $ frameSize,
                0xc2,
                0x80,
                0x80,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

  headCipher <- encrypt header
  
  headMAC <- updateEgressMac headCipher

  putBytes headCipher
  putBytes headMAC

  frameCipher <- encrypt bytes
  _ <- rawUpdateEgressMac frameCipher
  frameMAC <- updateEgressMac headMAC

  putBytes frameCipher
  putBytes frameMAC

getAndDecryptFrame::EthCryptM B.ByteString
getAndDecryptFrame = do
  headCipher <- getBytes 16
  headMAC <- getBytes 16

  expectedHeadMAC <- updateEgressMac headCipher
  when (expectedHeadMAC /= headMAC) $ error "oops, head mac isn't what I expected"

  header <- decrypt headCipher

  let frameSize = 
        (fromIntegral $ header `B.index` 0 `shiftL` 16) +
        (fromIntegral $ header `B.index` 1 `shiftL` 8) +
        (fromIntegral $ header `B.index` 2)

  frameCipher <- getBytes frameSize
  frameMAC <- getBytes 16

  _ <- rawUpdateIngressMac frameCipher
  expectedFrameMAC <- updateIngressMac headMAC

  when (expectedFrameMAC /= frameMAC) $ error "oops, frame mac isn't what I expected"

  frame <- decrypt frameCipher

  --TODO- verify the HMAC, update ingressCipher

  return frame
