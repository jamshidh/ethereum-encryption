
module Frame (
  FrameHeader(..),
  bytesToFrameHeader,
  frameHeaderToBytes,
  EthCryptState(..),
  getAndDecryptFrame
  ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BC
import System.IO

import qualified AESCTR as AES

data FrameHeader =
  FrameHeader {
    frameSize::Int,
    headerHmac::B.ByteString
    } deriving (Show)

bytesToFrameHeader::AES.AESCTRState->B.ByteString->(AES.AESCTRState, FrameHeader)
bytesToFrameHeader state bytes | B.length bytes == 32 =
  if B.unpack (B.drop 3 first) == [0xc2, 0x80, 0x80, 0,0,0,0,0,0,0,0,0,0]
  then
    (state',
     FrameHeader {
        frameSize = 
           (fromIntegral $ first `B.index` 0 `shiftL` 16) +
           (fromIntegral $ first `B.index` 1 `shiftL` 8) +
           (fromIntegral $ first `B.index` 2),
        headerHmac = hmac'
        })
  else error $ "frame header in wrong format: " ++ BC.unpack (B16.encode bytes)
  where
    (encryptedFirst, hmac') = B.splitAt 16 bytes
    (state', first) = AES.decrypt state encryptedFirst
    
bytesToFrameHeader _ x = error $ "Missing case for bytesToFrameHeader: " ++ BC.unpack (B16.encode x)

frameHeaderToBytes::FrameHeader->B.ByteString
frameHeaderToBytes fh =
  B.pack [fromIntegral $ frameSize fh `shiftR` 16,
          fromIntegral $ frameSize fh `shiftR` 8,
          fromIntegral $ frameSize fh,
          0xc2,
          0x80,
          0x80,
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  `B.append` headerHmac fh
  

data EthCryptState =
  EthCryptState {
    handle::Handle,
    encryptState::AES.AESCTRState,
    decryptState::AES.AESCTRState
    }

type EthCryptM = StateT EthCryptState IO

encrypt::B.ByteString->EthCryptM B.ByteString
encrypt input = do
  state <- get
  let aesState = encryptState state
  let (aesState', output) = AES.encrypt aesState input
  put state{encryptState=aesState'}
  return output

decrypt::B.ByteString->EthCryptM B.ByteString
decrypt input = do
  state <- get
  let aesState = decryptState state
  let (aesState', output) = AES.decrypt aesState input
  put state{decryptState=aesState'}
  return output

getBytes::Int->EthCryptM B.ByteString
getBytes size = do
  state <- get
  liftIO $ B.hGet (handle state) size
  
getAndDecryptFrame::EthCryptM B.ByteString
getAndDecryptFrame = do
  headCipher <- getBytes 16
  headHMAC <- getBytes 16

  head <- decrypt headCipher

  let frameSize = 
        (fromIntegral $ head `B.index` 0 `shiftL` 16) +
        (fromIntegral $ head `B.index` 1 `shiftL` 8) +
        (fromIntegral $ head `B.index` 2)

  liftIO $ putStrLn $ "frameSize = " ++ show frameSize
  
  frameCipher <- getBytes frameSize
  frameHMAC <- getBytes 16

  frame <- decrypt frameCipher

  --TODO- verify the HMAC, update ingressCipher

  return frame
