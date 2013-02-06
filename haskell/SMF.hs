-- http://www.cs.elte.hu/~blala/darcs/hmidi/examples/SMF.hs
-- |Decoding the Standard MIDI File (SMF) Format.
-- Implemented as a quick-and-dirty (and ugly) Parsec parser on strings, because 
-- I'm lazy and efficiency is (hopefully) not that important in this case.

module SMF
  ( module System.MIDI.Base
  , MidiEvent'(..)
  , MetaEvent(..)
  , Track
  , TimeBase(..)
  , parseSMF
  , loadSMF
  , timestampUnitInMilisecs
  ) where

import Data.Bits
import Data.Char
import Data.Int
import Data.Word

import Control.Monad
import Text.ParserCombinators.Parsec hiding (Parser)
import System.IO

import System.MIDI.Base

----- Types

-- |SMF meta events
data MetaEvent 
  = SequenceNo  Int
  | Text        String
  | Copyright   String
  | TrackName   String
  | Instrument  String
  | Lyric       String
  | Marker      String
  | CuePoint    String
  | ProgramName String
  | DeviceName  String
  | EndOfTrack
  | Tempo       Int                -- ^ measured in microseconds per quarter note
  | SMPTE       Int Int Int Float  -- ^ hours, minutes, seconds, frames
  | TimeSig     Int Int Int Int    -- ^ numerator, denominator, ...
  | KeySig      Int Bool           -- ^ negative: flats, positive: sharps. True if major, False if minor
  | PropEvent   String
  | MIDIChannel Int                -- ^ obsolate
  | MIDIPort    Int                -- ^ obsolate
  deriving (Show,Eq)
  
-- |A timetamped SMF event. The meaning of the timestamp depends on the file, see `Tempo` and `TimeSig` (?)
data MidiEvent' = MidiEvent' Int (Either MetaEvent MidiMessage) deriving Show
type Track = [MidiEvent']
  
type Parser a = GenParser Char Word8 a  -- state = running status   
  
mthd = do { string "MThd" ; return () }
mtrk = do { string "MTrk" ; return () }

data TimeBase = PPQN Int | SMPTE' Int Int deriving Show

timebase :: TimeBase -> Int 
timebase (PPQN n) = n
timebase (SMPTE' fr sf) = fr * sf

-- |First argument is the division (from the SMF header), second is the tempo (from the `Tempo` meta event).
-- Returns the milisecs per SMF timestamp unit.
timestampUnitInMilisecs :: TimeBase -> Int -> Float
timestampUnitInMilisecs division tempo = case division of
  PPQN ppqn    -> fromIntegral tempo * 0.001 / fromIntegral ppqn
  SMPTE' fr sf -> fromIntegral tempo * 0.001 / fromIntegral (fr*sf) 
    
loadSMF :: FilePath -> IO ((Int,TimeBase),[Track])   
loadSMF fpath = do
  h <- openBinaryFile fpath ReadMode
  mid <- hGetContents h               
  
  y <- case runParser smf 0 fpath mid of
    Left err -> fail $ show err
    Right xx -> return xx

  hClose h  -- hGetContents is lazy, so we should close the file before doing the parsing...
  return y
   
-- |Timestamps in the resulting list of `MidiEvent'`-s are in the SMF units, so most 
-- probably you have to convert them, using `timestampUnitInMilisecs`.  
parseSMF :: [Char] -> Either ParseError ((Int,TimeBase),[Track])   
parseSMF txt = runParser smf 0 "" txt

----- Parsec parser

smf = do
  (typ,trk,div) <- header
  when (typ/=1) $ unexpected "only SMF files of type 1 are supported at the moment"
  tracks <- replicateM (fromIntegral trk) track
  return ((fromIntegral typ,div),tracks)
    
header = do
  mthd
  len <- int32
  when (len/=6) $ fail "invalid header"
  typ <- int16
  trk <- int16
  res <- lookAhead int16
  div <- if res>0 
    then liftM (PPQN . fromIntegral) int16
    else do
      f <- int8
      s <- int8
      return $ SMPTE' (-f) s   
  return (typ,trk,div)
  
track = do
  mtrk
  len <- liftM fromIntegral int32
  dat <- replicateM len anyChar
  withInput dat eventlist
  
withInput :: String -> Parser a -> Parser a
withInput s parser = do
  inp <- getInput
  setInput s
  x <- parser
  setInput inp
  return x
  
eventlist = eventlist' 0

eventlist' :: Int -> Parser [MidiEvent']
eventlist' time = do
  m <- liftM Just (event time) <|> do { eof ; return Nothing }  
  case m of
    Nothing -> return []
    Just (time',ev) -> do
      evs <- eventlist' time'
      return (ev:evs)
  
event :: Int -> Parser (Int,MidiEvent')
event time = do
  delta <- variable
  msg <- message
  let time' = time + delta
  return (time' , MidiEvent' time' msg)
  
message :: Parser (Either MetaEvent MidiMessage)
message = do
  next <- lookAhead byte
  cmd <- if next<128 then getState else byte   -- running status hack
  let hi = fromIntegral $ shiftR cmd 4 :: Int
      lo = fromIntegral $ cmd .&. 15   :: Int
  if cmd == 255 
    then do 
      meta <- byte 
      me <- metaevent meta 
      return $ Left me 
    else do
      setState cmd 
      msg <- message' hi lo
      return $ Right msg
  
message' 8  chn = do { k <- int8 ; v <- int8 ; return $ MidiMessage (chn+1) $ NoteOff k          }  
message' 9  chn = do { k <- int8 ; v <- int8 ; return $ MidiMessage (chn+1) $ NoteOn  k v        }  
message' 10 chn = do { k <- int8 ; v <- int8 ; return $ MidiMessage (chn+1) $ PolyAftertouch k v }  
message' 11 chn = do { k <- int8 ; v <- int8 ; return $ MidiMessage (chn+1) $ CC k v             }  
message' 12 chn = do { p <- int8 ;             return $ MidiMessage (chn+1) $ ProgramChange p    }   
message' 13 chn = do { v <- int8 ;             return $ MidiMessage (chn+1) $ Aftertouch v       }  
message' 14 chn = do { l <- int8 ; h <- int8 ; return $ MidiMessage (chn+1) $ PitchWheel (l + shiftL h 7 - 8192) }    
message' 15 lo  = system lo
message' _  _   = unexpected "expected something at least 0x80"    

system 0  = do { m <- sysex ; return $ SysEx m }
system 1  = return Undefined
system 2  = do { l <- int8  
               ; h <- int8  ; return $ SongPosition (l + shiftL h 7) }
system 3  = do { s <- int8  ; return $ SongSelect s  }
system 4  = return Undefined
system 5  = return Undefined
system 6  = return TuneRequest
system 7  = return Undefined   -- end of SysEx
system 8  = return SRTClock
system 9  = return Undefined 
system 10 = return SRTStart
system 11 = return SRTContinue
system 12 = return SRTStop
system 13 = return Undefined
system 14 = return ActiveSensing

constbyte n = do
  b <- byte
  when (b /= n) $ unexpected $ "expected " ++ show b 

metaevent 0 = do
  l <- byte 
  case l of
    0 -> return $ SequenceNo (-1)
    2 -> do
      l <- int8
      h <- int8
      return $ SequenceNo (l + shiftL h 8)
    _ -> unexpected "0 or 2 expected"

metaevent 1    = do { s <- vstring ; return $ Text         s }
metaevent 2    = do { s <- vstring ; return $ Copyright    s }
metaevent 3    = do { s <- vstring ; return $ TrackName    s }
metaevent 4    = do { s <- vstring ; return $ Instrument   s }
metaevent 5    = do { s <- vstring ; return $ Lyric        s }
metaevent 6    = do { s <- vstring ; return $ Marker       s }
metaevent 7    = do { s <- vstring ; return $ CuePoint     s }
metaevent 8    = do { s <- vstring ; return $ ProgramName  s }
metaevent 9    = do { s <- vstring ; return $ DeviceName   s }
metaevent 0x7f = do { s <- vstring ; return $ PropEvent    s }

metaevent 0x20 = do { constbyte 1 ; l <- int8 ; return $ MIDIChannel l }
metaevent 0x21 = do { constbyte 1 ; l <- int8 ; return $ MIDIPort    l }
metaevent 0x2f = do { constbyte 0 ; return EndOfTrack }
metaevent 0x51 = do 
  constbyte 3
  a <- int8
  b <- int8
  c <- int8
  return $ Tempo $ shiftL a 16 + shiftL b 8 + c
metaevent 0x54 = do 
  constbyte 5
  hr <- int8
  mn <- int8
  ss <- int8
  fr <- int8
  ff <- int8
  return $ SMPTE hr mn ss (fromIntegral fr + 0.01 * fromIntegral ff)
metaevent 0x58 = do 
  constbyte 4
  n <- int8
  d <- int8
  c <- int8
  b <- int8
  return $ TimeSig n d c b
metaevent 0x59 = do 
  constbyte 2
  sf <- int8
  mi <- int8
  x <- case mi of 
    0  -> return True   -- major
    1  -> return False  -- minor 
    _  -> unexpected "0 or 1 expected"
  return $ KeySig sf x

metaevent k = unexpected $ "unexpected Meta Event " ++ show k

vstring :: Parser String
vstring = do
  l <- variable
  s <- replicateM l anyChar
  return s  
  
sysex :: Parser [Word8]
sysex = do
  d <- byte
  if d /= 0xf7 
    then do { ds <- sysex ; return (d:ds) }
    else return [] 
    
byte :: Parser Word8
byte = liftM (fromIntegral.ord) anyChar

-- actually, this always give a positive Int!
int8 :: Parser Int
int8 = liftM ord anyChar
  
variable :: Parser Int
variable = variable' 0     

variable' k = do
  d <- int8
  let m = (shiftL k 7) + (d .&. 127)
  if d .&. 128 == 0 then return m else variable' m

int16 = liftM fromIntegral (bigendian 2) :: Parser Int16
int32 = liftM fromIntegral (bigendian 4) :: Parser Int32

bigendian :: Int -> Parser Int
bigendian l = bigendian' 0 l

bigendian' :: Int -> Int -> Parser Int
bigendian' m 0 = return m
bigendian' m l = do
  d <- int8
  bigendian' (d + shiftL m 8) (l-1)
  
    
