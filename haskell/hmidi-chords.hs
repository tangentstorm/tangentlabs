-- http://www.cs.elte.hu/~blala/darcs/hmidi/examples/chords.hs

--
-- A very simple example application using System.MIDI.
--
-- It accepts NoteOn / NoteOff messages from a MIDI source and 
-- sends corresponding chords to a MIDI destination.
--

module Main where

import Control.Monad
import System.MIDI

-- the essence

chord = [0,4,7]
output_channel = 1

mycallback outconn event@(MidiEvent _ (MidiMessage chn msg)) = do
  case msg of
    NoteOff k   -> forM_ chord $ \j -> send outconn $ MidiMessage output_channel $ NoteOff (k+j)
    NoteOn  k v -> forM_ chord $ \j -> send outconn $ MidiMessage output_channel $ NoteOn  (k+j) v
    _           -> return () 
mycallback _ _ = return ()

-- source / destination selection

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of 
  [(x,"")] -> Just x
  _        -> Nothing
  
select srclist = do
  names <- mapM getName srclist
  forM_ (zip [1..] names) $ \(i,name) -> putStrLn $ show i ++ ": " ++ name
  let nsrc = length srclist
  src <- case srclist of
    []  -> fail "no midi devices found"
    [x] -> return x
    _   -> do
      putStrLn "please select a midi device"
      l <- getLine
      let k = case maybeRead l of
        { Nothing -> nsrc
        ; Just m  -> if m<1 || m>nsrc then nsrc else m
        }
      putStrLn $ "device #" ++ show k ++ " selected."
      return $ srclist!!(k-1)
  return src
      
-- main      
      
main = do

  srclist <- enumerateSources
  putStrLn "midi sources:"
  src <- select srclist

  dstlist <- enumerateDestinations
  putStrLn "\nmidi destinations:"
  dst <- select dstlist

  outconn <- openDestination dst
  inconn  <- openSource src $ Just (mycallback outconn)
  putStrLn "connected"
 
  start inconn ; putStrLn "started. Press 'ENTER' to exit."
  getLine
  stop inconn  ; putStrLn "stopped."
  
  close inconn ; putStrLn "closed."
  close outconn
  
