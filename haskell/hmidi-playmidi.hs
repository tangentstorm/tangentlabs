--
-- A simplified MID file player, as an example application using System.MIDI.
-- You will need a GM (General MIDI) capable synth, or something like that (Windows has one built-in).
--

module Main where

import Data.Ord
import Data.List
import Control.Concurrent
import Control.Monad
import System.IO
import System.Environment
import System.Exit

import System.MIDI
import SMF

-- player thread

player :: Connection -> MVar [MidiEvent] -> IO ()
player conn mv = do
  t <- currentTime conn
  evs <- readMVar mv
  case evs of
    [] -> do
      putStrLn "the song ended."
      return ()
    (MidiEvent s ev):evs' -> do
      when (s<=t) $ do
        swapMVar mv evs'
        case ev of
          SysEx _   -> return ()
          Undefined -> return ()
          _         -> send conn ev
      threadDelay 1000
      player conn mv
      
-- song

data Song = Song
  { song_bpm    :: Float
  , song_tracks :: [[MidiEvent]]
  }
  
filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap f xs = map (fromJust . f) $ filter test xs where
  test x = case f x of 
    Just _  -> True
    Nothing -> False
  fromJust (Just x) = x

tmeta (MidiEvent' ts (Left  x)) = Just (ts,x)
tmeta (MidiEvent' _  (Right _)) = Nothing 

tmidi (MidiEvent' _  (Left  _)) = Nothing 
tmidi (MidiEvent' ts (Right y)) = Just $ MidiEvent (fromIntegral ts) y

toSong :: TimeBase -> [[MidiEvent']] -> Song
toSong division tracks = Song bpm $ map convert midi where
  convert = map (\(MidiEvent ts ev) -> MidiEvent (round $ pertick * fromIntegral ts) ev)
  tTempo (_,Tempo tempo) = Just tempo
  tTempo _ = Nothing
  tempos = filterMap tTempo metaAll
  (tempo,bpm) = case tempos of
    []  -> ( 500000 , 120 )
    t:_ -> ( t      , 60000000 / fromIntegral t )
  pertick = timestampUnitInMilisecs division tempo
  metaAll = concat meta
  meta = map (filterMap tmeta) tracks
  midi = map (filterMap tmidi) tracks

-- source / destination selection

maybeRead :: Read a => String -> Maybe a
maybeRead s = case reads s of 
  [(x,"")] -> Just x
  _        -> Nothing
  
select devlist = do
  names <- mapM getName devlist
  forM_ (zip [1..] names) $ \(i,name) -> putStrLn $ show i ++ ": " ++ name
  let ndev = length devlist
  dev <- case devlist of
    []  -> fail "no midi devices found"
    [x] -> return x
    _   -> do
      putStrLn "please select a midi device"
      l <- getLine
      let k = case maybeRead l of
        { Nothing -> 1
        ; Just m  -> if m<1 || m>ndev then 1 else m
        }
      putStrLn $ "device #" ++ show k ++ " selected."
      return $ devlist!!(k-1)
  return dev

-- main

main = do
  args <- getArgs
  fname <- case args of
    [s] -> return s
    _   -> do
      putStrLn "Usage: playmidi <fname.mid>"
      exitFailure
  
  ((_,division),tracks) <- loadSMF fname
  let song = toSong division tracks
  putStrLn $ "bpm = " ++ show (song_bpm song)
  
  let events = sortBy (comparing $ \(MidiEvent t _) -> t) $ concat (song_tracks song)
  mv <- newMVar events
  
  dstlist <- enumerateDestinations
  dst <- select dstlist
    
  conn <- openDestination dst
  start conn
 
  thread <- forkIO (player conn mv)
  
  putStrLn "Press 'ENTER' to exit." 
  getLine
  
  killThread thread
  
  close conn   
  
