--http://www.cs.elte.hu/~blala/darcs/hmidi/examples/monitor.hs
--
-- A very simple example application using System.MIDI.
-- It's a basic MIDI monitor: prints all the incoming messages.
--

-- compile with -threaded:
-- ghc --make -threaded -O hmidi-monitor.hs


module Main where

import Control.Monad
import Control.Concurrent

import System.MIDI

-- the essence

mythread conn = do
  events <- getEvents conn
  mapM_ print events
  (threadDelay 5000)
  mythread conn

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

  conn <- openSource src Nothing
  putStrLn "connected"

  threadid <- forkIO (mythread conn) 
 
  start conn ; putStrLn "started. Press 'ENTER' to exit."
  getLine
  stop conn    ; putStrLn "stopped."
  
  killThread threadid
  
  close conn   ; putStrLn "closed."
  
