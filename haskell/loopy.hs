main :: IO()
main = do
     line <- getLine
     putStrLn line
     let h:t = line in
          if h == 'q' then return ()
	  else main
