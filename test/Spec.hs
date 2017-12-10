import Parse
import Control.Monad (forM_)

parseTests = [ ("- 1 + 2", Prim (Op "+") (Neg (Lit (Integer 1))) (Lit (Integer 2))) 
             , ("if 1 then 2 else -3", If (Lit (Integer 1)) (Lit (Integer 2)) (Neg (Lit (Integer 3))) )
             ]

check :: (String, Exp) -> String
check (x,y) = x ++ " ... " ++ 
              case parse x of Right z -> if z == y
                                         then "Correct"
                                         else "Wrong parse. Expected: " ++ show y ++ ", Received: " ++ show z
                              Left e ->  "ParseError: " ++ show e 

main :: IO ()
main = do
      putStrLn ""
      putStrLn ("Testing parser (" ++ show (length parseTests) ++ " tests)")
      forM_ (map check parseTests) putStrLn

