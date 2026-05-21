module Main where

(?) :: a -> b -> a
(?) = undefined

test :: Int
test = 42 ? 41 ? 40

main = putStrLn $ show test
