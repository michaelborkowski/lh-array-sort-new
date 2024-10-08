import Prelude as P

mergeSort :: [Int] -> [Int]
mergeSort lst = case lst of 
                     [] -> [] 
                     [x] -> [x]
                     _ -> let (left, right) = split lst
                              left' = mergeSort left 
                              right' = mergeSort right 
                            in merge left' right' 

split :: [Int] -> ([Int], [Int])
split lst = case lst of 
                [] -> ([], [])
                x:[] -> ([x], [])
                x:y:[] -> ([x], [y])
                _ -> let len = P.length lst 
                         mid = len `div` 2 
                       in (take mid lst, drop mid lst)

merge :: [Int] -> [Int] -> [Int]
merge l1 l2 = case (l1, l2) of 
                    ([], []) -> []
                    ([], _) -> l2 
                    (_, []) -> l1 
                    (a:rst, b:rst') -> if a < b 
                                       then a:(merge rst (b:rst'))
                                       else b:(merge (a:rst) rst')

main = do 
        print $ mergeSort [8, 9, 7, 3, 2, 0, 1, 3, 5, 2, 4, 2, 6, 8, 5, 3, 2, 5, 7, 8, 9, 77, 23, 99, 100]
