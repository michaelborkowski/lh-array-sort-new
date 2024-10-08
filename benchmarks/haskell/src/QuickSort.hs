import Prelude as P 

-- This implementation is not inplace
qsort :: [Int] -> [Int]
qsort lst = case lst of 
                [] -> [] 
                x:xs -> let 
                          lesserArr = filter (< x) xs 
                          greaterArr = filter (>= x) xs
                          sortedLesser = qsort lesserArr 
                          sortedGreater = qsort greaterArr 
                         in sortedLesser ++ [x] ++ sortedGreater


main = do 
        print (qsort [5, 2, 3, 5, 6, 7, 8, 2, 0, 1, 4, 22, 35, 67, 85, 33, 29, 0])
                          
       