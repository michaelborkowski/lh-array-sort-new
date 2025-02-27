
insert :: Int -> [Int] -> [Int]
insert elem lst = case lst of
                        [] -> [elem]
                        x:xs -> if x > elem
                                then elem:lst
                                else x:(insert elem xs)

insertionSort :: [Int] -> [Int]
insertionSort list = case list of
                            [] -> []
                            x:rst -> let
                                        sortedRst = insertionSort rst
                                        list' = insert x sortedRst
                                      in list'

main = do
    print (insertionSort [3, 2, 1, 2, 10, 33, 22, 34, 2, 0, 1, 2, 2, 3, 4, 98, 89])
