{-# LANGUAGE CPP #-}

module Insertion where

import Array as A

insert :: Ord a => A.Array a -> a -> Int -> A.Array a
insert xs x 0 = A.set xs 0 x  -- first element is sorted
insert xs x n                 -- sort the nth element into the first n+1 elements
  | x < a     =  insert (A.set xs' (n) a) x (n - 1)
  | otherwise =  A.set xs' n x
    where
      (a, xs') = (A.get2 xs (n-1))

{-
// JL: inplace c style of the above insert method.
void insert(int* xs, int x, int n){
  if(n == 0) {
    xs[0] = x;
    return;
  }
  int a = xs[n-1];
  if(x < a){
    // swapping
    xs[n] = a;
    insert(xs,x,n-1); // tail recursive
  }else{
    xs[n] = x;
  }
}
-}


isort :: Ord a => A.Array a -> Int -> A.Array a
isort xs n
  | ( s == 0 ) = xs'
  | ( s == 1 ) = xs'
  | ( n == 0 ) = xs'
  | otherwise  = let (a, xs'') = (A.get2 xs' (s-n))
                  in isort (insert xs'' a (s-n)) (n-1) -- switch to tail recursive
    where
      (s, xs') = A.size2 xs

{-
// JL: inplace c style of the above isort method.
void isort(int* xs, int n, int s){
  if(s == 0 || s == 1 || n == 0){
    return;
  }
  int a = xs[s-n];
  insert(xs, a, (s-n));
  isort(xs, n-1, s); // tail recursive
}

int main(void){
  // top
  isort(arr, sz, sz);
}
-}

isort_top :: Ord a => A.Array a -> A.Array a
isort_top xs' =
    if s <= 1
    then xs
    else
      let ys = isort xs s in ys
  where
    (s, xs) = A.size2 xs'
