-- some sorting algorithms

qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xs) = (qsort l) ++ [x] ++ (qsort r) where
  l = filter (<= x) xs
  r = filter (>  x) xs

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge xs@(x:xt) ys@(y:yt) = if x <= y
  then x : merge xt ys
  else y : merge xs yt

msort :: Ord a => [a] -> [a]
msort [] = []
msort [a] = [a]
msort xs = merge (msort o) (msort e) where
  o = odds  xs
  e = evens xs
  odds :: [a] -> [a]
  odds [] = []
  odds [x] = [x]
  odds (x:_:t) = x : odds t
  evens :: [a] -> [a]
  evens [] = []
  evens [x] = []
  evens (_:x:t) = x : evens t

-- foldr and foldl(')

myfoldr :: (a -> b -> b) -> b -> [a] -> b
myfoldr _ r [] = r
myfoldr f r (x:t) = f x (myfoldr f r t)

myfoldl :: (b -> a -> b) -> b -> [a] -> b
myfoldl _ r [] = r
myfoldl f r (x:t) = myfoldl f (f r x) t

-- `seq` introduces strictness
myfoldl' :: (b -> a -> b) -> b -> [a] -> b
myfoldl' _ r [] = r
myfoldl' f r (x:t) = let r' = f r x in
  r' `seq` (myfoldl' f r' t)

-- the eight queens puzzle

isSafe :: [Int] -> Int -> Int -> Bool
isSafe [] _ _ = True
isSafe (h:rs) r o =
  h /= r && abs (h - r) /= o &&
  isSafe rs r (o + 1)

queens :: Int -> [[Int]]
queens n = foldl f [[]] [1..n] where
  f bs _ = concatMap g bs
  g rs = [r : rs | r <- [1..n], isSafe rs r 1]

-- the Fibonacci sequence

fibs :: [Integer]
fibs = next 0 1 where
  next a b = a : next b (a + b)
