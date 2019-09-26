{-# language
    FlexibleContexts
  #-}

module Main (main) where

import ArrayList (ArrayList(..))
import Control.Monad.Random.Strict hiding (fromList)
import Control.Monad.ST (runST)
import Data.Bifunctor (Bifunctor(..))
import Data.Foldable (foldlM)
import Data.Hashable (Hashable(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Primitive
import Data.Word (Word16,Word32)
import Foreign.Storable (Storable)
import Prelude hiding (dropWhile)
import System.IO.Unsafe (unsafePerformIO)
import Test.SmallCheck.Series (Series,generate)
import Test.Tasty (TestTree,defaultMain,testGroup,localOption)
import Test.Tasty.SmallCheck (Testable,over,SmallCheckDepth(..),testProperty)
import qualified ArrayList as AL
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE

main :: IO ()
main = do
  defaultMain $ testGroup "ArrayList" tests

tests :: [TestTree]
tests =
  [ testPropDepth 10 "arraylist inserts followed by dump (short)"
      (over word16Series insertions)
  , testPropDepth 150 "arraylist inserts followed by dump (long)"
      (over word32Series insertions)
  , testPropDepth 150 "arraylist inserts followed by repeated pop (long)"
      (over word32Series pushPop)
  , testPropDepth 50 "arraylist dropWhile"
      (over word32Series dropWhile)
  , testPropDepth 50 "insert array"
      (over word32Series insert)
  , testPropDepth 50 "insert big array"
      (over word32Series insertBigArray)
  , testPropDepth 50 "insert big arrays"
      (over word32Series insertArrays)
  ]

word16Series :: Series m [Word16]
word16Series = scanSeries 0 $ \n -> [n + 89, n + 71]

word32Series :: Series m [Word32]
word32Series = scanSeries 0 $ \n -> [n + 73]

scanSeries :: a -> (a -> [a]) -> Series m [a]
scanSeries x0 f = generate $ \n -> map NE.toList
  . concat
  . take n
  . iterate
    (\ys -> do {
        xs@(x :| _) <- ys
      ; z <- f x
      ; pure $ z :| NE.toList xs
    })
  $ [x0 :| []]

insertions :: (Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
insertions xs = unsafePerformIO $ AL.with $ \a0 -> do
  a1 <- foldlM AL.pushR a0 xs
  (a2,ys) <- dumpList a1
  pure $ (,) a2 $ if xs == ys
    then Right "good"
    else Left ("expected " ++ show xs ++ " but got " ++ show ys)

pushPop :: (Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
pushPop xs = unsafePerformIO $ AL.with $ \a0 -> do
  a1 <- foldlM AL.pushR a0 xs
  let go al = do
        (al',m) <- AL.popL al
        case m of
          Nothing -> pure (al',[])
          Just a -> fmap (second (a:)) (go al')
  (a2,ys) <- go a1
  pure $ (,) a2 $ if xs == ys
    then Right "good"
    else Left $ "expected " ++ show xs ++ " but got " ++ show ys

dropWhile :: (Hashable a, Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
dropWhile xs = unsafePerformIO $ AL.with $ \a0 ->
  case deterministicShuffle xs of
    [] -> pure (a0, Right "good")
    x : _ -> do
      a1 <- foldlM AL.pushR a0 xs
      (a2,_) <- AL.dropWhileL a1 $ \y -> pure (y /= x)
      (a3,ys) <- dumpList a2
      let expected = L.dropWhile (/= x) xs
      pure $ (,) a3 $ if expected == ys
        then Right "good"
        else Left $ "expected " ++ show expected ++ " but got " ++ show ys ++ " using pivot of " ++ show x

insert :: (Hashable a, Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
insert xs = unsafePerformIO $ AL.with $ \a0 -> do
  a1 <- foldlM AL.pushArrayR a0 (map singletonPrimArray xs)
  let go al = do
        (al',m) <- AL.popL al
        case m of
          Nothing -> pure (al',[])
          Just a -> fmap (second (a:)) (go al')
  (a2,ys) <- go a1
  pure $ (,) a2 $ if xs == ys
    then Right "good"
    else Left $ "expected " ++ show xs ++ " but got " ++ show ys

insertBigArray :: (Hashable a, Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
insertBigArray xs = unsafePerformIO $ AL.with $ \a0 -> do
  a1 <- AL.pushArrayR a0 (fromList xs)
  let go al = do
        (al',m) <- AL.popL al
        case m of
          Nothing -> pure (al',[])
          Just a -> fmap (second (a:)) (go al')
  (a2,ys) <- go a1
  pure $ (,) a2 $ if xs == ys
    then Right "good"
    else Left $ "expected " ++ show xs ++ " but got " ++ show ys

insertArrays :: (Hashable a, Eq a, Show a, Prim a, Storable a)
  => [a]
  -> Either String String
insertArrays xs = unsafePerformIO $ AL.with $ \a0 -> do
  a1 <- AL.pushArrayR a0 (fromList xs)
  a2 <- AL.pushArrayR a1 (fromList xs)
  let go al = do
        (al',m) <- AL.popL al
        case m of
          Nothing -> pure (al',[])
          Just a -> fmap (second (a:)) (go al')
  (a3,zs) <- go a2
  pure $ (,) a3 $ if zs == (xs ++ xs)
    then Right "good"
    else Left $ "expected " ++ show (xs ++ xs) ++ " but got " ++ show zs

dumpList :: (Prim a, Storable a) => ArrayList a -> IO (ArrayList a, [a])
dumpList xs@(ArrayList _ len _ _) = do
  marr <- newPrimArray len
  newXs <- AL.dump xs marr 0
  arr <- unsafeFreezePrimArray marr
  pure (newXs, primArrayToList arr)

testPropDepth :: Testable IO a => Int -> String -> a -> TestTree
testPropDepth n name = localOption (SmallCheckDepth n)
  . testProperty name

deterministicShuffle :: Hashable a => [a] -> [a]
deterministicShuffle xs = evalRand (shuffle xs) (mkStdGen (hash xs))

shuffle :: [a] -> Rand StdGen [a]
shuffle [] = pure []
shuffle xs = do
  randomPosition <- getRandomR (0, length xs - 1)
  let (left, (a:right)) = L.splitAt randomPosition xs
  fmap (a:) (shuffle (left ++ right))

singletonPrimArray :: Prim a => a -> PrimArray a
singletonPrimArray a = runST $ do
  marr <- newPrimArray 1
  writePrimArray marr 0 a
  unsafeFreezePrimArray marr

