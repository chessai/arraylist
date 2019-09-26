-----------------------------------------------------------------------------------

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall #-}

-----------------------------------------------------------------------------------

module ArrayList
  ( ArrayList(..)
  , size
  , with
  , new
  , free
  , pushR
  , pushArrayR
  , popL
  , dropWhileL
  , dropWhileScanL
  , dropScanL
  , dropL
  , dump
  , dumpMap
  , clear
  , showDebug
  ) where

-----------------------------------------------------------------------------------

import Control.Monad (when)
import Data.Functor ((<$>))
import Control.Applicative ((<*>))
import Data.Bits (Bits(unsafeShiftR))
import Data.Primitive.Addr (Addr(Addr), setAddr)
import Data.Primitive.PrimArray (PrimArray, MutablePrimArray)
import Data.Primitive.Types (Prim())
import Foreign.Storable (Storable(sizeOf, alignment, peek, poke))
import GHC.Exts (RealWorld)
import GHC.Ptr (Ptr(Ptr), castPtr, plusPtr, nullPtr)
import Initialize (Initialize(initialize))
import qualified Data.Primitive as Primitive
import qualified Data.Primitive.PrimArray as PrimArray
import qualified Data.Primitive.Ptr as PrimPtr
import qualified Foreign.Marshal.Alloc as FMAlloc
import qualified Foreign.Marshal.Array as FMArray
import qualified Foreign.Storable as FStorable

-----------------------------------------------------------------------------------

data ArrayList a = ArrayList
  {-# UNPACK #-} !Int -- ^ start index (in elements)
  {-# UNPACK #-} !Int -- ^ used length (in elements)
  {-# UNPACK #-} !Int -- ^ buffer length (in elements)
  {-# UNPACK #-} !(Ptr a) -- ^ all the data

-----------------------------------------------------------------------------------

instance Storable (ArrayList a) where
  sizeOf _ = wordSz * 4;
  alignment _ = wordSz;
  peek ptr = ArrayList
    <$> peek (castPtr ptr)
    <*> peek (plusPtr ptr wordSz)
    <*> peek (plusPtr ptr (wordSz + wordSz))
    <*> peek (plusPtr ptr (wordSz + wordSz + wordSz))
  poke ptr (ArrayList a b c d) = do
    poke (castPtr ptr) a
    poke (plusPtr ptr wordSz) b
    poke (plusPtr ptr (wordSz + wordSz)) c
    poke (plusPtr ptr (wordSz + wordSz + wordSz)) d
  {-# INLINE sizeOf #-}
  {-# INLINE alignment #-}
  {-# INLINE peek #-}
  {-# INLINE poke #-}

instance Storable a => Initialize (ArrayList a) where
  initialize (Ptr addr#) = setAddr (Addr addr#) 4 (0 :: Int)
  {-# INLINE initialize #-}

-----------------------------------------------------------------------------------

{-# INLINE minimizeMemory #-}
minimizeMemory :: forall a. Storable a => ArrayList a -> IO (ArrayList a)
minimizeMemory xs@(ArrayList start len bufLen ptr)
    -- We do not drop below a certain size, since then we would
    -- end up doing frequent reallocations. Although, once the size
    -- reaches zero, we deallocate entirely since this can save a lot
    -- of memory when we have many empty ArrayLists.
  | len == 0 = do
      FMAlloc.free ptr
      return (ArrayList 0 0 0 nullPtr)
  | bufLen <= initialSize = return xs
  | len < eighth bufLen = do
      newPtr <- FMAlloc.mallocBytes (FStorable.sizeOf (undefined :: a) * div bufLen 2)
      FMArray.moveArray newPtr (FMArray.advancePtr ptr start) len
      FMAlloc.free ptr
      return (ArrayList 0 len (div bufLen 2) newPtr)
  | otherwise = return (ArrayList start len bufLen ptr)

wordSz :: Int; wordSz = Primitive.sizeOf (undefined :: Int); {-# INLINE wordSz #-}
initialSize :: Int; initialSize = 4; {-# INLINE initialSize #-}

twiceUntilExceeds :: Int -> Int -> Int
twiceUntilExceeds !i !limit = go i where { go !n = if n > limit then n else go (n * 2) }
half, eighth :: Int -> Int;
half      x = unsafeShiftR x 1;
eighth    x = unsafeShiftR x 3;

-----------------------------------------------------------------------------------

size :: ArrayList a -> Int
{-# INLINE size #-}
size (ArrayList _ len _ _) = len

new :: Storable a => IO (ArrayList a)
new = return (ArrayList 0 0 0 nullPtr)

free :: ArrayList a -> IO ()
free (ArrayList _ _ _ ptr) = FMAlloc.free ptr

with :: Storable a => (ArrayList a -> IO (ArrayList a, b)) -> IO b
with f = do
  initial <- new
  (final, a) <- f initial
  free final
  return a

pushR :: forall a. Storable a => ArrayList a -> a -> IO (ArrayList a)
pushR (ArrayList start len bufLen ptr) a = if start + len < bufLen
  then do
    poke (FMArray.advancePtr ptr (start + len)) a
    return (ArrayList start (len + 1) bufLen ptr)
  else if
    | len == 0 -> do
        when (bufLen /= 0) (fail "ArrayList.pushR: invariant violated")
        when (start /= 0) (fail "ArrayList.pushR: invariant violated")
        when (ptr /= nullPtr) (fail "ArrayList.pushR: invariant violated")
        newPtr <- FMAlloc.mallocBytes (FStorable.sizeOf (undefined :: a) * initialSize)
        poke newPtr a
        return (ArrayList 0 1 initialSize newPtr)
    | len < half bufLen -> do
        FMArray.moveArray ptr (FMArray.advancePtr ptr start) len
        poke (FMArray.advancePtr ptr len) a
        return (ArrayList 0 (len + 1) bufLen ptr)
    | otherwise -> do
        newPtr <- FMAlloc.mallocBytes (FStorable.sizeOf (undefined :: a) * bufLen * 2)
        FMArray.moveArray newPtr (FMArray.advancePtr ptr start) len
        FMAlloc.free ptr
        poke (FMArray.advancePtr newPtr len) a
        return (ArrayList 0 (len + 1) (bufLen * 2) newPtr)

pushArrayR :: forall a. (Storable a, Prim a) => ArrayList a -> PrimArray a -> IO (ArrayList a)
pushArrayR (ArrayList start len bufLen ptr) as = if start + len + asLen <= bufLen
  then do
    PrimArray.copyPrimArrayToPtr (FMArray.advancePtr ptr (start + len)) as 0 asLen
    return (ArrayList start (len + asLen) bufLen ptr)
  else if
    | len == 0 -> do
        when (bufLen /= 0) (fail "ArrayList.pushArrayR: invariant violated")
        when (start /= 0) (fail "ArrayList.pushArrayR: invariant violated")
        when (ptr /= nullPtr) (fail "ArrayList.pushArrayR: invariant violated")
        let newBufLen = twiceUntilExceeds initialSize asLen
        newPtr <- FMAlloc.mallocBytes (FStorable.sizeOf (undefined :: a) * newBufLen)
        PrimArray.copyPrimArrayToPtr newPtr as 0 asLen
        return (ArrayList 0 asLen newBufLen newPtr)
    | len < half bufLen && asLen < half bufLen -> do
        FMArray.moveArray ptr (FMArray.advancePtr ptr start) len
        PrimArray.copyPrimArrayToPtr (FMArray.advancePtr ptr len) as 0 asLen
        return (ArrayList 0 (len + asLen) bufLen ptr)
    | otherwise -> do
        let newBufLen = twiceUntilExceeds (2 * bufLen) (len + asLen)
        newPtr <- FMAlloc.mallocBytes (FStorable.sizeOf (undefined :: a) * newBufLen)
        FMArray.moveArray newPtr (FMArray.advancePtr ptr start) len
        FMAlloc.free ptr
        PrimArray.copyPrimArrayToPtr (FMArray.advancePtr newPtr len) as 0 asLen
        return (ArrayList 0 (len + asLen) newBufLen newPtr)
  where
    asLen = PrimArray.sizeofPrimArray as

popL :: forall a. Storable a => ArrayList a -> IO (ArrayList a, Maybe a)
popL xs@(ArrayList start len bufLen ptr)
  | len < 1 = return (xs, Nothing)
  | otherwise = do
      a <- peek (FMArray.advancePtr ptr start)
      newArrList <- minimizeMemory (ArrayList (start + 1) (len - 1) bufLen ptr)
      return (newArrList, Just a)

{-# INLINE dropWhileL #-}
dropWhileL :: forall a. Storable a
  => ArrayList a
  -> (a -> IO Bool) -- ^ predicate
  -> IO (ArrayList a,Int)
dropWhileL (ArrayList start len bufLen ptr) p = do
  let go :: Int -> IO Int
      go !i = if i < len
        then do
          a <- peek (FMArray.advancePtr ptr (start + i))
          b <- p a
          if b
            then go (i + 1)
            else return i
        else return i
  dropped <- go 0
  newArrList <- minimizeMemory $ ArrayList (start + dropped) (len - dropped) bufLen ptr
  return (newArrList,dropped)


{-# INLINE dropWhileScanL #-}
dropWhileScanL :: forall a b. Storable a
  => ArrayList a
  -> b
  -> (b -> a -> IO (Bool,b))
  -> IO (ArrayList a,Int,b)
dropWhileScanL (ArrayList start len bufLen ptr) b0 p = do
  let go :: Int -> b -> IO (Int,b)
      go !i !b = if i < len
        then do
          !a <- peek (FMArray.advancePtr ptr (start + i))
          (!shouldContinue,!b') <- p b a
          if shouldContinue
            then go (i + 1) b'
            else return (i,b')
        else return (i,b)
  (dropped,b') <- go 0 b0
  newArrList <- minimizeMemory $ ArrayList (start + dropped) (len - dropped) bufLen ptr
  return (newArrList,dropped,b')

{-# INLINE dropScanL #-}
dropScanL :: forall a b. Storable a
  => ArrayList a
  -> Int
  -> b
  -> (b -> a -> IO b)
  -> IO (ArrayList a, b)
dropScanL (ArrayList start len bufLen ptr) n b0 p = do
  let !m = min n len
  let go :: Int -> b -> IO b
      go !i !b = if i < m
        then do
          a <- peek (FMArray.advancePtr ptr (start + i))
          b' <- p b a
          go (i + 1) b'
        else return b
  b' <- go 0 b0
  newArrList <- minimizeMemory $ ArrayList (start + m) (len - m) bufLen ptr
  return (newArrList,b')

{-# INLINE dropL #-}
dropL :: forall a. Storable a => ArrayList a -> Int -> IO (ArrayList a)
dropL (ArrayList start len bufLen ptr) n = do
  let m = min n len
  minimizeMemory $ ArrayList (start + m) (len - m) bufLen ptr

-- | Deletes all elements from the linked list, copying them
--   into the buffer specified by the pointer. Returns an
--   empty linked list.
dump :: (Prim a, Storable a)
  => ArrayList a -> MutablePrimArray RealWorld a -> Int -> IO (ArrayList a)
dump xs@(ArrayList start len _ ptr) marr ix = do
  PrimPtr.copyPtrToMutablePrimArray marr ix (FMArray.advancePtr ptr start) len
  clear xs

-- | Dump the elements into a 'MutablePrimArray', mapping over them
--   first. This is a fairly niche function.
dumpMap :: (Storable a, Prim b)
  => ArrayList a -> (a -> b) -> MutablePrimArray RealWorld b -> Int -> IO (ArrayList a)
dumpMap xs@(ArrayList start len _ ptr) f marr ix = do
  let go :: Int -> IO ()
      go !i = if i < len
        then do
          a <- FStorable.peekElemOff ptr (start + i)
          PrimArray.writePrimArray marr (ix + i) (f a)
        else return ()
  go 0
  clear xs

clear :: Storable a => ArrayList a -> IO (ArrayList a)
clear xs@(ArrayList _ len _ _) = dropL xs len
{-# INLINE clear #-}

primArrayToListN :: forall a. Prim a => Int -> PrimArray a -> [a]
primArrayToListN len arr = go 0
  where
  go :: Int -> [a]
  go !ix = if ix < len
    then PrimArray.indexPrimArray arr ix : go (ix + 1)
    else []

-- | Does not affect the contents of the ArrayList
showDebug :: forall a. (Prim a, Storable a, Show a) => ArrayList a -> IO String
showDebug (ArrayList start len _ ptr) = do
  marr <- PrimArray.newPrimArray len
  PrimPtr.copyPtrToMutablePrimArray marr 0 (plusPtr ptr (start * Primitive.sizeOf (undefined :: a))) len
  arr <- PrimArray.unsafeFreezePrimArray marr
  return (show (primArrayToListN len arr :: [a]))

{-
-- | This should not be used in production code.
dumpList :: (Prim a, Storable a) => ArrayList a -> IO (ArrayList a, [a])
dumpList xs@(ArrayList _ len _ _) = do
  marr <- newPrimArray len
  newXs <- dump xs marr 0
  arr <- unsafeFreezePrimArray marr
  return (newXs,primArrayToListN len arr)
-}

-----------------------------------------------------------------------------------
