  {-# LANGUAGE FlexibleInstances #-}
  {-# LANGUAGE DeriveFunctor #-}
  {-# LANGUAGE GeneralizedNewtypeDeriving #-}
  {-# LANGUAGE RecordWildCards #-}
  {-# LANGUAGE KindSignatures #-}
  {-# LANGUAGE DataKinds #-}
  {-# LANGUAGE TypeFamilies #-}
  {-# LANGUAGE RankNTypes #-}

module Contract where

  import Prelude hiding (and,or,truncate)
  import Data.List (groupBy,sortOn,foldl')
  import Data.Function (on)
  import GHC.TypeLits
  import Data.Proxy

  -----------------------------------------------------------------------------
  -- Semirings

  class Semiring r where
    nil   :: r
    unit  :: r
    plus  :: r -> r -> r
    times :: r -> r -> r

  instance Semiring Double where
    nil   = 0
    unit  = 1
    plus  = (+)
    times = (*)

  class Semiring r => Additive r where
    neg :: r -> r

  instance Additive Double where
    neg = negate

  class Semiring r => Multiplicative r where
    inv :: r -> r

  instance Multiplicative Double where
    inv = recip

  -----------------------------------------------------------------------------
  -- Currency
  data Currency = EUR | GBP

  -----------------------------------------------------------------------------
  -- Contracts
  data Contract obs
    = Zero
    | Both (Contract obs) (Contract obs)
    | Or (Contract obs) (Contract obs)
    | Give (Contract obs)
    | Truncate Time (Contract obs)
    | Thereafter (Contract obs) (Contract obs)
    | One Currency
    | Scale obs (Contract obs)
    | Get (Contract obs)
    | Anytime (Contract obs)

  -----------------------------------------------------------------------------
  -- Contract Smart Constructors
  one :: Currency -> Contract obs
  one = One

  zero :: Contract obs
  zero = Zero

  both :: Contract obs -> Contract obs -> Contract obs

  both = Both

  or :: Contract obs -> Contract obs -> Contract obs
  or = Or
  
  give :: Contract obs -> Contract obs
  give = Give

  thereafter :: Contract obs -> Contract obs -> Contract obs
  thereafter = Thereafter

  truncate :: Time -> Contract obs -> Contract obs
  truncate = Truncate
  
  scale :: obs -> Contract obs -> Contract obs
  scale = Scale

  get :: Contract obs -> Contract obs
  get = Get

  anytime :: Contract obs -> Contract obs
  anytime = Anytime

  expired :: Contract obs
  expired = truncate epoch zero

  instance Semiring (Contract obs) where
    nil   = expired     ;  unit  = zero
    plus  = or          ;  times = both

  instance Multiplicative (Contract obs) where
    inv = give

  -----------------------------------------------------------------------------
  -- Derived Contracts

  zcb :: Time -> r -> Currency -> Contract (Time -> r)
  zcb time amount currency = scaleK amount (get (truncate time (one currency)))

  scaleK :: r -> Contract (Time -> r) -> Contract (Time -> r)
  scaleK x c = scale (const x) c

  european :: Time -> Contract obs -> Contract obs
  european t c = get (truncate t (c `or` zero))

  and :: Contract obs -> Contract obs -> Contract obs
  c1 `and` c2 = (both c1 c2) `thereafter` (c1 `or` c2)

  american :: Time -> Time -> Contract obs -> Contract obs
  american t1 t2 c = beforeT1 `thereafter` afterT1 where
    beforeT1 = get (truncate t1 afterT1)
    afterT1  = anytime (truncate t2 (zero `or` c))


  -----------------------------------------------------------------------------
  -- Tropical Semirings
  data Max a = NegInfty | Max a    
    deriving (Eq,Ord,Show,Functor)

  data Min a = Min a    | PosInfty 
    deriving (Eq,Ord,Show,Functor)
  
  instance (Ord a, Semiring a) => Semiring (Max a) where
    nil  = NegInfty
    unit = Max nil
    plus = max
    Max a `times` Max b = Max (a `plus` b)
    _ `times` _         = NegInfty

  instance (Ord a, Semiring a) => Semiring (Min a) where
    nil  = PosInfty
    unit = Min nil
    plus = min
    Min a `times` Min b = Min (a `plus` b)
    _ `times` _ = PosInfty

  instance (Ord r, Additive r) => Multiplicative (Max r) where 
    inv (Max x) = Max (neg x)

  -----------------------------------------------------------------------------
  -- Time
  data Time = Finite Int | Infinite deriving (Eq,Ord,Show)

  instance Semiring Time where
    nil   = epoch           ;  unit  = Infinite
    plus  = max             ;  times = min

  epoch :: Time
  epoch = Finite 0

  previous :: Time -> Maybe Time
  previous (Finite t) | t > 0 = Just (Finite (t - 1))
  previous _          = Nothing

  next :: Time -> Time
  next (Finite n) = Finite (n + 1)
  next Infinite = Infinite
  
  diff :: Time -> Time -> Maybe Int
  diff (Finite t1) (Finite t2) = Just (t2 - t1)
  diff Infinite Infinite = Nothing

  -----------------------------------------------------------------------------
  -- Expiry
  expiry :: Contract obs -> Time
  expiry Zero               = Infinite
  expiry (Both c1 c2)       = min (expiry c1) (expiry c2)
  expiry (Or c1 c2)         = max (expiry c1) (expiry c2)
  expiry (Give c)           = expiry c
  expiry (Truncate t c)     = min (expiry c) t
  expiry (Thereafter c1 c2) = max (expiry c1) (expiry c2)
  expiry (One c)            = Infinite 
  expiry (Scale o c)        = expiry c
  expiry (Get c)            = expiry c
  expiry (Anytime c)        = expiry c

  -----------------------------------------------------------------------------
  -- Financial Model
  data Financial r obs = 
    Financial { exch  :: Currency -> Time -> r
              , disc  :: Time -> r -> Time -> r
              , snell :: (Time -> r) -> Time -> r
              , eval  :: obs -> Time -> r -> r     }

  static :: Currency -> Double -> Financial (Max Double) (Time -> Double)
  static k rate = Financial exch disc snell eval where
    exch k' = go k k' where
      go EUR GBP t = Max 1.4
      go GBP EUR t = Max (recip 1.4)
      go k1 k2 t   = Max 1
    disc h v t | Just n <- diff t h
               , Max x <- v
               = Max $ x / ((1 + rate)^n)
               | otherwise = NegInfty
    snell f t | v@Max{} <- f t = max v (disc (next t) (snell f (next t)) t)
              | otherwise = NegInfty
    eval f t NegInfty = NegInfty
    eval f t (Max x)  = Max (f t * x)

  -----------------------------------------------------------------------------
  -- Worth
  worth :: Multiplicative r => Financial r obs -> Contract obs -> Time -> r
  worth (Financial exch disc snell eval) = go where
    go c                  time | time >= expiry c = nil
    go Zero               time = unit
    go (Both c1 c2)       time = go c1 time `times` go c2 time
    go (Or c1 c2)         time = go c1 time `plus` go c2 time
    go (Give c)           time = inv (go c time)        
    go (Truncate t c)     time = go c time
    go (Thereafter c1 c2) time | time < expiry c1 = go c1 time
                               | otherwise        = go c2 time
    go (One k)            time = exch k time
    go (Scale o c)        time = eval o time (go c time)
    go (Get c)            time | Just t <- horizon c = disc t (go c t) time
                               | otherwise = nil
    go (Anytime c)        time | Just t <- horizon c = snell (go c) time
                               | otherwise = nil
    horizon = previous . expiry

  -----------------------------------------------------------------------------
  -- Example Contracts
  c0, c1, c2, c3, c4 :: Num a => Contract (Time -> a)
  c0 = zcb t0 100 EUR
  c1 = zcb t1 100 EUR
  c2 = zcb t2 100 EUR
  c3 = zcb t3 100 EUR
  c4 = zcb t4 100 EUR

  c0', c1', c2', c3', c4' :: Num a => Contract (Time -> a)
  c0' = zcb t0 200 EUR
  c1' = zcb t1 200 EUR
  c2' = zcb t2 200 EUR
  c3' = zcb t3 200 EUR
  c4' = zcb t4 200 EUR

  fxo r t currency1 currency2 = european t (fx r currency1 currency2)

  fx r currency1 currency2 = scaleK r (one currency1) `and` give (one currency2)

  t0 = Finite 0
  t1 = Finite 1
  t2 = Finite 2
  t3 = Finite 3
  t4 = Finite 4
  t5 = Finite 5

  -----------------------------------------------------------------------------
  -- Gradients

  data Gradient a = G a a deriving (Eq, Ord, Show)

  instance Semiring a => Semiring (Gradient a) where
    nil = G nil nil
    unit = G unit nil
    plus (G f df) (G g dg) = G (f `plus` g) (df `plus` dg)
    times (G f df) (G g dg) = G (f `times` g) ((df `times` g) `plus` (f `times` dg))
  instance Additive a => Additive (Gradient a) where
    neg (G f df) = G (neg f) (neg df)
  instance (Additive a, Multiplicative a) => Multiplicative (Gradient a) where
    inv (G f df) = G (inv f) (neg (inv (f `times` f)) `times` df)

  staticG
    :: Currency -> Double -> Financial (Max (Gradient Double)) (Time -> Double)
  staticG k rate = Financial exch disc snell eval where
    exch k' = go k k' where
      go EUR GBP t = Max (G 1.4 0.0)
      go GBP EUR t = Max (inv $ G 1.4 0.0)
      go k1 k2 t   = Max (G 1.0 0.0)
    disc h v t | Just n <- diff t h, Max x <- v
               = Max $ x `times` inv (G (r n) (fromIntegral n * r (n-1)))
               | otherwise = NegInfty
               where r n = (1 + rate) ** fromIntegral n
    snell f t = error "snell is not defined for gradients."
    eval f t NegInfty = NegInfty
    eval f t (Max x)  = Max (G (f t) 0 `times` x)

  -----------------------------------------------------------------------------
