> {-#
> LANGUAGE
>     DataKinds
>   , FlexibleContexts
>   , FlexibleInstances
>   , PolyKinds
>   , RankNTypes
>   , ScopedTypeVariables
>   , TypeApplications
>   , TypeOperators
>   , ViewPatterns
> #-}

> module Elliptic where

> import Control.Monad.Reader
> import Data.Binary
> import Data.Bits
> import Data.Proxy
> import Data.Ratio
> import GHC.TypeLits

Cryptography

A very popular form of cryptography uses a mathematical object called an
Elliptic Curve. It's just the graph of an equation, that is the set of
solutions (x,y) to

y^2 = x^3 + a * x + b

We will represent the equation itself using the a and b parameters.

> data Curve k = Curve
>   { aParameter :: k
>   , bParameter :: k
>   } deriving Show

Notice that there is another parameter k which represents the numeric field for
which x,y ∈ k. A mathematician who studies analysis might choose k = ℝ or ℂ, but in order
for computation to be feasible we'll require k to be a finite numeric field.

> newtype Mod integer p = Mod { unMod :: integer } deriving Show

> numVal :: (KnownNat p , Num n) => proxy p -> n
> numVal = fromInteger . natVal

> instance (Eq z , Integral z , KnownNat p) => Eq (z `Mod` p) where
>   Mod x == Mod y = (x - y) `mod` numVal (Proxy @p) == 0

> instance (Ord z , Integral z , KnownNat p) => Ord (z `Mod` p) where
>   Mod x `compare` Mod y = (x - y `mod` numVal (Proxy @p)) `compare` 0

> instance (Enum z , Integral z , KnownNat p) => Enum (z `Mod` p) where
>   toEnum x = Mod $ toEnum x `mod` numVal (Proxy @p)
>   fromEnum (Mod x) = fromEnum x

> instance (Eq z , Integral z , KnownNat p) => Num (z `Mod` p) where
>   Mod x + Mod y = Mod $ (x + y) `mod` numVal (Proxy @p)
>   Mod x - Mod y = Mod $ (x - y) `mod` numVal (Proxy @p)
>   Mod x * Mod y = Mod $ (x * y) `mod` numVal (Proxy @p)
>   abs (Mod x) = Mod $ x `mod` numVal (Proxy @p)
>   signum (Mod x) = if x == 0 then 0 else 1
>   fromInteger x = Mod $ fromInteger (x `mod` natVal (Proxy @p))

> instance (Ord z , Integral z , KnownNat p) => Real (z `Mod` p) where
>   toRational (Mod x) = toRational (x `mod` numVal (Proxy @p))

> instance (Ord z , Integral z , KnownNat p) => Integral (z `Mod` p) where
>   Mod x `quot` Mod y = Mod $ x `quot` y
>   Mod x `rem` Mod y = Mod $ x `rem` y
>   Mod x `quotRem` Mod y = let (q,r) = x `quotRem` y in (Mod q,Mod r)
>   Mod x `div` Mod y = Mod $ x `div` y
>   Mod x `mod` Mod y = Mod $ x `mod` y
>   Mod x `divMod` Mod y = let (d,m) = x `divMod` y in (Mod d,Mod m)
>   toInteger (Mod x) = toInteger (x `mod` numVal (Proxy @p))

> instance (Integral z , KnownNat p) => Fractional (z `Mod` p) where
>   fromRational r = fromInteger (numerator r) / fromInteger (denominator r)
>   recip (Mod x) =
>     let
>       xEuclid x0 y0 x1 y1 u v
>         | v == 0    = x0
>         | otherwise =
>             let (q , r) = u `divMod` v
>             in xEuclid x1 y1 (x0-q*x1) (y0-q*y1) v r
>       recipMod = xEuclid 1 0 0 1
>     in
>       Mod (x `recipMod` numVal (Proxy @p))


Points in the plane could be represented as pairs of k but we also want to allow the
possibility of a "point at infinity".

> data Point k = Pt k k | InfPt deriving (Eq,Show)

Points on an elliptic curve form an Abelian group with the point at
infinity acting as the identity.

> negPt :: Num k => Point k -> Point k
> negPt InfPt = InfPt
> negPt (Pt x y) = Pt x (negate y)

> (.+)
>   :: ( Eq k , Fractional k
>      , MonadReader (Curve k) m )
>   => Point k -> Point k -> m (Point k)
> infixl 6 .+
> InfPt .+ pt = return pt
> pt .+ InfPt = return pt
> pt0@ (Pt x0 y0) .+ pt1@ (Pt x1 y1) = do
>   if pt0 == negPt pt1 then return InfPt
>   else do
>     a <- reader aParameter
>     let {-pt be the point collinear with pt1 and pt2-}
>       m = if pt0 == pt1
>           then (3*x0^2+a) / (2*y0) -- slope of tangent
>           else (y1-y0) / (x1-x0) -- slope of secant
>       x = m^2-x0-x1
>       y = y0 + m*(x-x0)
>       pt = Pt x y
>     return $ negPt pt

> combine
>   :: (Ord z , Integral z , Eq k , Fractional k , MonadReader (Curve k) m)
>   => [(z,Point k)] -> m (Point k)
> combine [] = return InfPt
> combine c_pts = do
>   let
>     positive =
>       [ if c > 0 then (c,pt) else (negate c , negPt pt)
>       | (c,pt) <- c_pts
>       , c /= 0 && pt /= InfPt
>       ]
>   half <- combine [(c `div` 2 , pt) | (c,pt) <- positive]
>   evenPart <- half .+ half
>   oddPart <- foldM (.+) InfPt [pt | (c,pt) <- positive , odd c]
>   evenPart .+ oddPart

> (.*)
>   :: (Ord z , Integral z , Eq k , Fractional k , MonadReader (Curve k) m)
>   => z -> Point k -> m (Point k)
> c .* pt = combine [(c,pt)]

> data PointedCurve k = PointedCurve
>   { basePt :: Point k
>   , curve :: Curve k
>   }

> withReader' :: MonadReader r' m => (r' -> r) -> Reader r a -> m a
> withReader' f r = reader (runReader (withReader f r))

> unsecret
>   :: (Integral z , Eq k , Fractional k , MonadReader (PointedCurve k) m)
>   => z -> m (Point k)
> unsecret private = do
>   g <- reader basePt
>   withReader' curve (private .* g)

> sign
>   :: ( Integral z , Fractional z
>      , Integral k , Fractional k
>      , MonadReader (PointedCurve k) m )
>   => z -> z -> z -> m (z , z)
> sign d e k = do
>   Pt (fromIntegral -> r) _ <- unsecret k
>   let s = (e + d * r) / k
>   return (r,s)

> verify
>   :: ( Integral z , Fractional z
>      , Integral k , Fractional k
>      , MonadReader (PointedCurve k) m )
>   => Point k -> z -> z -> z -> m Bool
> verify q e r s = do
>   let
>     w = recip s
>     u1 = e * w
>     u2 = r * w
>   g <- reader basePt
>   Pt (fromIntegral -> v) _ <-
>     withReader' curve (combine [(u1,g),(u2,q)])
>   return $ v == r

> {-
> return True = do
>   (r,s) <- sign d e k
>   q <- unsecret d
>   verify q e r s
> -}

> type P256k =
>   0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

> type N256k =
>   0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

> type SecretKey256k = Integer `Mod` N256k
> type PublicKey256k = Point (Integer `Mod` P256k)
> type Message256k = Integer `Mod` N256k
> type Signature256k = (Integer `Mod` N256k,Integer `Mod` N256k)
> curve256k :: PointedCurve (Integer `Mod` P256k)
> curve256k = PointedCurve
>   { basePt = Pt
>       0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
>       0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
>   , curve = Curve
>     { aParameter = 0
>     , bParameter = 7
>     }
>   }
> run256k :: Reader (PointedCurve (Mod Integer P256k)) x -> x
> run256k algo = runReader algo curve256k
> unsecret256k :: SecretKey256k -> PublicKey256k
> unsecret256k x = run256k $ unsecret x
> sign256k :: SecretKey256k -> Message256k -> SecretKey256k -> Signature256k
> sign256k secretKey message entropy = run256k $
>   sign secretKey message entropy
> verify256k :: PublicKey256k -> Message256k -> Signature256k -> Bool
> verify256k publicKey message (sig1,sig2) = run256k $
>   verify publicKey message sig1 sig2
