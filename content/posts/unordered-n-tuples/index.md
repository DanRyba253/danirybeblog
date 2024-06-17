+++
title = 'Unordered Homogeneous N-tuples for Guaranteed Commutativity'
date = 2024-06-17T20:21:27+07:00
tags = ["type-level-programming"]
categories = ["haskell"]
summary = "Defining a type of unordered containers and using it to write commutative functions"
+++

## Introduction

A few days ago, I stumbled upon
[this blogpost](https://gelisam.blogspot.com/2013/07/the-commutative-monad.html)
in which the author proposes a way to restrict the type of binary functions to
only allow for ones that are commutative. The key idea is to introduce unordered collections,
and no, I'm not talking about Sets or Maps or whatever. Those data structures are actually
quite ordered, in the sense that they contain the ordering information of their elements:

```haskell
Data.Set.elems :: Set a -> [a]

Data.Map.elems :: Map k a -> [a]
```

The way I want you to think about it is this: **if I can get a list from a Set/Map,
which contains the ordering information of its elements, then that information
must've already been contained in the original Set/Map!**

But a truly unordered collection would not have any kind of ordering of its elements whatsoever,
while still somehow allowing us to work with them. And any function that takes
its arguments in a collection like that would be commutative by default
because it wouldn't be able to observe their order. There would be no order to observe.

## A Truly Unordered Collection

The aforementioned [blogpost](https://gelisam.blogspot.com/2013/07/the-commutative-monad.html)
suggests implementing an unordered pair something like this:

```haskell
newtype UnorderedPair a = UP
    { diffBy :: (a -> Bool) -> Either Bool (a, a) }
```

The idea, is that to access the elements of an unordered pair, we need to first differentiate between them.
We supply a function `f :: a -> Bool`. If it returns different values for the elements of the pair,
then we have successfully differentiated between them, and we get them back (`Right (a1, a2)`) where
`f a1 == True` and `f a2 == False`. Notice that the ordering of `a1` and `a2` is completely
determined by `f` and not by any information already present in the `UnorderedPair`.

But if `f` returns the same value for both elements of the pair, then we have not
successfully differentiated between them, and we get back `Left False` or `Left True` depending on
the result of `f`.

Basically, `diffBy` classifies elements of `UnorderedPair` using a predicate.

Another way to think about this is that we can only observe ordered data, so in order
to observe `a1` and `a2` we need to order them, and that's exactly what `f`
attempts to do.

Another interesting analogy is that `UnorderedPair a` is like two a's superimposed perfectly on top of each other.
If you don't know what type they are, then they look the same to you, and there is no way to separate them.
That is, unless you can find some sort of difference between them, which is what `f` does.

Anyway, now we can write stuff like this:

```haskell
and :: UnorderedPair Bool -> Bool
and ub = case diffBy ub id of
    Left True      -> True  -- both booleans are True
    Right (b1, b2) -> False -- b1 is True, b2 is False
    Left False     -> False -- both booleans are False

or :: UnorderedPair Bool -> Bool
or ub = case diffBy ub id of
    Left True      -> True  -- both booleans are True
    Right (b1, b2) -> True  -- b1 is True, b2 is False
    Left False     -> False -- both booleans are False
```

Now, as long as we construct unordered pairs correctly, functions `and` and `or`
are guaranteed to be commutative, just from their type. Cool!

{{< figure src="cool.gif" title="thumbs-up meme" >}}

But, I hear you ask. What if we need a function that takes in 3 arguments, or 4 arguments,
or even... n arguments?
In other words, the next step is to somehow generalize `UnorderedPair` into a collection that
can hold any number of elements.

## Unordered N-tuples

For brevity, I call this collection `U` for "Unordered". Here's how I define it:

```haskell
-- type level Nats
data Nat = Z | S Nat

-- singleton types for Nats
data Natural (n :: Nat) where
    NZ :: Natural Z
    NS :: Natural n -> Natural (S n)

-- type family for adding Nats
type family (n :: Nat) :+: (m :: Nat) :: Nat where
    Z :+: m = m
    S n :+: m = S (n :+: m)

-- result of splitting U based on a predicate
data USplit (l :: Nat) a where
    US :: U n a -> U m a -> USplit (n :+: m) a

-- the unordered collection
data U (n :: Nat) a where
    U0 :: U Z a
    U1 :: a -> U (S Z) a
    UM :: Natural (S (S n))
       -> ((a -> Bool) -> USplit (S (S n)) a)
       -> U (S (S n)) a

```

The definition of U may seem overly complicated, but it's based on a few basic principles:

1. `U Z a` should be isomorphic to `()`.  
That's why `U0` exists.

2. `U (S Z) a` should be isomorphic to `a`.  
That's why `U1` exists.

3. It should be possible to view the size of any `U`.  
That's why `UM` includes a `Natural (S (S n))`
as its first argument.

4. Generalizing `UnorderedPair`, we get the ability to split `U (n :+: m) a` into `U n a`
and `U m a`, based on a predicate. So we use `USplit` to hold the results of this splitting.
Notice, how this doesn't create any new ordering, except for that which is created by
the predicate.

Here are a few self-explanatory definitions that make working with `U` easier:

```haskell
natToInt :: Natural n -> Int
natToInt NZ     = 0
natToInt (NS n) = 1 + natToInt n

natAdd :: Natural n -> Natural m -> Natural (n :+: m)
natAdd NZ m = m
natAdd (NS n) m = NS (natAdd n m)

unatlen :: U n a -> Natural n
unatlen U0 = NZ
unatlen (U1 _) = NS NZ
unatlen (UM n _) = n

ulen :: U n a -> Int
ulen = natToInt . unatlen

unull :: U n a -> Bool
unull U0 = True
unull _  = False

upush :: a -> U n a -> U (S n) a
upush a U0       = U1 a
upush a u@(U1 b) = UM (NS (NS NZ)) \g -> case (g a, g b) of
    (True, True) -> US (upush a u) U0
    (True, False) -> US (U1 a) (U1 b)
    (False, True) -> US (U1 b) (U1 a)
    (False, False) -> US U0 (upush a u)
upush a (UM n f) = UM (NS n) \g -> case (f g, g a) of
    (US ts fs, True) -> US (upush a ts) fs
    (US ts fs, False) -> unsafeCoerce $ US ts (upush a fs)

-- Btw, I use unsafeCoerce in the definition of upush
-- but it's justified in this case.
-- GHC is just too stupid to type check my code.  
-- Or, more probably, I'm too stupid to write code that GHC can type check. 
```

And here are a few not-so-self-explanatory ones:

```haskell
-- very useful, super general function
ufold :: b                 -- if U is empty
      -> (a -> b)          -- if U has one element
      -> (a -> Bool)       -- predicate to split with
      -> (USplit n a -> b) -- split handler
      -> U n a -> b
ufold if0 if1 pred splitHandler u = case u of
    U0                -> if0
    U1 a              -> if1 a
    UM _ splitter -> splitHandler (splitter pred)

-- Vec type
data Vec (n :: Nat) a where
    VNil :: Vec Z a
    (:>) :: a -> Vec n a -> Vec (S n) a
infixr 5 :>

-- "forgetful" function

-- forgets the ordering of elements in Vec
unorder :: Vec n a -> U n a
unorder VNil = U0
unorder (a :> as) = upush a (unorder as)

-- forgets the length of Vec
unlength :: (forall n . Vec n a -> b) -> [a] -> b
unlength f [] = f VNil
unlength f (a : as) = unlength (f . (a :>)) as

-- unfucks your polymorphic (guaranteed to be commutative) function.
unfuck :: (forall n . U n a -> b) -> [a] -> b
unfuck f = unlength (f . unorder)
```

So now we have an unordered collection `U` that can hold any number of elements
and a full arsenal of functions to work with it.
I'm not sure if it's a good idea to go out of my comfort zone like that,
but I think I want to try writing some actually executable code!

## Examples

```haskell
-- boolean operations

andU :: U n Bool -> Bool
andU = ufold True id id \(US ts fs) -> unull fs

and2 :: U (S (S Z)) Bool -> Bool
and2 = andU

-- >>> and2 $ unorder (True :> False :> VNil)
-- False

and :: [Bool] -> Bool
and = unfuck andU

orU :: U n Bool -> Bool
orU = ufold False id id \(US ts fs) -> not (unull ts)

or2 :: U (S (S Z)) Bool -> Bool
or2 = orU

-- >>> or2 $ unorder (True :> False :> VNil)
-- True

or :: [Bool] -> Bool
or = unfuck orU

-- adding function
add :: [Int] -> Int
add = unfuck addU
  where
    addU :: U n Int -> Int
    addU = ufold 0 id (< 0) \(US neg nonNeg) ->
        addNonNeg nonNeg - addPos (negate <$> neg)
    
    addNonNeg :: U n Int -> Int
    addNonNeg = ufold 0 id (== 0) \(US _ p) -> addPos p

    addPos :: U n Int -> Int
    addPos = ufold 0 id even \(US e o) ->
        let e' = (`div` 2) <$> e
            o' = (`div` 2) <$> o
        in 2 * addNonNeg e' + ulen o + 2 * addNonNeg o'

-- >>> add [1, 2, 3, 4 , 5]
-- 15
```

This is actually pretty fun. Not practical, but fun. Writing `add` was kinda like solving a puzzle.
You need to figure out what property of inputs you can use to split them on. Here, I was able to use dvisibility by 2, but I'm not sure how to, for example, write a function that multiplies the inputs.

## Future work

Here, I outline some of the things I wanted to do, but couldn't figure out how to:

1. Prove that any commutative function can be rewritten using `U`. Or prove otherwise.
2. Prove that `U` in fact, doesn't have any ordering information.  
This seems intuitive to me, but never the less, a formal proof would be nice.
3. See if `ubind :: U n (U m a) -> U (n :*: m) a` is possible to implement.  
This would make `U` a kind of "parametrized monad-like".
4. Find any practical applications for anything I've ever written :)

## P.S.

Oh, and if you want to play around with this, you can find all the code
[here](https://github.com/DanRyba253/Unordered-N-Tuples).
