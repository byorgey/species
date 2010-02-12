From oleg at okmij.org Thu Sep 14 19:07:29 2006
To: haskell@haskell.org
Subject: On computable types. I. Typed lambda and type closures
Message-ID: <20060915020729.17DB7AC04@Adric.metnet.fnmoc.navy.mil>
Date: Thu, 14 Sep 2006 19:07:29 -0700 (PDT)
X-comment: noted that the code works in later versions of GHC.
X-comment: Added LANGUAGE pragmas
Status: OR


This is the first message in a series on arbitrary type/kind-level
computations in the present-day Haskell, and on using of so computed
types to give signatures to terms and to drive the selection of
overloaded functions. We can define the type TD N to be the type of a
tree fib(N)-level deep, and instantiate the read function for the tree
of that type. The type computations are largely expressed in a
functional language not too unlike Haskell itself.

In this message we implement call-by-value lambda-calculus with
booleans, naturals and case-discrimination. The distinct feature of
our implementation, besides its simplicity, is the primary role of
type application rather than that of abstraction. Yet we trivially
represent closures and higher-order functions. We use proper names for
function arguments (rather than deBruijn indices), and yet we avoid
the need for fresh name generation, name comparison, and
alpha-conversion. We have no explicit environment and no need to
propagate and search it, and yet we can partially apply functions.

Our implementation fundamentally relies on the connection between
polymorphism and abstraction, and takes the full advantage of the
type-lambda implicitly present in Haskell. The reason for the
triviality of our code is the typechecker's already doing most of the
work need for an implementation of lambda-calculus.

Our code is indeed quite simple: its general part has only three
lines:

   instance E (F x) (F x)
   instance (E y y', A (F x) y' r) => E ((F x) :< y) r
   instance (E (x :< y) r', E (r' :< z) r) => E ((x :< y) :< z) r

The first line says that abstractions evaluate to themselves, the
second line executes the redex, and the third recurses to find it.
Still, we may (and did) write partial applications, the fixpoint
combinator, Fibonacci function, and S and K combinators. Incidentally,
the realization of the S combinator again takes three lines, two of
which build the closures (partial applications) and the third line
executes the familiar S-rule.

   instance A (F CombS) f (F (CombS,f))
   instance A (F (CombS,f)) g (F (CombS,f,g))
   instance E (f :< x :< (g :< x)) r => A (F (CombS,f,g)) x r

Incidentally, the present code constitutes what seems to be the
shortest proof that the type system of Haskell with the undecidable
instances extension is indeed Turing-complete. That extension is
needed for the fixpoint combinator -- which is present in the system
described in Luca Cardelli's 1988 manuscript:
        http://lucacardelli.name/Papers/PhaseDistinctions.pdf
As he wrote, ``Here we have generalized the language of constant
expressions to include typed lambda abstraction, application and
recursion (because of the latter we do not require compile-time
computations to terminate).'' [p9]


This message is all the code, which runs in GHC 6.4.1 - 6.8.2 (it could well
run in Hugs; alas, Hugs did not like infix type constructors like :<).


> {-# LANGUAGE TypeOperators, PatternSignatures, EmptyDataDecls, Rank2Types #-}
> {-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables  #-}
> {-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}
> module TypeLC where

First we define some constants

> data HTrue  = HTrue
> data HFalse = HFalse

> data Zero = Zero
> data Su a = Su a


Indicator for functions, or applicable things:

> data F x

and the applicator

> class A l a b | l a -> b

The meaning of |A l a b| is that the application to |a| of an
applicable thing denoted by |l| yields |b|.

Surprisingly, this already works. Let us define the boolean Not function

> data FNot

by case analysis:

> instance A (F FNot) HTrue  HFalse
> instance A (F FNot) HFalse HTrue

The next function is the boolean And. It takes two arguments, so we
have to handle currying now.

> data FAnd

Applying And to an argument makes a closure, waiting for the second
argument.

> instance A (F FAnd) x (F (FAnd,x))

When we receive the second argument, we are in the position to produce
the result. Again, we use the case analysis.

> instance A (F (FAnd,HTrue))  a  a
> instance A (F (FAnd,HFalse)) a  HFalse

Commonly, abstraction is held to be `more fundamental', which is
reflected in the popular phrase `Lambda-the-Ultimate'. In our system,
application is fundamental.  An abstraction is a not-yet-applied
application -- which is in itself a first-class value.  The class A
defines the meaning of a function, and an instance of A becomes the
definition of a function (clause).

We have dealt with simple expressions and applicative things. We now
build sequences of applications, and define the corresponding big step
semantics. We introduce the syntax for applications:

> data f :< x
> infixl 1 :<

and the big-step evaluation function:

> class E a b | a -> b

Constants evaluate to themselves

> instance E HTrue HTrue
> instance E HFalse HFalse
> instance E Zero Zero

Abstractions are values and so evaluate to themselves

> instance E (F x) (F x)

Familiar rules for applications

> instance (E y y', A (F x) y' r) => E ((F x) :< y) r
> instance (E (x :< y) r', E (r' :< z) r) => E ((x :< y) :< z) r

Other particular rules

> instance E x x' => E (Su x) (Su x')


That is all. The rest of the message are the tests. The first one is
the type-level equivalent of the following function:

      testb x = and (not x) (not (not x))

At the type level, it looks not much differently:

> type Testb x =
>     E (F FAnd :< (F FNot :< x) :< (F FNot :< (F FNot :< x))) r => r
> testb1_t = undefined :: Testb HTrue
> testb1_f = undefined :: Testb HFalse


We introduce the applicative fixpoint combinator

> data Rec l
> instance E (l :< (F (Rec l)) :< x) r => A (F (Rec l)) x r


and define the sum of two numerals

> fix f = f (fix f)
> vsum = fix (\self n m -> case n of 0 -> m
>                                    (n+1) -> 1 + (self n m))

At the type level, this looks as follows

> data FSum'            -- first define the non-recursive function

> instance A (F FSum') self (F (FSum',self))
> instance A (F (FSum',self)) n (F (FSum',self,n)) -- build closures
> instance A (F (FSum',self,Zero)) m m
> instance E (self :< n :< m) r => A (F (FSum',self,(Su n))) m (Su r)

> type FSum  = Rec (F FSum')   -- now we tie up the knot

After we define a few sample numerals, we can add them

> type N0 = Zero; type N1 = Su N0; type N2 = Su N1; type N3 = Su N2
> (n0::N0, n1::N1, n2::N2, n3::N3) = undefined

> test_sum :: E (F FSum :< x :< y) r => x -> y -> r
> test_sum = undefined
>
> test_sum_2_3 = test_sum n2 n3

  *TypeLC> :t test_sum_2_3
  test_sum_2_3 :: Su (Su (Su (Su (Su Zero))))


Finally, the standard test -- Fibonacci

> vfib = fix(\self n -> case n of 0 -> 1
>                                 1 -> 1
>                                 (n+2) -> (self n) + (self (n+1)))


> data Fib'

> instance A (F Fib') self (F (Fib',self))    -- build closure
> instance A (F (Fib',self)) Zero (Su Zero)
> instance A (F (Fib',self)) (Su Zero) (Su Zero)
> instance E (F FSum :< (self :< n) :< (self :< (Su n))) r 
>     => A (F (Fib',self)) (Su (Su n)) r


> type Fib  = Rec (F Fib')
> test_fib :: E (F Fib :< n) r => n -> r
> test_fib = undefined
>
> test_fib_5 = test_fib (test_sum n3 n2)


Finally, we demonstrate that our calculus is combinatorially complete,
by writing the S and K combinators

> data CombK
> instance A (F CombK) a (F (CombK,a))
> instance A (F (CombK,a)) b a
>
> data CombS
> instance A (F CombS) f (F (CombS,f))
> instance A (F (CombS,f)) g (F (CombS,f,g))
> instance E (f :< x :< (g :< x)) r => A (F (CombS,f,g)) x r

A few examples: SKK as the identity

> type Test_skk x = E (F CombS :< F CombK :< F CombK :< x) r => r
> test_skk1 = undefined:: Test_skk HTrue

and the representation of numerals in the SK calculus. The expression
(F FSum :< Su Zero) is a partial application of the function sum to 1.

> type CombZ   = F CombS :< F CombK
> type CombSu  = F CombS :< (F CombS :< (F CombK :< F CombS) :< F CombK)
> type CombTwo = CombSu :< (CombSu :< CombZ)
> test_ctwo :: E (CombTwo :< (F FSum :< Su Zero) :< Zero) r => r
> test_ctwo = undefined


We define the instances of Show to be able to show things. We define
the instances in a way that the value is not required.

> instance Show HTrue  where show _ = "HTrue"
> instance Show HFalse where show _ = "HFalse"
> class Nat a where fromNat :: a -> Integer
> instance Nat Zero where fromNat _ = 0
> instance Nat x => Nat (Su x) where fromNat _ = succ (fromNat (undefined::x))
> instance Show Zero  where show _ = "N0"
> instance Nat x => Show (Su x) where
>     show x = "N" ++ (show (fromNat x))


