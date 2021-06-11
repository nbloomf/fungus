---
title: Lambda Terms
header-includes: |
  \usepackage{bussproofs}
---



Contents
--------

- [Frontmatter](#frontmatter)
- [Syntax](#syntax)
- [Free and Bound Variables](#free-and-bound-variables)
- [Alpha Equivalence](#alpha-equivalence)





Frontmatter
-----------

This module is literate Haskell and contains a mix of proofs and code. The following boilerplate has to be included here at the beginning.

> module Fungus.LambdaTerm where
> 
> import qualified Data.Map as M
> import qualified Data.Set as S
> import qualified Data.Text as T
> import           Test.QuickCheck
> import           Test.QuickCheck.Property
> 
> import Fungus.ParserUtils

I'm following the approach (particularly for substitution) given in [Stoughton88](@Stoughton88) almost verbatim.





Syntax
------

In this section we'll define the syntax of lambda calculus as a set of _strings_. We use ``monospaced characters`` to represent literal strings while _italicized characters_ are string variables; concatenation of strings is denoted by juxtaposition. If $A$ and $B$ are sets of strings, then $AB$ denotes the set of all pairwise concatenations of strings in $A$ and $B$.

::: definition :::
($\lambda$-terms.) Let $\LambdaIdents$ denote the set of nonempty strings of latin alphanumeric characters whose first character is a lower case letter. Let $\LambdaConsts$ be a set of nonempty strings whose first character is not $\lambda$, ``@``, ``(``, or a lower case letter. The set $\LambdaTerms$ of $\lambda$-_terms_ is the smallest set of strings which satisfies the following.

1. If $x \in \LambdaIdents$, then $x \in \LambdaTerms$; strings of this form are called _variables_.
2. If $c \in \LambdaConsts$, then $c \in \LambdaTerms$; strings of this form are called _constants_.
3. If $x \in \LambdaIdents$ and $e \in \LambdaTerms$, then $\lamex{x}{e} \in \LambdaTerms$.
4. If $x \in \LambdaIdents$ and $e_1, e_2 \in \LambdaTerms$, then $\letin{x}{e_1}{e_2} \in \LambdaTerms$.
5. If $e_1, e_2 \in \LambdaTerms$, then $\apply{e_1}{e_2} \in \LambdaTerms$.
::::::::::::::::::

It may seem odd at first to define a set by invoking its minimalness like this. To see why this is ok, consider the (small) class of all sets of strings which are "closed" in the sense described by the definition of $\LambdaTerms$. This class is not empty since it includes the set of all strings as a member, and the $n$-ary intersection of closed sets is again closed, so we can take the intersection of the class.

We can also give a concrete description of $\LambdaTerms$ which is handy for writing proofs.

::: theorem :::
Define a sequence $S_n$ for $n \in \nats$ recursively as follows.

$$\begin{eqnarray*}
S_0 & = & \LambdaIdents \cup \LambdaConsts \\
S_{n+1} & = & S_n \\
 & & \cup \, \{ \lamex{x}{e} \mid x \in \LambdaIdents, e \in S_n \} \\
 & & \cup \, \{ \letin{x}{e_1}{e_2} \mid x \in \LambdaIdents, e_1, e_2 \in S_n \} \\
 & & \cup \, \{ \apply{e_1}{e_2} \mid e_1, e_2 \in S_n \}
\end{eqnarray*}$$

Then $\bigcup_{i \in \nats} S_i = \LambdaTerms$.

::: proof :::
First we show that $S_i \subseteq \LambdaTerms$ for all $i \in \nats$ by induction on $i$. For the base case, certainly $S_0 \subseteq \LambdaTerms$. For the inductive step, suppose $S_n \subseteq \LambdaTerms$ for some $n$. There are four ways a string $s$ can be in $S_{n+1}$, and in each case we have $s \in \LambdaTerms$ using either the closure of $\LambdaTerms$ or the inductive hypothesis. So we have $S_i \subseteq \LambdaTerms$ for each $i$, and thus $\bigcup S_i \subseteq \LambdaTerms$ as needed.

To see that $\bigcup S_i \supseteq \LambdaTerms$, it suffices to show that $\bigcup S_i$ is closed; since $\LambdaTerms$ is the intersection over all closed sets the inclusion follows. To this end, note first that $S_n \subseteq S_m$ whenever $n \leq m$. Now $$\LambdaIdents \cup \LambdaConsts = S_0 \subseteq \bigcup S_i;$$ this handles the first two closure cases. We consider the remaining three in turn.

1. Suppose $x \in \LambdaIdents$ and $e \in \bigcup S_i$. Then we have $e \in S_n$ for some particular $n$, and so $\lamex{x}{e} \in S_{n+1} \subseteq \bigcup S_i$ by definition.

2. Suppose $x \in \LambdaTerms$ and $e_1, e_2 \in \bigcup S_i$; then we have $e_1 \in S_{n_1}$ and $e_2 \in S_{n_2}$ for some particular $n_1$ and $n_2$. By definition, we have $$\letin{x}{e_1}{e_2} \in S_{\max(n_1,n_2)} \subseteq \bigcup S_i$$ as needed.

3. Suppose $e_1, e_2 \in \bigcup S_i$; then we have $e_1 \in S_{n_1}$ and $e_2 \in S_{n_2}$ for some particular $n_1$ and $n_2$. By definition, we have $$\apply{e_1}{e_2} \in S_{\max(n_1,n_2)} \subseteq \bigcup S_i$$ as needed.

So $\bigcup S_i$ is closed, and thus $\LambdaTerms \subseteq \bigcup S_i$. We then have $\LambdaTerms = \bigcup S_i$ as claimed.
:::::::::::::
:::::::::::::::

The limit-based characterization of $\LambdaTerms$ suggests a natural way to "measure" its elements.

::: definition :::
Let $e \in \LambdaTerms$. Then there exists a $k \in \nats$ with $e \in S_k$. The smallest such $k$ is called the _height_ of $e$, denoted $\height(e)$.
::::::::::::::::::

We're using the well-ordering property of $\nats$ to define $\height$ here, which means this is a non-constructive definition. However we can characterize it using (terminating) recursion as in the following result.

::: theorem :::
(Structure of $\lambda$-terms.) If $z \in \LambdaTerms$ then one (and only one) of the following holds.

1. $z \in \LambdaIdents$.
2. $z \in \LambdaConsts$.
3. $z = \lamex{x}{e}$ where $e \in \LambdaTerms$ and $\height(z) = 1 + \height(e)$.
4. $z = \letin{x}{e_1}{e_2}$ where $e_1,e_2 \in \LambdaTerms$ and $\height(z) = 1 + \max(\height(e_1), \height(e_2))$.
5. $z = \apply{e_1}{e_2}$ where $e_1,e_2 \in \LambdaTerms$ and $\height(z) = 1 + \max(\height(e_1), \height(e_2))$.

::: proof :::
Let $z \in \LambdaTerms$ and let $\height(z) = k$. We consider two cases: either $k = 0$ or $k = n+1$ for some $n$.

If $k = 0$, then $z \in S_0$, so by definition either $z \in \LambdaIdents$ or $z \in \LambdaConsts$ as needed.

Suppose instead that $k = n+1$ for some $n$, so that $z \in S_{n+1}$. Since $k$ is minimal with $z \in S_k$, we have $z \notin S_n$. Then there are three possibilities.

1. Suppose $z = \lamex{x}{e}$ with $e \in S_n$. If $e \in S_i$ for some $i < n$ then we have $z \in S_{i+1}$, violating the minimalness of $n+1$. So in fact $\height(e) = n$ and we have $\height(z) = 1 + \height(e)$.

2. Suppose $z = \letin{x}{e_1}{e_2}$ with $e_1, e_2 \in S_n$. Set $h_1 = \height(e_1)$ and $h_2 = \height(e_2)$. Note that $h_1, h_2 \leq n$. If both of these inequalities are strict, say $e_1, e_2 \in S_i$ with $i < n$, then we have $z \in S_{i+1}$, violating the minimalness of $n+1$. So at least one of $h_1$ and $h_2$ is equal to $n$ and we have $\height(z) = 1 + \max(\height(e_1),\height(e_2))$.

3. Suppose $z = \apply{e_1}{e_2}$ with $e_1, e_2 \in S_n$. Set $h_1 = \height(e_1)$ and $h_2 = \height(e_2)$. Note that $h_1, h_2 \leq n$. If both of these inequalities are strict, say $e_1, e_2 \in S_i$ with $i < n$, then we have $z \in S_{i+1}$, violating the minimalness of $n+1$. So at least one of $h_1$ and $h_2$ is equal to $n$ and we have $\height(z) = 1 + \max(\height(e_1),\height(e_2))$.

The "and only one" part is trivial because each of the five forms starts with a different character; no string can match more than one.
:::::::::::::
:::::::::::::::

There is an alternative notation we will sometimes prefer when expressing the five closure properties of $\lambda$-terms: natural deduction style _inference rules_. These are the big fraction looking things we see so often in type theory literature.

::: definition :::
[@lambda-syntax-inference-rules]()($\lambda$-terms, natural deduction style.) We define $\LambdaTerms$ to be the smallest set satisfying the following rule schemas.

$$\begin{prooftree}
\AxiomC{$x \in \LambdaIdents$}
\RightLabel{$\mathsf{Var}_\lambda$}
\UnaryInfC{$x \in \LambdaTerms$}
\end{prooftree}$$

$$\begin{prooftree}
\AxiomC{$c \in \LambdaConsts$}
\RightLabel{$\mathsf{Con}_\lambda$}
\UnaryInfC{$c \in \LambdaTerms$}
\end{prooftree}$$

$$\begin{prooftree}
\AxiomC{$x \in \LambdaIdents$}
\AxiomC{$e \in \LambdaTerms$}
\RightLabel{$\mathsf{Abs}_\lambda$}
\BinaryInfC{$\lamex{x}{e} \in \LambdaTerms$}
\end{prooftree}$$

$$\begin{prooftree}
\AxiomC{$x \in \LambdaIdents$}
\AxiomC{$e_1 \in \LambdaTerms$}
\AxiomC{$e_2 \in \LambdaTerms$}
\RightLabel{$\mathsf{Let}_\lambda$}
\TrinaryInfC{$\letin{x}{e_1}{e_2} \in \LambdaTerms$}
\end{prooftree}$$

$$\begin{prooftree}
\AxiomC{$e_1 \in \LambdaTerms$}
\AxiomC{$e_2 \in \LambdaTerms$}
\RightLabel{$\mathsf{App}_\lambda$}
\BinaryInfC{$\apply{e_1}{e_2} \in \LambdaTerms$}
\end{prooftree}$$

::::::::::::::::::

Establishing that a particular string is in $\LambdaTerms$ requires evidence, and natural deduction style proof trees are a handy notation for this evidence. For instance, here is a tree establishing that the string ``(x \c)`` is a $\lambda$-term.

$$\begin{prooftree}
\AxiomC{$x \in \LambdaIdents$}
\RightLabel{$\mathsf{Var}_\lambda$}
\UnaryInfC{$x \in \LambdaTerms$}
\AxiomC{$\backslash c \in \LambdaConsts$}
\RightLabel{$\mathsf{Con}_\lambda$}
\UnaryInfC{$\backslash c \in \LambdaTerms$}
\RightLabel{$\mathsf{App}_\lambda$}
\BinaryInfC{$\apply{x}{\backslash c} \in \LambdaTerms$}
\end{prooftree}$$

The structure theorem for $\lambda$-terms justifies modeling $\LambdaTerms$ using the following Haskell type.

> data LambdaTerm a
>   = VariableTerm a LambdaVariable
>   | ConstantTerm a LambdaConstant
>   | Abstraction  a (LambdaVariable, a) (LambdaTerm a)
>   | LetBinding   a (LambdaVariable, a) (LambdaTerm a) (LambdaTerm a)
>   | Application  a                     (LambdaTerm a) (LambdaTerm a)
>   deriving (Show)
> 
> newtype LambdaVariable = LambdaVariable
>   { unLambdaVariable :: T.Text
>   } deriving (Eq, Ord, Show)
> 
> newtype LambdaConstant = LambdaConstant
>   { unLambdaConstant :: T.Text
>   } deriving (Eq, Ord, Show)
> 
> instance Functor LambdaTerm where
>   fmap f = \case
>     VariableTerm a x            -> VariableTerm (f a) x
>     ConstantTerm a c            -> ConstantTerm (f a) c
>     Abstraction  a (x, b) e     -> Abstraction  (f a) (x, f b) (fmap f e)
>     LetBinding   a (x, b) e1 e2 -> LetBinding   (f a) (x, f b) (fmap f e1) (fmap f e2)
>     Application  a        e1 e2 -> Application  (f a)          (fmap f e1) (fmap f e2)
> 
> instance Eq (LambdaTerm a) where
>   z1 == z2 = case (z1,z2) of
>     (VariableTerm _ x1, VariableTerm _ x2) -> x1 == x2
>     (ConstantTerm _ c1, ConstantTerm _ c2) -> c1 == c2
>     (Abstraction _ (x1, _) e1, Abstraction _ (x2, _) e2) -> x1 == x2 && e1 == e2
>     (LetBinding _ (x1, _) e1 f1, LetBinding _ (x2, _) e2 f2) -> x1 == x2 && e1 == e2 && f1 == f2
>     (Application _ e1 f1, Application _ e2 f2) -> e1 == e2 && f1 == f2
>     _ -> False

We've made one addition: these expressions are decorated with an extra value of type `a`. We'll use this later to include type annotations and source location information, but for now it can just be `()`. Annotations are ignored for the purpose of equality testing.

> class LambdaAnnotation a where
>   emptyLambdaAnnotation :: a
> 
> instance LambdaAnnotation () where
>   emptyLambdaAnnotation = ()
> 
> lambda :: (LambdaAnnotation a) => LambdaVariable -> LambdaTerm a -> LambdaTerm a
> lambda x e = Abstraction emptyLambdaAnnotation (x, emptyLambdaAnnotation) e
> 
> letin :: (LambdaAnnotation a) => LambdaVariable -> LambdaTerm a -> LambdaTerm a -> LambdaTerm a
> letin x e1 e2 = LetBinding emptyLambdaAnnotation (x, emptyLambdaAnnotation) e1 e2

Note that ``LambdaTerm a`` is not a set of strings! What we've done is encode the set of _valid derivations_ of $\lambda$-terms as a type; the structure of ``LambdaTerm`` is precisely the structure of a derivation that a given string is in $\LambdaTerms$, at least when ``a`` is ``()``.

Translating the $\height$ function from the theorem is straightforward.

> heightOfLambdaTerm :: LambdaTerm a -> Integer
> heightOfLambdaTerm = \case
>   VariableTerm _ _       -> 0
>   ConstantTerm _ _       -> 0
>   Abstraction  _ _ e     -> 1 + heightOfLambdaTerm e
>   LetBinding   _ _ e1 e2 -> 1 + max (heightOfLambdaTerm e1) (heightOfLambdaTerm e2)
>   Application  _   e1 e2 -> 1 + max (heightOfLambdaTerm e1) (heightOfLambdaTerm e2)

The structure theorem also justifies our use of recursive definitions of functions on $\LambdaTerms$; we can define a function on $\lambda$-terms by specifying it on variables and constants (the base case) and then for all other constructs in terms of its values on shorter terms (the recursive case). For example, we can use this to define the _size_ of a term.

::: definition :::
The _size_ of a lambda term is defined recursively as follows.

1. If $x \in \LambdaIdents$ then $\size(x) = 0$.
2. If $c \in \LambdaConsts$ then $\size(c) = 0$.
3. $\size(\lamex{x}{e}) = 1 + \size(e)$.
4. $\size(\letin{x}{e_1}{e_2}) = 1 + \size(e_1) + \size(e_2)$.
5. $\size(\apply{e_1}{e_2}) = 1 + \size(e_1) + \size(e_2)$.
::::::::::::::::::

Recursive functions translate to the Haskell representation cleanly.

> sizeOfLambdaTerm :: LambdaTerm a -> Integer
> sizeOfLambdaTerm = \case
>   VariableTerm _ _       -> 0
>   ConstantTerm _ _       -> 0
>   Abstraction  _ _ e     -> 1 + sizeOfLambdaTerm e
>   LetBinding   _ _ e1 e2 -> 1 + sizeOfLambdaTerm e1 + sizeOfLambdaTerm e2
>   Application  _   e1 e2 -> 1 + sizeOfLambdaTerm e1 + sizeOfLambdaTerm e2

We can also use recursion as a proof strategy. For example, the height of a $\lambda$-term is bounded by its size. (The main value of this theorem is in demonstrating the structure of an inductive proof on $\lambda$-terms.)

::: theorem :::
For every $\lambda$-term $z$ we have $\height(z) \leq \size(z)$.

::: proof :::
We proceed by structural induction on $z$.

1. If $z \in \LambdaIdents$ we have $\height(z) = 0 = \size(z)$ as needed.

2. If $z \in \LambdaConsts$ we have $\height(z) = 0 = \size(z)$ as needed.

3. Suppose $z = \lamex{x}{e}$. By the induction hypothesis we have $\height(e) \leq \size(e)$, so that $$\height(z) = 1 + \height(e) \leq 1 + \size(e) = \size(z)$$ as needed.

4. Suppose $z = \letin{x}{e_1}{e_2}$. By the induction hypothesis we have $\height(e_1) \leq \size(e_1)$ and $\height(e_2) \leq \size(e_2)$. Now
$$\begin{eqnarray*}
 &      & \height(z) \\
 & =    & 1 + \max(\height(e_1),\height(e_2)) \\
 & \leq & 1 + \height(e_1) + \height(e_2) \\
 & \leq & 1 + \size(e_1) + \size(e_2) \\
 & =    & \size(z)
\end{eqnarray*}$$
as needed.

5. Suppose $z = \apply{e_1}{e_2}$. By the induction hypothesis we have $\height(e_1) \leq \size(e_1)$ and $\height(e_1) \leq \size(e_2)$. Now
$$\begin{eqnarray*}
 &      & \height(z) \\
 & =    & 1 + \max(\height(e_1),\height(e_2)) \\
 & \leq & 1 + \height(e_1) + \height(e_2) \\
 & \leq & 1 + \size(e_1) + \size(e_2) \\
 & =    & \size(z)
\end{eqnarray*}$$
as needed.
:::::::::::::
:::::::::::::::

Theorems are a natural source of property tests for our code; these are tests that hammer a function with random inputs and verify that some specified property always holds.

> prop_heightOfLambdaTerm_lt_sizeOfLambdaTerm
>   :: forall a. LambdaTerm a -> Bool
> prop_heightOfLambdaTerm_lt_sizeOfLambdaTerm e =
>   heightOfLambdaTerm e <= sizeOfLambdaTerm e

Property tests serve as a good check that (1) the proof of the theorem and (2) the translation into Haskell are correct (or at least not incorrect). We'll try to include them whenever possible; they are devastatingly effective at finding bugs. To use them, we'll need to be able to generate arbitrary values of type ``LambdaTerm a``.

> instance (Arbitrary a) => Arbitrary (LambdaTerm a) where
>   arbitrary = getSize >>= generateDepth
>     where
>       generateDepth :: Int -> Gen (LambdaTerm a)
>       generateDepth k
>         | k <= 0 = oneof
>             [ VariableTerm <$> arbitrary <*> arbitrary
>             , ConstantTerm <$> arbitrary <*> arbitrary
>             ]
>         | otherwise = do
>             let recur = elements [0..(k `div` 2)] >>= generateDepth
>             oneof
>               [ Abstraction <$> arbitrary <*> arbitrary <*> recur
>               , LetBinding  <$> arbitrary <*> arbitrary <*> recur <*> recur
>               , Application <$> arbitrary <*>               recur <*> recur
>               ]
> 
>   shrink = \case
>     ConstantTerm loc c ->
>       map (ConstantTerm loc) $ shrink c
>     VariableTerm loc v ->
>       map (VariableTerm loc) $ shrink v
>     Abstraction loc x e ->
>       (e:) $ map (Abstraction loc x) $ shrink e
>     LetBinding loc x e1 e2 -> concat
>       [ [ e1, e2 ]
>       , [ LetBinding loc x f1 e2 | f1 <- shrink e1 ]
>       , [ LetBinding loc x e1 f2 | f2 <- shrink e2 ]
>       ]
>     Application loc e1 e2 -> concat
>       [ [ e1, e2 ]
>       , [ Application loc f1 e2 | f1 <- shrink e1 ]
>       , [ Application loc e1 f2 | f2 <- shrink e2 ]
>       ]
> 
> instance Arbitrary LambdaVariable where
>   arbitrary = do
>     let
>       xs = "xyzw"
> 
>       ident :: [Char] -> Gen T.Text
>       ident as = do
>         c <- elements as
>         NonNegative k <- arbitrary :: Gen (NonNegative Int)
>         p <- arbitrary
>         return $ T.pack $ if p
>           then [c]
>           else [c] <> show k
> 
>     LambdaVariable <$> ident xs
> 
>   shrink (LambdaVariable x) =
>     case T.unpack x of
>       []   -> []
>       c:[] -> []
>       c:cs -> map (LambdaVariable . T.pack . (c:)) $ shrink cs
> 
> instance Arbitrary LambdaConstant where
>   arbitrary = do
>     let
>       cs = "abcd"
> 
>       ident :: [Char] -> Gen T.Text
>       ident as = do
>         c <- elements as
>         NonNegative k <- arbitrary :: Gen (NonNegative Int)
>         p <- arbitrary
>         return $ T.pack $ if p
>           then [c]
>           else [c] <> show k
> 
>     LambdaConstant <$> ident cs
> 
>   shrink (LambdaConstant x) =
>     case T.unpack x of
>       []   -> []
>       c:[] -> []
>       c:cs -> map (LambdaConstant . T.pack . (c:)) $ shrink cs

We need a few more definitions before we can state and prove more interesting things about $\lambda$-terms.





Free and Bound Variables
------------------------

Note that in the $\lambda$ [construction rules](@lambda-syntax-inference-rules), variables can be introduced in two fundamentally different ways. In $\mathsf{Var}_\lambda$, variables are themselves terms. In $\mathsf{Abs}_\lambda$ and $\mathsf{Let}_\lambda$, however, the variable is not a term on its own. In these latter two cases we say the variable appearance is a _binding site_. Then given a $\lambda$ term of the form $\lamex{x}{e}$ or $\letin{x}{f}{e}$, any occurrence of $x$ in $e$ is _bound_ -- although not necessarily at that binding site, if there is a deeper binding of $x$ that shadows the outer binding.

If a variable in a $\lambda$-term is not bound, it is _free_. We can formalize the set of free variables in a term with a recursive function.

::: definition :::
The set of _free variables_ in a $\lambda$-term $z$, denoted $\freeLambdaVars(z)$, is defined recursively as follows.

1. If $x \in \LambdaIdents$ then $\freeLambdaVars(x) = \{x\}$.
2. If $c \in \LambdaConsts$ then $\freeLambdaVars(c) = \varnothing$.
3. $\freeLambdaVars(\lamex{x}{e}) = \freeLambdaVars(e) \setminus \{x\}$.
4. $\freeLambdaVars(\letin{x}{e_1}{e_2}) = \freeLambdaVars(e_1) \cup (\freeLambdaVars(e_2) \setminus \{x\})$.
5. $\freeLambdaVars(\apply{e_1}{e_2}) = \freeLambdaVars(e_1) \cup \freeLambdaVars(e_2)$.
::::::::::::::::::

As usual, the translation to Haskell is straightforward.

> freeLambdaVariablesInLambdaTerm
>   :: forall a. LambdaTerm a -> S.Set LambdaVariable
> freeLambdaVariablesInLambdaTerm = \case
>   VariableTerm _ x -> S.singleton x
>   ConstantTerm _ _ -> S.empty
>   Abstraction _ (x, _) e ->
>     S.delete x $ freeLambdaVariablesInLambdaTerm e
>   LetBinding _ (x, _) e1 e2 -> S.union
>     (freeLambdaVariablesInLambdaTerm e1)
>     (S.delete x $ freeLambdaVariablesInLambdaTerm e2)
>   Application _ e1 e2 -> S.union
>     (freeLambdaVariablesInLambdaTerm e1)
>     (freeLambdaVariablesInLambdaTerm e2)

It's worth stating that any given $\lambda$-term has finitely many free variables, because then $\LambdaIdents \setminus \freeLambdaVars(z)$ is always nonempty.

::: lemma :::
For any $\lambda$-term $z$, $\freeLambdaVars(z)$ is finite.

::: proof :::
By structural induction on $\lambda$-terms. The empty set and singleton sets are finite, subsets of a finite set are finite, and the pairwise union of finite sets is finite.
:::::::::::::
:::::::::::::

We'll also assume the existence of a distinguished function $\choice : \mathcal{P}(\LambdaIdents) \setminus \varnothing  \rightarrow \LambdaIdents$ which selects an element from a nonempty set of variables. We can avoid using the axiom of choice here by assuming an ordering on variables and taking the smallest one. This ordering doesn't have to be the obvious one, either; for example, consider the graded ordering that considers $\mathsf{x0}, \mathsf{x1}, \ldots$ to be smaller than all other identifiers, and then compares using the ordinary lexicographic order. Then if $A$ is not finite then $\choice(A)$ will be of the form $\mathsf{x}n$ for some $n \in \nats$. (This is useful for our implementation of $\choice$.)

The free variables in a $\lambda$-expression are subject to substitution.

::: definition :::
Functions $\LambdaIdents \rightarrow \LambdaTerms$ are called _substitutions_. Given an identifier $x$, a $\lambda$-term $z$, and a substitution $\sigma$, we define a set $\new(x,z,\sigma)$ by $$\new(x,z,\sigma) = \{ y \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(z) \setminus \{x\}\ \mathrm{then}\ y \notin \freeLambdaVars(\sigma(u)) \}.$$

We also define a _pointwise update_ operation. Given $\sigma$, we define $\sigma_{v/u}$ by $$\sigma_{v/u}(x) = \left\{\begin{array}{ll} v & \mathrm{if}\ x = u \\ \sigma(x) & \mathrm{otherwise}. \end{array}\right.$$

The set of all substitutions is denoted $\LambdaSubstitutions$.
::::::::::::::::::

That is, $\new(x,z,\sigma)$ consists of those variables which are not free in any $\sigma(u)$ where $u$ ranges over the free variables in $z$, except for $x$. The set of variables $y$ _can't_ be is finite, so $\new(x,z,\sigma)$ is always infinite (in particular, it's not empty.)

Substitutions are defined as functions from variables to terms, but in practice they will be the identity on all but a finite number of inputs. For this reason we can implement them as finite maps and decree that such a map is the identity outside of its explicit domain. This is important for our implementation.

We'd like to implement $\new$ in code, however this is awkward because the value of $\new(x,z,\sigma)$ is an infinite set. Instead we'll implement $\new$ as a predicate on variables; ``isNewLambdaVar x z sigma y`` will return ``True`` precisely when $y \in \new(x,z,\sigma)$. Then we can implement $\choice(\new(x,z,\sigma))$ by taking the first identifier $\mathsf{x}n$ which satisfies the predicate.

> isNewLambdaVar
>   :: LambdaVariable -> LambdaTerm a -> M.Map LambdaVariable (LambdaTerm a)
>   -> LambdaVariable -> Bool
> isNewLambdaVar x z sigma y =
>   let
>     -- M.Map values are finite, so we implicitly
>     -- make sigma the identity outside of its support
>     freeImageOf u = case M.lookup u sigma of
>       Nothing -> S.singleton u
>       Just e  -> freeLambdaVariablesInLambdaTerm e
>   in all
>     (\u -> S.notMember y $ freeImageOf u)
>     (S.delete x $ freeLambdaVariablesInLambdaTerm z)
> 
> chooseNewLambdaVar
>   :: LambdaVariable -> LambdaTerm a -> M.Map LambdaVariable (LambdaTerm a) -> LambdaVariable
> chooseNewLambdaVar x z sigma = head
>   $ filter (isNewLambdaVar x z sigma)
>   $ map (\k -> LambdaVariable $ T.pack ("x" <> show k))
>   $ [0..]

We can also implement the pointwise update operator.

> variableUpdateSub
>   :: (LambdaAnnotation a)
>   => LambdaVariable -> LambdaVariable
>   -> M.Map LambdaVariable (LambdaTerm a) -> M.Map LambdaVariable (LambdaTerm a)
> variableUpdateSub y x = M.insert x (VariableTerm emptyLambdaAnnotation y)

We're now prepared to define substitution of variables.

::: definition :::
Let $z$ be a $\lambda$-term and $\sigma$ a substitution. The _simultaneous substitution_ of $\sigma$ on $z$, denoted $\sigma[z]$, yields a new $\lambda$-term, defined by structural recursion as follows.

1. If $z \in \LambdaIdents$ then $\sigma[z] = \sigma(z)$.
2. If $z \in \LambdaConsts$ then $\sigma[z] = z$.
3. If $z = \lamex{x}{e}$ then $\sigma[z] = \lamex{y}{\sigma_{y/x}[e]}$ where $y = \choice(\new(x,e,\sigma))$.
4. If $z = \letin{x}{e_1}{e_2}$ then $\sigma[z] = \letin{y}{\sigma[e_1]}{\sigma_{y/x}[e_2]}$ where $y = \choice(\new(x,e_2,\sigma))$.
5. If $z = \apply{e_1}{e_2}$ then $\sigma[z] = \apply{\sigma[e_1]}{\sigma[e_2]}$.
::::::::::::::::::

The Haskell translation is straightforward. Also note that as a consequence of modeling substitutions using finite maps, we can model the identity substitution $\mathsf{id}$ using the empty `Map`.

> applySubToLambdaTerm
>   :: M.Map LambdaVariable (LambdaTerm a) -> LambdaTerm a -> LambdaTerm a
> applySubToLambdaTerm sigma = \case
>   VariableTerm a x ->
>     M.findWithDefault (VariableTerm a x) x sigma
>   ConstantTerm a c ->
>     ConstantTerm a c
>   Abstraction a (x, b) e ->
>     let y = chooseNewLambdaVar x e sigma
>     in Abstraction a (y, b)
>       (applySubToLambdaTerm (M.insert x (VariableTerm b y) sigma) e)
>   LetBinding a (x, b) e1 e2 ->
>     let y = chooseNewLambdaVar x e2 sigma
>     in LetBinding a (y, b)
>       (applySubToLambdaTerm sigma e1)
>       (applySubToLambdaTerm (M.insert x (VariableTerm b y) sigma) e2)
>   Application a e1 e2 ->
>     Application a
>       (applySubToLambdaTerm sigma e1)
>       (applySubToLambdaTerm sigma e2)
> 
> identitySub :: M.Map LambdaVariable (LambdaTerm a)
> identitySub = M.empty

At this point we can prove some basic facts about free variables of substitutions. First, we can characterize the free variables in an applied substitution.

::: theorem :::
[@free-vars-subst]()(Free variables in an applied substitution.) Let $z$ be a $\lambda$-term and $\sigma$ a substitution. Then we have $$\freeLambdaVars(\sigma[z]) = \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t)).$$

::: proof :::
We proceed by structural induction on $z$.

1. If $z \in \LambdaIdents$, we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma[z]) \\
 & = & \freeLambdaVars(\sigma(z)) \\
 & = & \bigcup_{t \in \{z\}} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t))
\end{eqnarray*}$$
as claimed.

2. If $z \in \LambdaConsts$, we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma[z]) \\
 & = & \freeLambdaVars(z) \\
 & = & \varnothing \\
 & = & \bigcup_{t \in \varnothing} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t))
\end{eqnarray*}$$
as claimed.

3. Suppose $z = \lamex{x}{e}$. Let $y = \choice(\new(x,e,\sigma))$; note that by definition, if $t \in \freeLambdaVars(e) \setminus \{x\}$ then $y \notin \freeLambdaVars(\sigma(t))$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma[z]) \\
 & = & \freeLambdaVars(\sigma[\lamex{x}{e}]) \\
 & = & \freeLambdaVars(\lamex{y}{\sigma_{y/x}[e]}) \\
 & = & \freeLambdaVars(\sigma_{y/x}[e]) \setminus \{y\} \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e)} \freeLambdaVars(\sigma_{y/x}(t)) \right] \setminus \{y\} \\
 & = & \left[ \freeLambdaVars(\sigma_{y/x}(x)) \cup \bigcup_{t \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma_{y/x}(t)) \right] \setminus \{y\} \\
 & = & \left[ \freeLambdaVars(y) \cup \bigcup_{t \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \setminus \{y\} \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \setminus \{y\} \\
 & = & \bigcup_{t \in \freeLambdaVars(\lamex{x}{e})} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t))
\end{eqnarray*}$$
as claimed.

4. Suppose $z = \letin{x}{e_1}{e_2}$. Let $y = \choice(\new(x,e_2,\sigma))$; note that by definition, if $t \in \freeLambdaVars(e_2) \setminus \{x\}$ then $y \notin \freeLambdaVars(\sigma(t))$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma[z]) \\
 & = & \freeLambdaVars(\sigma[\letin{x}{e_1}{e_2}]) \\
 & = & \freeLambdaVars(\letin{y}{\sigma[e_1]}{\sigma_{y/x}[e_2]}) \\
 & = & \freeLambdaVars(\sigma[e_1]) \cup (\freeLambdaVars(\sigma_{y/x}[e_2]) \setminus \{y\}) \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e_1)} \freeLambdaVars(\sigma(t)) \right] \cup \left[ \left( \bigcup_{t \in \freeLambdaVars(e_2)} \freeLambdaVars(\sigma_{y/x}(t)) \right) \setminus \{y\} \right] \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e_1)} \freeLambdaVars(\sigma(t)) \right] \cup \left[ \left( \freeLambdaVars(\sigma_{y/x}(x)) \cup \bigcup_{t \in \freeLambdaVars(e_2) \setminus \{x\}} \freeLambdaVars(\sigma_{y/x}(t)) \right) \setminus \{y\} \right] \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e_1)} \freeLambdaVars(\sigma(t)) \right] \cup \left[ \left( \freeLambdaVars(y) \cup \bigcup_{t \in \freeLambdaVars(e_2) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right) \setminus \{y\} \right] \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(e_1)} \freeLambdaVars(\sigma(t)) \right] \cup \left[ \bigcup_{t \in \freeLambdaVars(e_2) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \\
 & = & \bigcup_{t \in \freeLambdaVars(e_1) \cup (\freeLambdaVars(e_2) \setminus \{x\})} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(\letin{x}{e_1}{e_2})} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t))
\end{eqnarray*}$$
as claimed.

5. Suppose $z = \apply{e_1}{e_2}$. Then we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma[z]) \\
 & = & \freeLambdaVars(\sigma[\apply{e_1}{e_2}]) \\
 & = & \freeLambdaVars(\apply{\sigma[e_1]}{\sigma[e_2]}) \\
 & = & \freeLambdaVars(\sigma[e_1]) \cup \freeLambdaVars(\sigma[e_2]) \\
 & = & \bigcup_{t \in \freeLambdaVars(e_1)} \freeLambdaVars(\sigma(t)) \cup \bigcup_{t \in \freeLambdaVars(e_2)} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(e_1) \cup \freeLambdaVars(e_2)} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(\apply{e_1}{e_2})} \freeLambdaVars(\sigma(t)) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma(t))
\end{eqnarray*}$$
as claimed.
:::::::::::::
:::::::::::::::

We can also express this theorem as a property test.

> prop_free_vars_in_applied_lambda_sub
>   :: forall a. LambdaTerm a -> M.Map LambdaVariable (LambdaTerm a) -> Property
> prop_free_vars_in_applied_lambda_sub z sigma =
>   let
>     freeVarsInImage :: LambdaVariable -> S.Set LambdaVariable
>     freeVarsInImage t = case M.lookup t sigma of
>       Nothing -> S.singleton t
>       Just e  -> freeLambdaVariablesInLambdaTerm e
> 
>   in (===)
>     (freeLambdaVariablesInLambdaTerm (applySubToLambdaTerm sigma z))
>     (S.unions $ S.map freeVarsInImage $ freeLambdaVariablesInLambdaTerm z)

Next, we can characterize the free variables in a pointwise update.

::: theorem :::
[@free-vars-pointwise-update]() Let $x$ and $y$ be variables, $z$ a $\lambda$-term, and $\sigma$ a substitution. Then we have $$\freeLambdaVars(\sigma_{y/x}[z]) = \left[ \bigcup_{t \in \freeLambdaVars(z) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \cup \left\{\begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(z) \\ \varnothing & \mathrm{otherwise}. \end{array}\right.$$
In particular, for $\sigma = \mathsf{id}$, we have $$\freeLambdaVars(\mathsf{id}_{y/x}[z]) = (\freeLambdaVars(z) \setminus \{x\}) \cup \left\{\begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(z) \\ \varnothing & \mathrm{otherwise}. \end{array}\right.$$

::: proof :::
Using the previous characterization of the [free variables in an applied substitution](@free-vars-subst), we have
$$\begin{eqnarray*}
 &   & \freeLambdaVars(\sigma_{y/x}[z]) \\
 & = & \bigcup_{t \in \freeLambdaVars(z)} \freeLambdaVars(\sigma_{y/z}(t)) \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(z) \setminus \{x\}} \freeLambdaVars(\sigma_{y/x}(t)) \right] \cup \left\{\begin{array}{ll} \freeLambdaVars(\sigma_{y/x}(x)) & \mathrm{if}\ x \in \freeLambdaVars(z) \\ \varnothing & \mathrm{otherwise} \end{array}\right. \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(z) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \cup \left\{\begin{array}{ll} \freeLambdaVars(y) & \mathrm{if}\ x \in \freeLambdaVars(z) \\ \varnothing & \mathrm{otherwise} \end{array}\right. \\
 & = & \left[ \bigcup_{t \in \freeLambdaVars(z) \setminus \{x\}} \freeLambdaVars(\sigma(t)) \right] \cup \left\{\begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(z) \\ \varnothing & \mathrm{otherwise} \end{array}\right.
\end{eqnarray*}$$
as claimed.
:::::::::::::
:::::::::::::::

As a property test:

> prop_free_vars_in_applied_pointwise_update_sub
>   :: forall a
>    . (LambdaAnnotation a)
>   => LambdaVariable -> LambdaVariable
>   -> LambdaTerm a -> M.Map LambdaVariable (LambdaTerm a) -> Property
> prop_free_vars_in_applied_pointwise_update_sub y x z sigma =
>   let
>     freeVarsInImage :: LambdaVariable -> S.Set LambdaVariable
>     freeVarsInImage t = case M.lookup t sigma of
>       Nothing -> S.singleton t
>       Just e  -> freeLambdaVariablesInLambdaTerm e
> 
>     freeVarsInImages = S.unions $ S.map freeVarsInImage $
>       S.delete x $ freeLambdaVariablesInLambdaTerm z
> 
>     freeVarsInUpdate = freeLambdaVariablesInLambdaTerm $
>       applySubToLambdaTerm (variableUpdateSub y x sigma) z
> 
>   in if S.member x (freeLambdaVariablesInLambdaTerm z)
>     then (===)
>       (freeVarsInUpdate)
>       (S.union freeVarsInImages (S.singleton y))
>     else (===)
>       (freeVarsInUpdate)
>       (freeVarsInImages)

We also have a sort of composition on substitutions, although it's not the usual function composition.

::: definition :::
Given substitutions $\sigma_1$ and $\sigma_2$, we define their _composite_ $\sigma_2 \sigma_1$ by $$(\sigma_2 \sigma_1)(x) = \sigma_2[\sigma_1(x)].$$
::::::::::::::::::

Translating composition to Haskell is a little trickier because we're representing substitutions as finite maps; just note that if $\sigma_2 \sigma_1$ moves a variable, then it must have been in the support of either $\sigma_1$ or $\sigma_2$.

> composeLambdaSubs
>   :: M.Map LambdaVariable (LambdaTerm a)
>   -> M.Map LambdaVariable (LambdaTerm a)
>   -> M.Map LambdaVariable (LambdaTerm a)
> composeLambdaSubs sigma2 sigma1 =
>   foldr f M.empty (S.union (M.keysSet sigma1) (M.keysSet sigma2))
>   where
>     f x sigma = case M.lookup x sigma1 of
>       Just e  -> M.insert x (applySubToLambdaTerm sigma2 e) sigma
>       Nothing -> case M.lookup x sigma2 of
>         Just e  -> M.insert x e sigma
>         Nothing -> sigma

At this point there are several properties about free variables and substitution we'd like to prove, however we're not quite ready yet. We need a looser notion of equality for $\lambda$-terms that captures the intuition that "renaming the bound variables" doesn't fundamentally change the _meaning_ of a term. This is what we'll discuss next.





Alpha Equivalence
-----------------

We define an equivalence relation on $\LambdaTerms$ as follows.

::: definition :::
($\alpha$-equivalence.) We denote by $\AlphaEq$ the smallest equivalence relation on $\LambdaTerms$ which satisfies the following.

1. $\lamex{x}{e} \AlphaEq \lamex{y}{f}$ if either
    1. $x = y$ and $e \AlphaEq f$
    2. $y \notin \freeLambdaVars(e)$ and $\mathsf{id}_{y/x}[e] \AlphaEq f$.
2. $\letin{x}{e_1}{e_2} \AlphaEq \letin{y}{f_1}{f_2}$ if $e_1 \AlphaEq f_1$ and either
    1. $x = y$ and $e_2 \AlphaEq f_2$
    2. $y \notin \freeLambdaVars(e_2)$ and $\mathsf{id}_{y/x}[e_2] \AlphaEq f_2$.
3. $\apply{e_1}{e_2} \AlphaEq \apply{f_1}{f_2}$ if $e_1 \AlphaEq f_1$ and $e_2 \AlphaEq f_2$.

The hypothesis of (1) will play a role in several results later, so we abbreviate it $\mathcal{A}(e,x,f,y)$. Similarly, the hypothesis of (2) is abbreviated $\mathcal{B}(e_1,e_2,x,f_1,f_2,y)$.
::::::::::::::::::

Again, at first this might seem like an odd way to define an equivalence relation, but we can take the intersection over all equivalences which satisfy the properties (and there's at least one, since the universal relation does). We can go a bit further; the union of the universal relations on terms of each "form" satisfies the conditions, so for example we can say that if $z$ is a lambda abstraction and $z \AlphaEq w$, then $w$ is also a lambda abstraction. This definition does not, however, immediately yield a recursive function to actually decide whether or not two terms are $\alpha$-equivalent.

We can extend $\alpha$-equivalence to substitutions. Given substitutions $\sigma_1$ and $\sigma_2$ and a set $A$ of variables, we say that $\sigma_1 \AlphaEq^A \sigma_2$ if $\sigma_1(a) \AlphaEq \sigma_2(a)$ for all $a \in A$, and we say $\sigma_1 \AlphaEq \sigma_2$ if $\sigma_1 \AlphaEq^{\LambdaIdents} \sigma_2$.

::: lemma :::
[@choice-id-alpha-eq-lemma]() We have the following.

1. If $y \notin \freeLambdaVars(e)$, then $\lamex{x}{e} \AlphaEq \lamex{y}{\mathsf{id}_{y/x}[e]}$.

2. If $y \notin \freeLambdaVars(e_2)$, then $\letin{x}{e_1}{e_2} \AlphaEq \letin{y}{e_1}{\mathsf{id}_{y/x}[e_2]}$.

::: proof :::
To see (1), note that $\mathsf{id}_{y/x}[e] \AlphaEq \mathsf{id}_{y/x}[e]$ since $\AlphaEq$ is reflexive; then the conclusion follows from the defining property of $\AlphaEq$ for lambda expressions.

To see (2), note that $e_1 \AlphaEq e_1$ and $\mathsf{id}_{y/x}[e_2] \AlphaEq \mathsf{id}_{y/x}[e_2]$ by reflexivity; the conclusion follows from the defining property of $\AlphaEq$ for let expressions.
:::::::::::::
:::::::::::::

We haven't seen the Haskell implementation of $\alpha$-equivalence yet, but we can still hit this theorem with a property test.

> prop_lambda_expr_alpha_eq_lemma
>   :: forall a. (LambdaAnnotation a, Show a)
>   => LambdaVariable -> LambdaVariable -> LambdaTerm a -> Property
> prop_lambda_expr_alpha_eq_lemma x y e =
>   (S.notMember y (freeLambdaVariablesInLambdaTerm e))
>     ==>
>   (alphaEqTerm
>     (lambda x e)
>     (lambda y (applySubToLambdaTerm (variableUpdateSub y x identitySub) e)))
> 
> prop_let_expr_alpha_eq_lemma
>   :: forall a. (LambdaAnnotation a, Show a)
>   => LambdaVariable -> LambdaVariable -> LambdaTerm a -> LambdaTerm a -> Property
> prop_let_expr_alpha_eq_lemma x y e1 e2 =
>   (S.notMember y (freeLambdaVariablesInLambdaTerm e2))
>     ==>
>   (alphaEqTerm
>     (letin x e1 e2)
>     (letin y e1 (applySubToLambdaTerm (variableUpdateSub y x identitySub) e2)))

Free variables are invariant under $\alpha$-equivalence.

::: theorem :::
[@thm-alpha-eq-free-vars]() If $z \AlphaEq w$ then $\freeLambdaVars(z) = \freeLambdaVars(w)$.

::: proof :::
Define a relation $\sim$ on $\LambdaTerms$ by $z \sim w$ if and only if $z \AlphaEq w$ and $\freeLambdaVars(z) = \freeLambdaVars(w)$; we show that $\sim$ satisfies the conditions on $\AlphaEq$, so that $\sim$ equals $\AlphaEq$. This requires examining five possibilities.

Suppose $z = \lamex{x}{e}$ and $w = \lamex{y}{f}$. We consider two cases.

1. Suppose $x = y$ and $e \sim f$; that is, $e \AlphaEq f$ and $\freeLambdaVars(e) = \freeLambdaVars(f)$. By the definition of $\AlphaEq$ we have $z \AlphaEq w$, and moreover
    $$\begin{eqnarray*}
     &   & \freeLambdaVars(z) \\
     & = & \freeLambdaVars(\lamex{x}{e}) \\
     & = & \freeLambdaVars(e) \setminus \{x\} \\
     & = & \freeLambdaVars(f) \setminus \{y\} \\
     & = & \freeLambdaVars(\lamex{y}{f}) \\
     & = & \freeLambdaVars(w),
    \end{eqnarray*}$$
    so that $z \sim w$ as needed.

2. Suppose $y \notin \freeLambdaVars(e)$ and $\mathsf{id}_{y/x}[e] \sim f$; that is, $\mathsf{id}_{y/x}[e] \AlphaEq f$ and $\freeLambdaVars(\mathsf{id}_{y/x}[e]) = \freeLambdaVars(f)$. By the definition of $\AlphaEq$ we have $z \AlphaEq w$, and moreover
    $$\begin{eqnarray*}
     &   & \freeLambdaVars(z) \\
     & = & \freeLambdaVars(\lamex{x}{e}) \\
     & = & \freeLambdaVars(e) \setminus \{x\} \\
     & = & (\freeLambdaVars(e) \setminus \{x\}) \setminus\{y\} \\
     & = & \left((\freeLambdaVars(e) \setminus \{x\}) \cup \left\{\begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(e) \\ \varnothing & \mathrm{otherwise} \end{array}\right\}\right) \setminus \{y\} \\
     & = & \freeLambdaVars(\mathsf{id}_{y/x}[e]) \setminus \{y\} \\
     & = & \freeLambdaVars(f) \setminus \{y\} \\
     & = & \freeLambdaVars(\lamex{y}{f}) \\
     & = & \freeLambdaVars(w)
    \end{eqnarray*}$$
    so that $z \sim w$ as needed.

Suppose $z = \letin{x}{e_1}{e_2}$ and $w = \letin{y}{f_1}{f_2}$. We consider two cases.

1. Suppose $x = y$, $e_2 \sim f_2$, and $e_1 \sim f_1$. Now $e_1 \AlphaEq f_1$ and $e_2 \AlphaEq f_2$, so that $z \AlphaEq w$. Moreover, we have
    $$\begin{eqnarray*}
     &   & \freeLambdaVars(z) \\
     & = & \freeLambdaVars(\letin{x}{e_1}{e_2}) \\
     & = & \freeLambdaVars(e_1) \cup (\freeLambdaVars(e_2) \setminus \{x\}) \\
     & = & \freeLambdaVars(f_1) \cup (\freeLambdaVars(f_2) \setminus \{y\}) \\
     & = & \freeLambdaVars(\letin{y}{f_1}{f_2}) \\
     & = & \freeLambdaVars(w)
    \end{eqnarray*}$$
    so that $z \sim w$ as needed.

2. Suppose $y \notin \freeLambdaVars(e_2)$, $\mathsf{id}_{y/x}[e_2] \sim f_2$, and $e_1 \sim f_1$. Now $\mathsf{id}_{y/x}[e_2] \AlphaEq f_2$ and $e_1 \AlphaEq f_1$ and $\freeLambdaVars(\mathsf{id}_{y/x}[e_2]) = \freeLambdaVars(f_2)$ and $\freeLambdaVars(e_1) = \freeLambdaVars(f_1)$, so that $z \AlphaEq w$. Moreover we have
    $$\begin{eqnarray*}
     &   & \freeLambdaVars(z) \\
     & = & \freeLambdaVars(\letin{x}{e_1}{e_2}) \\
     & = & \freeLambdaVars(e_1) \cup (\freeLambdaVars(e_2) \setminus \{x\}) \\
     & = & \freeLambdaVars(e_1) \cup \left( (\freeLambdaVars(e_2) \setminus \{x\}) \setminus\{y\} \right) \\
     & = & \freeLambdaVars(e_1) \cup \left( \left((\freeLambdaVars(e_2) \setminus \{x\}) \cup \left\{\begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(e_2) \\ \varnothing & \mathrm{otherwise} \end{array}\right\}\right) \setminus \{y\} \right) \\
     & = & \freeLambdaVars(e_1) \cup \left( \freeLambdaVars(\mathsf{id}_{y/x}[e_2]) \setminus \{y\} \right) \\
     & = & \freeLambdaVars(f_1) \cup (\freeLambdaVars(f_2) \setminus \{y\}) \\
     & = & \freeLambdaVars(\letin{y}{f_1}{f_2}) \\
     & = & \freeLambdaVars(w)
    \end{eqnarray*}$$
    so that $z \sim w$ as needed.

Suppose $z = \apply{e_1}{e_2}$ and $w = \apply{f_1}{f_2}$, and suppose further that $e_1 \sim f_1$ and $e_2 \sim f_2$; that is, $e_1 \AlphaEq f_1$ and $e_2 \AlphaEq f_2$ and $\freeLambdaVars(e_1) = \freeLambdaVars(f_1)$ and $\freeLambdaVars(e_2) = \freeLambdaVars(f_2)$. By the definition of $\AlphaEq$ we have $z \AlphaEq w$, and moreover
$$\begin{eqnarray*}
 &   & \freeLambdaVars(z) \\
 & = & \freeLambdaVars(\apply{e_1}{e_2}) \\
 & = & \freeLambdaVars(e_1) \cup \freeLambdaVars(e_2) \\
 & = & \freeLambdaVars(f_1) \cup \freeLambdaVars(f_2) \\
 & = & \freeLambdaVars(\apply{f_1}{f_2}) \\
 & = & \freeLambdaVars(w)
\end{eqnarray*}$$
so that $z \sim w$ as needed.

That is, $\sim$ satisfies the condition from the definition of $\AlphaEq$, and thus $\AlphaEq$ is contained in $\sim$ as a set by minimalness. On the other hand, $\sim$ is contained in $\AlphaEq$ by definition. So in fact $\sim$ is equal to $\AlphaEq$. More explicitly, if $z \AlphaEq w$, then _both_ $z \AlphaEq w$ and $\freeLambdaVars(z) = \freeLambdaVars(w)$, as claimed.
:::::::::::::
:::::::::::::::

This claim is also amenable to property testing, although it is difficult to construct random $\alpha$-equivalent pairs to test. This makes the test of lower quality than unqualified property tests, although it's not without value.

> prop_alpha_eq_implies_same_free_vars
>   :: forall a. (Show a)
>   => LambdaTerm a -> LambdaTerm a -> Property
> prop_alpha_eq_implies_same_free_vars z w =
>   if alphaEqTerm z w
>     then (===)
>       (freeLambdaVariablesInLambdaTerm z)
>       (freeLambdaVariablesInLambdaTerm w)
>     else property succeeded

As a consequence of free variable preservation, we can boost $\alpha$-equivalences to an equality of $\new$ sets.

::: corollary :::
[@alpha-eq-to-new-sets]() If $z_1 \AlphaEq z_2$ and $\sigma_1 \AlphaEq^{\freeLambdaVars(z_1) \setminus \{x\}} \sigma_2$, then $\new(x,z_1,\sigma_1) = \new(x,z_2,\sigma_2)$.

::: proof :::
Because $\alpha$-equivalence preserves free variables, we have $\freeLambdaVars(z_1) = \freeLambdaVars(z_2)$ and $\freeLambdaVars(\sigma_1(u)) = \freeLambdaVars(\sigma_2(u))$ for all $u \in \freeLambdaVars(z_1) \setminus \{x\}$. Then
$$\begin{eqnarray*}
 &   & \new(x,z_1,\sigma_1) \\
 & = & \{ y \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(z_1) \setminus \{x\}\ \mathrm{then}\ y \notin \freeLambdaVars(\sigma_1(u)) \} \\
 & = & \{ y \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(z_1) \setminus \{x\}\ \mathrm{then}\ y \notin \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \{ y \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(z_2) \setminus \{x\}\ \mathrm{then}\ y \notin \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \new(x,z_2,\sigma_2)
\end{eqnarray*}$$
as claimed.
:::::::::::::
:::::::::::::::::

If substitutions are equal on the free variables of an expression, then their applications to the expression are also equal (not merely $\alpha$-equivalent).

::: theorem :::
[@thm-eq-subs-eq-terms]() Let $z$ be a $\lambda$-term and $\sigma_1, \sigma_2$ substitutions. If $\sigma_1 =^{\freeLambdaVars(z)} \sigma_2$, then $\sigma_1[z] = \sigma_2[z]$.

::: proof :::
Note that this statement involves _equality_, not $\alpha$-equivalence. We proceed by structural induction on $z$.

1. Suppose $z \in \LambdaIdents$. Now $\freeLambdaVars(z) = \{z\}$, and using the hypothesis we have $$\sigma_1[z] = \sigma_1(z) = \sigma_2(z) = \sigma_2[z]$$ as claimed.

2. Suppose $z \in \LambdaConsts$; then $\sigma_1[z] = z = \sigma_2[z]$ as claimed.

3. Suppose $z = \lamex{x}{e}$. Now $\freeLambdaVars(z) = \freeLambdaVars(e) \setminus \{x\}$ and (using the hypothesis) $\sigma_{1, y/x}[e] =^{\freeLambdaVars(e) \setminus \{x\}} \sigma_{2, y/x}$. By reflexivity we have $e \AlphaEq e$. Now using the [previous result](@alpha-eq-to-new-sets), we have $\new(x,e,\sigma_1) = \new(x,e,\sigma_2)$. Using the inductive hypothesis we then have
    $$\begin{eqnarray*}
     &   & \sigma_1[z] \\
     & = & \sigma_1[\lamex{x}{e}] \\
     & = & \lamex{y}{\sigma_{1, y/x}[e]}\ \mathrm{where}\ y = \choice(\new(x,z,\sigma_1)) \\
     & = & \lamex{y}{\sigma_{2, y/x}[e]}\ \mathrm{where}\ y = \choice(\new(x,z,\sigma_2)) \\
     & = & \sigma_2[\lamex{x}{e}] \\
     & = & \sigma_2[z]
    \end{eqnarray*}$$
    as claimed.

4. Suppose $z = \letin{x}{e_1}{e_2}$. Now $\freeLambdaVars(z) = \freeLambdaVars(e_1) \cup (\freeLambdaVars(e_2) \setminus \{x\})$. Using the hypothesis, we have $\sigma_1 =^{\freeLambdaVars(e_1)} \sigma_2$ and $\sigma_{1, y/x} =^{\freeLambdaVars(e_2) \setminus \{x\}} \sigma_{2, y/x}$. By reflexivity we have $e_2 \AlphaEq e_2$, and using the [previous result](@alpha-eq-to-new-sets), we have $\new(x,e_2,\sigma_1) = \new(x,e_2,\sigma_2)$. Using the inductive hypothesis, we then have
    $$\begin{eqnarray*}
     &   & \sigma_1[z] \\
     & = & \sigma_1[\letin{x}{e_1}{e_2}] \\
     & = & \letin{y}{\sigma_1[e_1]}{\sigma_{1, y/x}[e_2]}\ \mathrm{where}\ y = \choice(\new(x,e_1,\sigma_1)) \\
     & = & \letin{y}{\sigma_2[e_1]}{\sigma_{2, y/x}[e_2]}\ \mathrm{where}\ y = \choice(\new(x,e_2,\sigma_2)) \\
     & = & \sigma_2[\letin{x}{e_1}{e_2}] \\
     & = & \sigma_2[z]
    \end{eqnarray*}$$
    as claimed.

5. Suppose $z = \apply{e_1}{e_2}$. Now $\freeLambdaVars(z) = \freeLambdaVars(e_1) \cup \freeLambdaVars(e_2)$, so that $\sigma_1 =^{\freeLambdaVars(e_1)} \sigma_2$ and $\sigma_1 =^{\freeLambdaVars(e_2)} \sigma_2$. Using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &   & \sigma_1[z] \\
     & = & \sigma_1[\apply{e_1}{e_2}] \\
     & = & \apply{\sigma_1[e_1]}{\sigma_1[e_2]} \\
     & = & \apply{\sigma_2[e_1]}{\sigma_2[e_2]} \\
     & = & \sigma_2[\apply{e_1}{e_2}] \\
     & = & \sigma_2[z]
    \end{eqnarray*}$$
    as claimed.
:::::::::::::
:::::::::::::::

Another result that seems obvious, but has to be proved: applying the identity substitution yields an $\alpha$-equivalent term.

::: theorem :::
[@thm-id-alpha-eq]() Given a $\lambda$-term $z$, we have $\mathsf{id}[z] \AlphaEq z$.

::: proof :::
We proceed by structural induction on $z$.

1. If $z \in \LambdaIdents$, then we have $$\mathsf{id}[z] = \mathsf{id}(z) = z \AlphaEq z$$ as claimed.

2. If $z \in \LambdaConsts$, then we have $\mathsf{id}[z] = z \AlphaEq z$ as claimed.

3. Suppose $z = \lamex{x}{e}$ and let $y = \choice(\new(x,e,\mathsf{id}))$. We claim that $y$ is not free in $e$; to see why, note that if so then from the definition of $\new$ we have $y \notin \freeLambdaVars(\mathsf{id}(y)) = \{y\}$. Then using a [previous lemma](@choice-id-alpha-eq-lemma) we have $\lamex{x}{e} \AlphaEq \lamex{y}{\mathsf{id}_{y/x}[e]}$. Then
    $$\begin{eqnarray*}
     &          & \mathsf{id}[z] \\
     & =        & \mathsf{id}[\lamex{x}{e}] \\
     & =        & \lamex{y}{\mathsf{id}_{y/x}[e]} \\
     & \AlphaEq & \lamex{x}{e} \\
     & =        & z
    \end{eqnarray*}$$
    as claimed.

4. Suppose $z = \letin{x}{e_1}{e_2}$ and let $y = \choice(\new(x,e,\mathsf{id}))$. As in the previous case, $y$ is not free in $e_2$, so that by a [previous lemma](@choice-id-alpha-eq-lemma) we have $\lamex{x}{e} \AlphaEq \lamex{y}{\mathsf{id}_{y/x}[e_2]}$. Using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &          & \mathsf{id}[z] \\
     & =        & \mathsf{id}[\letin{x}{e_1}{e_2}] \\
     & =        & \letin{y}{\mathsf{id}[e_1]}{\mathsf{id}_{y/x}[e_2]} \\
     & \AlphaEq & \letin{y}{e_1}{\mathsf{id}_{y/x}[e_2]} \\
     & \AlphaEq & \letin{x}{e_1}{e_2} \\
     & =        & z
    \end{eqnarray*}$$
    so that $\mathsf{id}[z] \AlphaEq z$ by transitivity.

5. Suppose $z = \apply{e_1}{e_2}$. Using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &          & \mathsf{id}[z] \\
     & =        & \mathsf{id}[\apply{e_1}{e_2}] \\
     & =        & \apply{\mathsf{id}[e_1]}{\mathsf{id}[e_2]} \\
     & \AlphaEq & \apply{e_1}{e_2} \\
     & =        & z
    \end{eqnarray*}$$
    as claimed.
:::::::::::::
:::::::::::::::

This theorem is another good candidate for property testing.

> prop_identity_subst_alpha_eq
>   :: forall a. (Show a)
>   => LambdaTerm a -> Bool
> prop_identity_subst_alpha_eq z =
>   alphaEqTerm z (applySubToLambdaTerm identitySub z)

We can say something very strong about the sets of new variables for expressions which satisfy the hypotheses from the definition of $\alpha$-equivalence.

::: theorem :::
[@lemma-alpha-eq-new-sets-equal]() We have the following.

1. If $\mathcal{A}(e,x,f,y)$, then $\new(x,e,\sigma) = \new(y,f,\sigma)$.
2. If $\mathcal{B}(e_1,e_2,x,f_1,f_2,y)$, then $\new(x,e_2,\sigma) = \new(y,f_2,\sigma)$.

::: proof :::
First we show (1). Recall that $\mathcal{A}(e,x,f,y)$ is shorthand for the hypothesis on lambda expressions in the definition of $\AlphaEq$. Suppose it is true; we consider two cases.

1. Suppose $x = y$ and $e \AlphaEq f$. Using a [previous result](@thm-alpha-eq-free-vars), we have $\freeLambdaVars(e) = \freeLambdaVars(f)$. Now
    $$\begin{eqnarray*}
     &   & \new(x,e,\sigma) \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(f) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \new(y,f,\sigma)
    \end{eqnarray*}$$
    as claimed.

2. Suppose $y \notin \freeLambdaVars(e)$ and $\mathsf{id}_{y/x}[e] \AlphaEq f$. We've [seen](@thm-alpha-eq-free-vars) that $\freeLambdaVars(\mathsf{id}_{y/x}[e]) = \freeLambdaVars(f)$. Using another [previous result](@free-vars-pointwise-update), we also have $$\freeLambdaVars(\mathsf{id}_{y/x}[e]) = (\freeLambdaVars(e) \setminus \{x\}) \cup \left\{ \begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(e) \\ \varnothing & \mathrm{otherwise}. \end{array} \right.$$ In particular, we have $$\freeLambdaVars(f) \setminus \{y\} = (\freeLambdaVars(e) \setminus \{x\}) \setminus \{y\} = \freeLambdaVars(e) \setminus \{x\}.$$ Then
    $$\begin{eqnarray*}
     &   & \new(x,e,\sigma) \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(f) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \new(y,f,\sigma)
    \end{eqnarray*}$$
    as claimed.

Next we show (2). Recall that $\mathcal{B}(e_1,e_2,x,f_1,f_2,y)$ is shorthand for the hypothesis on let expressions in the definition of $\AlphaEq$. Suppose it is true; we consider two cases.

1. Suppose $x = y$, $e_1 \AlphaEq f_1$, and $e_2 \AlphaEq f_2$. Using a [previous result](@thm-alpha-eq-free-vars) we have $\freeLambdaVars(e_2) = \freeLambdaVars(f_2)$, so that
    $$\begin{eqnarray*}
     &   & \new(x,e_2,\sigma) \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(e_2) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(f_2) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \new(y,f_2,\sigma)
    \end{eqnarray*}$$
    as claimed.

2. Suppose $y \notin \freeLambdaVars(e_2)$, $e_1 \AlphaEq f_1$, and $\mathsf{id}_{y/x}[e_2] \AlphaEq f_2$. We've [seen](@thm-alpha-eq-free-vars) that $\freeLambdaVars(\mathsf{id}_{y/x}[e_2]) = \freeLambdaVars(f)$. Using another [previous result](@free-vars-pointwise-update), we also have $$\freeLambdaVars(\mathsf{id}_{y/x}[e_2]) = (\freeLambdaVars(e_2) \setminus \{x\}) \cup \left\{ \begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(e_2) \\ \varnothing & \mathrm{otherwise}. \end{array} \right.$$ In particular, we have $$\freeLambdaVars(f) \setminus \{y\} = (\freeLambdaVars(e_2) \setminus \{x\}) \setminus \{y\} = \freeLambdaVars(e_2) \setminus \{x\}.$$ Then
    $$\begin{eqnarray*}
     &   & \new(x,e_2,\sigma) \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(e_2) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(f_2) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma(u)) \} \\
     & = & \new(y,f_2,\sigma)
    \end{eqnarray*}$$
    as claimed.
:::::::::::::
:::::::::::::::

We can also say something about how new variables and the composition of substitutions interact.

::: theorem :::
[@thm-new-set-eq]() If $y \in \new(x,e,\sigma_1)$, then $\new(x,e,\sigma_2\sigma_1) = \new(y,\sigma_{1,y/x}[e],\sigma_2)$.

::: proof :::
Note that since $y \in \new(x,e,\sigma_1)$, if $u \in \freeLambdaVars(e) \setminus \{x\}$, then $y \notin \freeLambdaVars(\sigma_1(u))$, and thus $\freeLambdaVars(\sigma_1(u)) \setminus \{y\} = \freeLambdaVars(\sigma_1(u))$. then
$$\begin{eqnarray*}
 &   & \new(y, \sigma_{1, y/x}[e], \sigma_2) \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \freeLambdaVars(\sigma_{1, y/x}[e]) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \left\{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \left( \bigcup_{k \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma_1(k)) \cup \left\{ \begin{array}{ll} \{y\} & \mathrm{if}\ x \in \freeLambdaVars(e) \\ \varnothing & \mathrm{otherwise} \end{array} \right\} \right) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2(u)) \right\} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \left( \bigcup_{k \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma_1(k)) \right) \setminus \{y\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ u \in \bigcup_{k \in \freeLambdaVars(e) \setminus \{x\}} \freeLambdaVars(\sigma_1(k))\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ k \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ \left(\mathrm{if}\ u \in \freeLambdaVars(\sigma_1(k))\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2(u)) \right) \} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ k \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ t \notin \bigcup_{u \in \freeLambdaVars(\sigma_1(k))} \freeLambdaVars(\sigma_2(u)) \} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ k \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars(\sigma_2[\sigma_1(k)]) \} \\
 & = & \{ t \in \LambdaIdents \mid \mathrm{if}\ k \in \freeLambdaVars(e) \setminus \{x\}\ \mathrm{then}\ t \notin \freeLambdaVars((\sigma_2\sigma_1)(k)) \} \\
 & = & \new(x, e, \sigma_2\sigma_1)
\end{eqnarray*}$$
as claimed.
:::::::::::::
:::::::::::::::

Pointwise updates of the identity substitution on variables that are not free also yields alpha-equivalent terms.

::: lemma :::
If $x \notin \freeLambdaVars(z)$, then $\mathsf{id}_{e/x}[z] \AlphaEq z$.

::: proof :::
Note that $\mathsf{id}_{e/x} =^{\freeLambdaVars(z)} \mathsf{id}$, and so by a [previous result](@thm-eq-subs-eq-terms) we have $\mathsf{id}_{e/x}[z] = \mathsf{id}[e]$. We've [also shown](@thm-id-alpha-eq) that $\mathsf{id}[z] \AlphaEq z$, and so $\mathsf{id}_{e/x}[z] \AlphaEq z$ as claimed.
:::::::::::::
:::::::::::::

Next we show that composition of substitutions is compatible with simultaneous substitution.

::: theorem :::
[@thm-syntactic-sub]() (Syntactic Substitution.) For all terms $z$ and substitutions $\sigma_1$ and $\sigma_2$, we have $(\sigma_2\sigma_1)[z] = \sigma_2[\sigma_1[z]]$.

::: proof :::
We proceed by structural induction on $z$.

1. Suppose $z \in \LambdaIdents$. Then
    $$\begin{eqnarray*}
     &   & (\sigma_2\sigma_1)[z] \\
     & = & \sigma_2[\sigma_1(z)] \\
     & = & \sigma_2[\sigma_1[z]]
    \end{eqnarray*}$$
    as claimed.

2. Suppose $z \in \LambdaConsts$. Then
    $$\begin{eqnarray*}
     &   & (\sigma_2\sigma_1)[z] \\
     & = & z \\
     & = & \sigma_2[z] \\
     & = & \sigma_2[\sigma_1[z]]
    \end{eqnarray*}$$
    as claimed.

3. Suppose $z = \lamex{x}{e}$. Using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &   & \sigma_2[\sigma_1[z]] \\
     & = & \sigma_2[\sigma_1[\lamex{x}{e}]] \\
     & = & \sigma_2[\lamex{y}{\sigma_{1,y/x}[e]}] \\
     & = & \lamex{u}{\sigma_{2,u/y}[\sigma_{1,y/x}[e]]} \\
     & = & \lamex{u}{(\sigma_{2,u/y}\sigma_{1,y/x})[e]}
    \end{eqnarray*}$$
    where $y = \choice(\new(x,e,\sigma_1))$ and $u = \choice(\new(y,\sigma_{1,y/x}[e],\sigma_2))$, and we also have
    $$\begin{eqnarray*}
     &   & (\sigma_2\sigma_1)[z] \\
     & = & (\sigma_2\sigma_1)[\lamex{x}{e}] \\
     & = & \lamex{v}{(\sigma_2\sigma_1)_{v/x}[e]}
    \end{eqnarray*}$$
    where $v = \choice(\new(x,e,\sigma_2\sigma_1))$. Using the [previous result](@thm-new-set-eq), we have $\new(x,e,\sigma_2\sigma_1) = \new(y,\sigma_{1,y/x}[e],\sigma_2)$, and thus $u = v$. Now note that if $t \in \freeLambdaVars(e) \setminus \{x\}$, then $y \notin \freeLambdaVars(\sigma_1(t))$ (from the definition of $\new$) and in particular, for such $t$ we have $\sigma_{2,v/y} =^{\freeLambdaVars(\sigma_1(t))} \sigma_2$. Using a [previous result](@thm-eq-subs-eq-terms) we have $\sigma_{2,v/y}[\sigma_1(t)] = \sigma_2[\sigma_1(t)]$. Now note that for any variable $t \in \freeLambdaVars(e)$, we have
    $$\begin{eqnarray*}
     &   & (\sigma_{2,v/y}\sigma_{1,y/x})(t) \\
     & = & \sigma_{2,v/y}[\sigma_{1,y/x}(t)] \\
     & = & \sigma_{2,v/y}\left[ \left\{\begin{array}{ll} y & \mathrm{if}\ t = x \\ \sigma_1(t) & \mathrm{otherwise} \end{array}\right. \right] \\
     & = & \left\{\begin{array}{ll} \sigma_{2,v/y}[y] & \mathrm{if}\ t = x \\ \sigma_{2,v/y}[\sigma_1(t)] & \mathrm{otherwise} \end{array}\right. \\
     & = & \left\{\begin{array}{ll} \sigma_{2,v/y}(y) & \mathrm{if}\ t = x \\ \sigma_2[\sigma_1(t)] & \mathrm{otherwise} \end{array}\right. \\
     & = & \left\{\begin{array}{ll} v & \mathrm{if}\ t = x \\ \sigma_2[\sigma_1(t)] & \mathrm{otherwise} \end{array}\right. \\
     & = & \left\{\begin{array}{ll} v & \mathrm{if}\ t = x \\ (\sigma_2\sigma_1)(t) & \mathrm{otherwise} \end{array}\right. \\
     & = & (\sigma_2\sigma_1)_{v/x}(t).
    \end{eqnarray*}$$
    That is, we have $\sigma_{2,v/y}\sigma_{1,y/x} =^{\freeLambdaVars(e)} (\sigma_2\sigma_1)_{v/x}$. Using the [previous result](@thm-eq-subs-eq-terms) again we then have $(\sigma_{2,v/y}\sigma_{1,y/x})[e] = (\sigma_2\sigma_1)_{v/x}[e]$. Putting it all together, we have
    $$\begin{eqnarray*}
     &   & \sigma_2[\sigma_1[z]] \\
     & = & \lamex{u}{(\sigma_{2,u/y}\sigma_{1,y/x})[e]} \\
     & = & \lamex{v}{(\sigma_{2,v/y}\sigma_{1,y/x})[e]} \\
     & = & \lamex{v}{(\sigma_2\sigma_1)_{v/x}[e]} \\
     & = & (\sigma_2\sigma_1)[z]
    \end{eqnarray*}$$
    as claimed.

4. Suppose $z = \letin{x}{e_1}{e_2}$. Much like the $\lambda$ case, using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &   & \sigma_2[\sigma_1[z]] \\
     & = & \sigma_2[\sigma_1[\letin{x}{e_1}{e_2}]] \\
     & = & \sigma_2[\letin{y}{\sigma_1[e_1]}{\sigma_{1,y/x}[e_2]}] \\
     & = & \letin{u}{\sigma_2[\sigma_1[e_1]]}{\sigma_{2,u/y}[\sigma_{1,y/x}[e_2]]} \\
     & = & \letin{u}{\sigma_2[\sigma_1[e_1]]}{(\sigma_{2,u/y}\sigma_{1,y/x})[e_2]}
    \end{eqnarray*}$$
    where $y = \choice(\new(x,e_2,\sigma_1))$ and $u = \choice(\new(y,\sigma_{1,y/x}[e_2]),\sigma_2)$, and we also have
    $$\begin{eqnarray*}
     &   & (\sigma_2\sigma_1)[z] \\
     & = & (\sigma_2\sigma_1)[\letin{x}{e_1}{e_2}] \\
     & = & \letin{v}{(\sigma_2\sigma_1)[e_1]}{(\sigma_2\sigma_1)_{v/x}[e_2]}
    \end{eqnarray*}$$
    where $v = \choice(\new(x,e_2,\sigma_2\sigma_1))$. As with the $\lambda$ case, by [previous result](@thm-new-set-eq), we have $\new(x,e_2,\sigma_2\sigma_1) = \new(y,\sigma_{1,y/x}[e_2],\sigma_2)$, and thus $u = v$. Following that argument further we have $\sigma_{2,v/y}[\sigma_1(t)] = \sigma_2[\sigma_1[t]]$ for all $t \in \freeLambdaVars(e_2) \setminus \{x\}$, and then $(\sigma_{2,v/y}\sigma_{1,y/x})(t) = (\sigma_2\sigma_1)_{v/x}(t)$ for all $t \in \freeLambdaVars(e_2)$. Thus $\sigma_{2,v/y}\sigma_{1,y/x} =^{\freeLambdaVars(e_2)} (\sigma_2\sigma_1)_{v/x}$, and so $(\sigma_{2,v/y}\sigma_{1,y/x})[e_2] = (\sigma_2\sigma_1)_{v/x}[e_2]$. Then using the inductive hypothesis we have
    $$\begin{eqnarray*}
     &   & \sigma_2[\sigma_1[z]] \\
     & = & \letin{u}{\sigma_2[\sigma_1[e_1]]}{(\sigma_{2,u/y}\sigma_{1,y/x})[e_2]} \\
     & = & \letin{v}{\sigma_2[\sigma_1[e_1]]}{(\sigma_{2,v/y}\sigma_{1,y/x})[e_2]} \\
     & = & \letin{v}{\sigma_2[\sigma_1[e_1]]}{(\sigma_2\sigma_1)_{v/x}[e_2]} \\
     & = & \letin{v}{(\sigma_2\sigma_1)[e_1]}{(\sigma_2\sigma_1)_{v/x}[e_2]} \\
     & = & (\sigma_2\sigma_1)[z]
    \end{eqnarray*}$$
    as claimed.

5. Suppose $z = \apply{e_1}{e_2}$. Then
    $$\begin{eqnarray*}
     &   & (\sigma_2\sigma_1)[z] \\
     & = & (\sigma_2\sigma_1)[\apply{e_1}{e_2}] \\
     & = & \apply{(\sigma_2\sigma_1)[e_1]}{(\sigma_2\sigma_1)[e_2]} \\
     & = & \apply{\sigma_2[\sigma_1[e_1]]}{\sigma_2[\sigma_1[e_2]]} \\
     & = & \sigma_2[\apply{\sigma_1[e_1]}{\sigma_1[e_2]}] \\
     & = & \sigma_2[\sigma_1[\apply{e_1}{e_2}]] \\
     & = & \sigma_2[\sigma_1[z]]
    \end{eqnarray*}$$
    as claimed.
:::::::::::::
:::::::::::::::

This theorem is a great candidate for property testing; it is unqualified and states a simple equality of two expressions, but it conceals a lot of implementation details.

> prop_lambda_sub_action
>   :: forall a
>    . (Show a)
>   => LambdaTerm a
>   -> M.Map LambdaVariable (LambdaTerm a)
>   -> M.Map LambdaVariable (LambdaTerm a)
>   -> Property
> prop_lambda_sub_action z sigma1 sigma2 = (===)
>   (applySubToLambdaTerm (composeLambdaSubs sigma2 sigma1) z)
>   (applySubToLambdaTerm sigma2 (applySubToLambdaTerm sigma1 z))

The Syntactic Substitution theorem states that substitution is compatible with composition.

::: corollary :::
[@lemma-sub-id-collapse]() If $y \notin \freeLambdaVars(z)$ then $\sigma_{w/y}[\mathsf{id}_{y/x}[z]] = \sigma_{w/x}[z]$.

::: proof :::
If $t \in \freeLambdaVars(z)$, then $y \neq t$, and we have
$$\begin{eqnarray*}
 &   & (\sigma_{w/y}\mathsf{id}_{y/x})(t) \\
 & = & \sigma_{w/y}[\mathsf{id}_{y/x}(t)] \\
 & = & \sigma_{w/y}\left[ \left\{ \begin{array}{ll} y & \mathrm{if}\ t = x \\ t & \mathrm{otherwise} \end{array} \right. \right] \\
 & = & \left\{\begin{array}{ll} \sigma_{w/y}[y] & \mathrm{if}\ t = x \\ \sigma[t] & \mathrm{otherwise} \end{array}\right. \\
 & = & \left\{\begin{array}{ll} \sigma_{w/y}(y) & \mathrm{if}\ t = x \\ \sigma(t) & \mathrm{otherwise} \end{array}\right. \\
 & = & \left\{\begin{array}{ll} w & \mathrm{if}\ t = x \\ \sigma(t) & \mathrm{otherwise} \end{array}\right. \\
 & = & \sigma_{w/x}[t] \\
 & = & \sigma_{w/x}(t).
\end{eqnarray*}$$
That is, $\sigma_{w/y}\mathsf{id}_{y/x} =^{\freeLambdaVars(z)} \sigma_{w/x}$. Using a [previous result](@thm-eq-subs-eq-terms) as well as the [Syntactic Substitution](@thm-syntactic-sub) theorem we have
$$\begin{eqnarray*}
 &   & \sigma_{w/y}[\mathsf{id}_{y/x}[z]] \\
 & = & (\sigma_{w/y}\mathsf{id}_{y/x})[z] \\
 & = & \sigma_{w/x}[z]
\end{eqnarray*}$$
as claimed.
:::::::::::::
:::::::::::::::

It looks a lot like we have a monoid or semigroup action here; to nail that down we need to show that composition of substitutions forms a monoid or semigroup.

::: corollary :::
We have the following for substitutions $\sigma_i$.

1. $\sigma\ \mathsf{id} = \sigma$.
2. $\mathsf{id}\ \sigma \AlphaEq \sigma$.
3. $\sigma_3(\sigma_2\sigma_1) = (\sigma_3\sigma_2)\sigma_1$.

::: proof :::
1. Note that for all identifiers $t$, we have
    $$\begin{eqnarray*}
     &   & (\sigma\ \mathsf{id})(t) \\
     & = & \sigma[\mathsf{id}(t)] \\
     & = & \sigma[t] \\
     & = & \sigma(t)
    \end{eqnarray*}$$
    as needed.

2. Let $t$ be an identifier. Using a [previous result](@thm-id-alpha-eq) we have
    $$\begin{eqnarray*}
     &          & (\mathsf{id}\ \sigma)(t) \\
     & =        & \mathsf{id}[\sigma(t)] \\
     & \AlphaEq & \sigma(t)
    \end{eqnarray*}$$
    as needed.

3. Let $t$ be an identifier. Then using the [Syntactic Substitution](@thm-syntactic-sub) theorem we have
    $$\begin{eqnarray*}
     &   & (\sigma_3(\sigma_2\sigma_1))(t) \\
     & = & \sigma_3[(\sigma_2\sigma_1)(t)] \\
     & = & \sigma_3[\sigma_2[\sigma_1(t)]] \\
     & = & (\sigma_3\sigma_2)[\sigma_1(t)] \\
     & = & ((\sigma_3\sigma_2)\sigma_1)(t)
    \end{eqnarray*}$$
    as needed.
:::::::::::::
:::::::::::::::::

These properties are also amenable to property testing.

> prop_lambda_sub_composite_right_identity
>   :: forall a
>    . (Show a)
>   => M.Map LambdaVariable (LambdaTerm a)
>   -> Property
> prop_lambda_sub_composite_right_identity sigma = (===)
>   (composeLambdaSubs sigma identitySub) sigma
> 
> prop_lambda_sub_composite_left_identity
>   :: forall a
>    . (Show a)
>   => M.Map LambdaVariable (LambdaTerm a)
>   -> Bool
> prop_lambda_sub_composite_left_identity sigma = alphaEqSub
>   (composeLambdaSubs identitySub sigma) sigma
> 
> prop_lambda_sub_composite_associative
>   :: forall a
>    . (Show a)
>   => M.Map LambdaVariable (LambdaTerm a)
>   -> M.Map LambdaVariable (LambdaTerm a)
>   -> M.Map LambdaVariable (LambdaTerm a)
>   -> Property
> prop_lambda_sub_composite_associative sigma1 sigma2 sigma3 = (===)
>   (composeLambdaSubs sigma3 (composeLambdaSubs sigma2 sigma1))
>   (composeLambdaSubs (composeLambdaSubs sigma3 sigma2) sigma1)

Summarizing a few results, we have the following.

::: corollary :::
Let $\cdot$ denote substitution composition.

1. $(\LambdaSubstitutions, \cdot)$ is a semigroup.
2. $(\LambdaSubstitutions/\AlphaEq, \cdot, \mathsf{id})$ is a monoid.

Both of these structures act on $\LambdaTerms$ from the left by simultaneous substitution.
:::::::::::::::::

We're now prepared to show that simultaneous substitution is compatible with $\alpha$-equivalence. In fact the situation is stronger than that; applying a substitution to $\alpha$-equivalent terms yields _syntactically equal_ results.

::: theorem :::
If $z \AlphaEq w$, then $\sigma[z] = \sigma[w]$.

::: proof :::
We will follow a strategy similar to our proof that alpha equivalent terms have the same free variables. Define a relation $\sim$ on $\LambdaTerms$ by $z \sim w$ if and only if $z \AlphaEq w$ and $\sigma[z] = \sigma[w]$ for all substitutions $\sigma$. This $\sim$ is clearly an equivalence. We will show that it also satisfies the defining properties of $\AlphaEq$, so that $\AlphaEq$ is contained in $\sim$. Since $\sim$ is contained in $\AlphaEq$ by definition, the conclusion follows.

Suppose $z = \lamex{x}{e}$ and $w = \lamex{y}{f}$ with $\mathcal{A}(e,x,f,y)$, and let $\sigma$ be a substitution. We showed [previously](@lemma-alpha-eq-new-sets-equal) that $\new(x,e,\sigma) = \new(y,f,\sigma)$, and so letting $u = \choice(\new(x,e,\sigma))$ we have $$\sigma[z] = \sigma[\lamex{x}{e}] = \lamex{u}{\sigma_{u/x}[e]}$$ and $$\sigma[w] = \sigma[\lamex{y}{f}] = \lamex{u}{\sigma_{u,y}[f]}.$$ We consider two cases.

1. Suppose $x = y$ and $e \sim f$. Then using the inductive hypothesis we have $$\sigma_{u/x}[e] = \sigma_{u/x}[f] = \sigma_{u/y}[f]$$ and thus $$\sigma[z] = \lamex{u}{\sigma_{u/x}[e]} = \lamex{u}{\sigma_{u/y}[f]} = \sigma[w].$$ Since $\sigma$ was arbitrary, we have $z \sim w$ as claimed.

2. Suppose $y \notin \freeLambdaVars(e)$ and $\mathsf{id}_{y/x}[e] \sim f$. Using a [previous result](@lemma-sub-id-collapse) we have $$\sigma_{u/x}[e] = \sigma_{u/y}[\mathsf{id}_{y/x}[e]] = \sigma_{u/y}[f]$$ and thus $$\sigma[z] = \lamex{u}{\sigma_{u/x}[e]} = \lamex{u}{\sigma_{u/y}[f]} = \sigma[w].$$ Since $\sigma$ was arbitrary, we have $z \sim w$ as claimed.

Suppose $z = \letin{x}{e_1}{e_2}$ and $w = \letin{y}{f_1}{f_2}$ with $\mathcal{B}(e_1,e_2,x,f_1,f_2,y)$, and let $\sigma$ be a substitution. We showed [previously](@lemma-alpha-eq-new-sets-equal) that $\new(x,e_2,\sigma) = \new(y,f_2,\sigma)$, and so letting $u = \choice(\new(x,e,\sigma_2))$ we have
$$\begin{eqnarray*}
 &   & \sigma[z] \\
 & = & \sigma[\letin{x}{e_1}{e_2}] \\
 & = & \letin{u}{\sigma[e_1]}{\sigma_{u/x}[e_2]}
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \sigma[w] \\
 & = & \sigma[\letin{y}{f_1}{f_2}] \\
 & = & \letin{u}{\sigma[f_1]}{\sigma_{u/y}[f_2]}.
\end{eqnarray*}$$
We consider two cases.

1. Suppose $x = y$, $e_2 \sim f_2$, and $e_1 \sim f_1$. Then $e_1 \AlphaEq f_1$ and $e_2 \AlphaEq f_2$. Using the inductive hypothesis we have $$\sigma_{u/x}[e_2] = \sigma_{u/x}[f_2] = \sigma_{u/y}[f_2]$$ and thus
    $$\begin{eqnarray*}
     &   & \sigma[z] \\
     & = & \letin{u}{\sigma[e_1]}{\sigma_{u/x}[e_2]} \\
     & = & \letin{u}{\sigma[f_1]}{\sigma_{u/y}[f_2]} \\
     & = & \sigma[w].
    \end{eqnarray*}$$
    Since $\sigma$ was arbitrary we have $z \sim w$ as claimed.

2. Suppose $y \notin \freeLambdaVars(e_2)$, $\mathsf{id}_{y/x}[e_2] \sim f_2$, and $e_1 \sim f_1$. Using a [previous result](@lemma-sub-id-collapse) we have $$\sigma_{u/x}[e_2] = \sigma_{u/y}[\mathsf{id}_{y/x}[e_2]] = \sigma_{u/y}[f_2]$$ and thus
    $$\begin{eqnarray*}
     &   & \sigma[z] \\
     & = & \letin{u}{\sigma[e_1]}{\sigma_{u/x}[e_2]} \\
     & = & \letin{u}{\sigma[f_1]}{\sigma_{u/y}[f_2]} \\
     & = & \sigma[w].
    \end{eqnarray*}$$
    Since $\sigma$ was arbitrary, we have $z \sim w$ as claimed.

Suppose $z = \apply{e_1}{e_2}$ and $w = \apply{f_1}{f_2}$, and let $\sigma$ be a substitution. Since $z \AlphaEq w$ we have $e_1 \AlphaEq f_1$ and $e_2 \AlphaEq f_2$. Using the inductive hypothesis we then have $\sigma[e_1] = \sigma[f_1]$ and $\sigma[e_2] = \sigma[f_2]$, so that
$$\begin{eqnarray*}
 &   & \sigma[z] \\
 & = & \sigma[\apply{e_1}{e_2}] \\
 & = & \apply{\sigma[e_1]}{\sigma[e_2]} \\
 & = & \apply{\sigma[f_1]}{\sigma[f_2]} \\
 & = & \sigma[\apply{f_1}{f_2}] \\
 & = & \sigma[w].
\end{eqnarray*}$$
Since $\sigma$ was arbitrary we have $z \sim w$ as claimed.
:::::::::::::
:::::::::::::::

This finally gives us a computable strategy for detecting when two terms are $\alpha$-equivalent; apply the identity substitution to both and see if the results are _syntactically_ equal.

::: corollary :::
We have the following.

1. $z \AlphaEq w$ if and only if $\mathsf{id}[z] = \mathsf{id}[w]$.
2. $\sigma_1 \AlphaEq^{A} \sigma_2$ if and only if $\mathsf{id}\ \sigma_1 =^{A} \mathsf{id}\ \sigma_2$.

::: proof :::
1. If $z \AlphaEq w$, then $\mathsf{id}[z] = \mathsf{id}[w]$ by the previous theorem. If $\mathsf{id}[z] = \mathsf{id}[w]$, then using a [previous result](@thm-id-alpha-eq) we have $$z \AlphaEq \mathsf{id}[z] = \mathsf{id}[w] \AlphaEq w$$ as claimed.

2. Follows from (1).
:::::::::::::
:::::::::::::::::

We can translate this theorem to a Haskell function for detecting $\alpha$-equivalence.

> alphaEqTerm
>   :: LambdaTerm a -> LambdaTerm a -> Bool
> alphaEqTerm z w = (==)
>   (applySubToLambdaTerm identitySub z)
>   (applySubToLambdaTerm identitySub w)
> 
> alphaEqSub
>   :: M.Map LambdaVariable (LambdaTerm a) -> M.Map LambdaVariable (LambdaTerm a) -> Bool
> alphaEqSub sigma1 sigma2 = (==)
>   (M.map (applySubToLambdaTerm identitySub) sigma1)
>   (M.map (applySubToLambdaTerm identitySub) sigma2)

With an actual implementation of $\alpha$-equivalence in hand, we can write tests for the properties which use it. For instance we can check that it's an equivalence relation.

> prop_alpha_eq_reflexive
>   :: forall a. (Show a)
>   => LambdaTerm a -> Bool
> prop_alpha_eq_reflexive z = alphaEqTerm z z
> 
> prop_alpha_eq_symmetric
>   :: forall a. (Show a)
>   => LambdaTerm a -> LambdaTerm a -> Property
> prop_alpha_eq_symmetric z1 z2 = (===)
>   (alphaEqTerm z1 z2)
>   (alphaEqTerm z2 z1)
> 
> prop_alpha_eq_transitive
>   :: forall a. (Show a)
>   => LambdaTerm a -> LambdaTerm a -> LambdaTerm a -> Property
> prop_alpha_eq_transitive z1 z2 z3 =
>   if (alphaEqTerm z1 z2) && (alphaEqTerm z2 z3)
>     then alphaEqTerm z1 z3 === True
>     else property succeeded
