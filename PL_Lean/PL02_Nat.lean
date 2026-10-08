/-

# Natural numbers and recursive programming

This file is both a lecture and a Lean program.  Read the comments from top to
bottom, but also place the cursor on each command and inspect Lean's Infoview.
You are encouraged to change expressions, introduce mistakes, and observe
Lean's responses.

In the previous lecture we learned how to:
* inspect and evaluate Lean expressions;
* define constants and pure functions;
* use `Bool`, conditional expressions, and pattern matching;
* use functions as values;
* state simple properties and prove them with basic tactics.

In this lecture we use all of these ideas again, now on the *natural numbers*.
Natural numbers are our first example of an inductive type with infinitely many
values.  They are the simplest place to see how *data*, *recursive functions*,
and *proofs by induction* fit together.

We will learn how to:
* inspect the inductive type `Nat` and its two constructors;
* define functions on `Nat` by pattern matching;
* define recursive functions;
* write arithmetic functions: addition, multiplication, powers, factorial,
  comparison, and subtraction;
* prove simple properties of our programs, exploring new tactics.

-/

set_option autoImplicit false


section Reading_this_file

/-
## How to read this file

As in the previous lecture, comments explain the ideas while the declarations
below them are actual Lean code.

Remember the three commands that are especially useful while learning:

* `#check e` asks Lean for the type of `e`;
* `#eval e` evaluates `e` when Lean can compute its value;
* `#print name` displays a declaration.

We will use all three again below.  We will also use `example`, which states a
fact and asks Lean to check it, without giving the fact a name.

### How the exercises work

Exercises are marked with the word `Exercise`.  In most of them you replace the
placeholder `sorry` with your own solution.  The word `sorry` means "I promise
to fill this in later": Lean accepts it, but shows a warning.

Many programming exercises are followed by a few *tests*, written like this:

    example : tripleN 4 = 12 := by rfl

A test is silent when it passes and shows an error when it fails.  So when you
open this file for the first time, the tests of the exercises are red: this is
expected!  Your goal is to make them silent.  You can always use `#eval` to
experiment while you work.

-/

end Reading_this_file


namespace MyNat

/-
## Natural numbers

Natural numbers are the numbers

    0, 1, 2, 3, ...

In Lean they form the *inductive type* `Nat`.
Here we redefine `Nat` in a new namespace, in order to
avoid conflicts with Lean's native type `Nat`.
-/

inductive Nat where
  | zero : Nat          --- axiom: zero is a Nat
  | succ : Nat -> Nat   --- inference rule: if n is a Nat, then succ n is a Nat

#eval Nat.zero
#eval Nat.succ Nat.zero
#eval Nat.succ (Nat.succ Nat.zero)

/-
An inductive type is defined by listing its *constructors*: the only ways of
building a value of that type.  Conceptually, the constructors of `Nat` are:

* `Nat.zero`, which constructs zero;
* `Nat.succ n`, which constructs the successor of a natural number `n`.

As inference rules, we would write these constructors as:

                  n
--------      ----------
Nat.zero      Nat.succ n

Using these inference rules, we can derive that 3 is in Nat as follows:

--------
Nat.zero
------------------
Nat.succ Nat.zero
-----------------------------
Nat.succ (Nat.succ Nat.zero)
---------------------------------------
Nat.succ (Nat.succ (Nat.succ Nat.zero))

Thus:

    0       = Nat.zero
    1       = Nat.succ Nat.zero
    2       = Nat.succ (Nat.succ Nat.zero)
    3       = Nat.succ (Nat.succ (Nat.succ Nat.zero))

Numerals such as `0`, `1`, `2`, ... are just notation for natural-number values.
The important idea is not the notation itself, but the inductive structure:
starting from zero, every natural number is obtained by repeatedly taking a
successor.

This structure will guide both our programs and our proofs.

-/

end MyNat


/-
We now switch back to Lean's native type `Nat`. So, from now on we can use
pretty-printing and all the standard operators on `Nat` defined in the Lean library.
-/

section Natural_numbers

#check Nat            --- also types have types!
#check Nat.zero
#check Nat.succ

#check (7 : Nat)      --- Lean implicitly converts 7 into a Nat
#eval (7 : Nat)

#print Nat            --- built-in Nat have the same structure of MyNat.Nat

/-
For example, `Nat.succ 4` is the natural number 5.
-/

#eval Nat.succ 4

/-
The constructor `Nat.succ` is itself a function in Nat → Nat.
Its type says that, given a natural number, it produces another natural number:
-/

#check Nat.succ

/-
This is our first important example of an inductive type with a constructor
that has an argument.

Compare it with `Bool` from the previous lecture:

    Bool  has two constructors, `true` and `false`.
    Nat   has two constructors, `zero` and `succ`.

The difference is that `succ` carries another natural number with it.
That makes `Nat` *infinite*: from every natural number we can construct another
one by taking its successor.

-/

/-
### Some syntactic sugar

Writing `Nat.succ n` is precise but heavy.  Lean also lets us write `n + 1` for
the successor of `n`.  The two expressions denote exactly the same number, and Lean
prefers to *print* `n + 1`: you will see it in the Infoview.

The following facts hold by plain computation, so `rfl` proves them.
-/

example : 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by rfl

example (n : Nat) : Nat.succ n = n + 1 := by rfl

/-
__Exercise__: Note that `rfl` is not powerful enough to prove apparently
obvious equivalences, like e.g. `n + 1 = 1 + n`. Replace `sorry` with
`rfl` and check whether the goal is solved.
-/
example (n : Nat) : Nat.succ n = 1 + n := by sorry


/-
### Built-in arithmetic operators

Lean already knows the usual operations on natural numbers.
-/

#eval 7 + 5
#eval 6 * 7
#eval 17 / 5       -- integer division
#eval 17 % 5       -- remainder
#eval 2 ^ 10       -- power
#eval 2 ^ 100      -- no overflow: unlike `int` in C or Java, `Nat` is unbounded

/-
Subtraction deserves a warning.  There are no negative natural numbers, so
subtraction stops at zero:
-/

#eval 7 - 5
#eval 5 - 7

/-
In this lecture we will deliberately re-implement addition, multiplication, and
so on from scratch (`addN`, `mulN`, ...).  The goal is to learn how recursive
functions on inductive data work, and later to prove things about them.  In real
programs you should of course use the built-in operations, which are much faster.

-/

end Natural_numbers


section Pattern_matching_on_Nat

/-
## Pattern matching on natural numbers

We define the predecessor function by pattern matching:
* the predecessor of zero is zero,
* the predecessor of a successor is the number inside the successor.

-/

def predN (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

/-
The pattern `Nat.succ k` does two things at once:

1. it checks that the argument is a successor;
2. it gives a name, `k`, to the number stored inside that successor.

Lean also checks that the patterns cover *all* constructors.
__Exercise__: Try commenting the `Nat.zero` case from `predN` and read the error message.
-/

--- We can use `rfl` to prove simple facts by computation.
example : predN 0 = 0 := by rfl
example : predN 1 = 0 := by rfl
example : predN 7 = 6 := by rfl

--- With `rfl` we can also prove more general facts: for example, that
--- the predecessor of the successor of n is always n
theorem pred_succ (n: Nat) : predN (Nat.succ n) = n := by rfl

--- Most of the times, also the successor of the predecessor of `n` is `n`
example : Nat.succ (predN 3) = 3 := by rfl
example : Nat.succ (predN 7) = 7 := by rfl

/-
__Exercise__: but is this *always* true? If not, provide a counterexample
-/
example : let n := sorry                  --- replace this sorry with a natural number
  !(Nat.succ (predN n) == n) := by sorry   --- once done, replace this sorry with rfl

/-
We can define the predecessor a bit more succinctly, using:
* the numeral `0` instead of `Nat.zero` in the first pattern;
* the syntactic sugar `n + 1` instead of `Nat.succ n` in the second pattern;
* the compact equation-style syntax, which does not require the keyword `match`.
These simplifications lead to the following definition:
-/

def predN₂ : Nat → Nat
  | 0     => 0
  | n + 1 => n

#eval predN₂ 7


/-
We exploit all the shorthands used in `predN₂`, and the `_` wildcard introduced
in the previous lecture, to define a function `isZero` that tells whether its argument is zero.
-/

def isZero : Nat → Bool
| 0 => true
| _ => false

example : isZero 0 = true  := by rfl
example : isZero 3 = false := by rfl


/-
From now on we will mostly use `n + 1` in patterns, since this is what Lean shows us in goals.
However, it must be used consciously: writing `1 + n` in a pattern results in an error!

Patterns can also be *nested*: the pattern `n + 2` means `Nat.succ (Nat.succ n)`,
and it matches every number that is at least two.

-/

end Pattern_matching_on_Nat


section Recursion

/-
## Parity test

In imperative languages, a familiar way to process a natural number is a loop.

For example, assume that we want to compute if a number is even, but our language does
not have a modulus operator.  In an imperative language, we could solve the problem as follows:

    while n >= 2 do
        n := n - 2
    if n = 0 then   // n = 0 -> the number is even
      return true
    else            // n = 1 -> the number is odd
      return false

In functional programming we express the same idea by *recursion*.
A function examines the input, handles the base case, and makes a recursive
call on a smaller piece of the input.  There are no variables to update.

For example, the function `isEven` computes the parity of a number.

-/

def isEven : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => isEven n

example : isEven 0    := by rfl
example : !(isEven 1) := by rfl
example : isEven 2    := by rfl
example : !(isEven 7) := by rfl
example : isEven 10   := by rfl

/-
Notice the recursive call `isEven n` in the last case.  The argument of the
recursive call is *smaller* than the original argument `n + 2`.  Lean can see this
from the pattern: `n` is obtained from the original argument by removing two constructors.

For example:

    isEven 4  =  isEven 2  =  isEven 0  =  true

This observation is fundamental to ensure termination of computations.

-/


/-
## Recursive addition

In an imperative language, we can add `m` to `n` by counting `m` down to zero:

    result := n
    while m > 0 do
        result := result + 1
        m := m - 1
    return result

To define addition recursively, we first have to choose which of the two arguments we want
to decrease to the base case.  Let's choose the second argument `m`.
Then, we have the equations:

    n + 0     = n
    n + (m+1) = (n + m) + 1

In Lean, these equations can be directly transformed into a recursive function:
-/

def addN (n m : Nat) : Nat :=
  match m with
  | 0      => n
  | m' + 1 => Nat.succ (addN n m')

#check addN

example : addN 2 3 = 5          := by rfl
example : addN (addN 1 2) 3 = 6 := by rfl

/-
The recursive call is `addN n m'`.  The new argument `m'` is smaller than the
original argument `m' + 1`, so any evaluation of `addN` eventually terminates.

Lean evaluates `addN 2 3` by unfolding the definition again and again:

    addN 2 3
    = Nat.succ (addN 2 2)
    = Nat.succ (Nat.succ (addN 2 1))
    = Nat.succ (Nat.succ (Nat.succ (addN 2 0)))
    = Nat.succ (Nat.succ (Nat.succ 2))
    = 5

Reading such a trace is a very good way to understand a recursive function.
When you are unsure about a definition, try to produce a trace by hand.

The definition follows a very useful pattern:

    match n with
    | base case      => result for the base case
    | recursive case => result built from a smaller recursive call

This is called *structural recursion*: the recursive calls are made on pieces
of the input obtained by removing constructors.  Lean accepts a recursive
definition only if it can check that the recursion terminates.  This is not
just a technicality.  Lean is also a proof assistant, and a function that
never terminates would allow us to prove false statements.  For instance,
Lean rejects the following definition, because the recursive call is on a
*bigger* number (try it in a scratch file and read the error message):

    def bad (n : Nat) : Nat :=
      bad (n + 1)

-/

/-
__Exercise__: Re-define `addN` by using syntactic sugar and equation-style pattern matching.
-/

def addN₂ : Nat → Nat → Nat := sorry

example : addN₂ 4 5 = 9 := by sorry


/-

As expected, a function can call a previously defined function.  We do not need
to repeat the implementation of addition every time we want to add numbers.
This is one of the main reasons for defining small reusable functions.

__Exercise__: Define a recursive function `doubleN` that doubles its argument doubleN n = n+n
-/

def doubleN (n : Nat) : Nat := sorry

example : doubleN 0 = 0   := by sorry
example : doubleN 5 = 10  := by sorry


/-
### Multiplication

Multiplication can be defined as repeated addition:

    n * 0     = 0
    n * (m+1) = (n * m) + n

-/

def mulN (n m : Nat) : Nat :=
  match m with
  | 0      => 0
  | m' + 1 => addN (mulN n m') n

example : mulN 3 4 = 12 := by rfl
example : mulN 7 0 = 0  := by rfl
example : mulN 0 9 = 0  := by rfl

/-
Read the recursive case from the inside out:

    mulN n m'

computes `n * m'`.  We then add one more copy of `n`:

    addN (mulN n m') n

The structure of the program mirrors the mathematical definition.

-/

end Recursion


section Exercises_on_recursion

/-
### Exercise: Test if a number is odd

Define `isOdd`, which is `true` exactly for the odd numbers.
You can do it by pattern matching, or by reusing `isEven` together with Boolean negation `!`.
-/

def isOdd (n : Nat) : Bool := sorry

example : isOdd 0 = false   := by sorry
example : isOdd 7 = true    := by sorry
example : isOdd 10 = false  := by sorry


/-
### Exercise: Exponentiation

Exponentiation is repeated multiplication, recursively on the exponent:

    b ^ 0     = 1
    b ^ (e+1) = b * (b ^ e)

-/

def powN (b e : Nat) : Nat := sorry

example : powN 2 5 = 32 := by sorry
example : powN 3 0 = 1  := by sorry
example : powN 0 3 = 0  := by sorry


/-
### Exercise: Factorial

The factorial function is defined mathematically by

    0!     = 1
    (n+1)! = (n+1) * n!

-/

def fact : Nat → Nat := sorry

example : fact 0 = 1   := by sorry
example : fact 1 = 1   := by sorry
example : fact 5 = 120 := by sorry

set_option maxRecDepth 2000 in --- to avoid `maximum recursion depth has been reached`
example : fact 6 = 720 := by sorry


/-
### Exercise: Triple

Define a function `tripleN` that computes three times its argument.
Reuse `doubleN` and `addN` instead of writing a recursive definition.
-/

def tripleN (n : Nat) : Nat := sorry

example : tripleN 0 = 0  := by sorry
example : tripleN 4 = 12 := by sorry


/-
### Exercise: Sum up-to

Define a recursive function `sumUpTo` such that `sumUpTo n = 0 + 1 + 2 + ... + n`

    sumUpTo 0       = 0
    sumUpTo (n + 1) = (n + 1) + sumUpTo n

You may use Lean's built-in `+` here.
-/

def sumUpTo (n : Nat) : Nat := sorry

example : sumUpTo 0 = 0   := by sorry
example : sumUpTo 4 = 10  := by sorry
example : sumUpTo 10 = 55 := by sorry


/-
### Exercise: Fibonacci

Define the Fibonacci function:

    fibN 0       = 0
    fibN 1       = 1
    fibN (n + 2) = fibN n + fibN (n + 1)

Observe that this definition has two base cases and *two* recursive calls.
Lean accepts it because both calls are on smaller arguments.
-/

def fibN (n : Nat) : Nat := sorry

example : fibN 0 = 0    := by sorry
example : fibN 1 = 1    := by sorry
example : fibN 7 = 13   := by sorry
example : fibN 10 = 55  := by sorry


end Exercises_on_recursion



section Comparing_natural_numbers

/-
## Comparing numbers

Functions with several arguments can match on several arguments at once.
Here are three classic examples:

* `eqN n m` tests whether `n` and `m` are equal;
* `leN n m` tests whether `n` is less than or equal to `m`;
* `subN n m` computes `n - m`, stopping at zero.

Each of the first two returns a `Bool`, so we will be able to use them as
conditions of an `if`.  In the patterns below, `_ + 1` means "any successor,
whose predecessor we do not need to name".
-/

def eqN : Nat → Nat → Bool
  | 0,     0     => true
  | 0,     _ + 1 => false
  | _ + 1, 0     => false
  | n + 1, m + 1 => eqN n m

def leN : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | n + 1, m + 1 => leN n m

def subN : Nat → Nat → Nat
  | 0,     _     => 0
  | n + 1, 0     => n + 1
  | n + 1, m + 1 => subN n m

example : eqN 3 3 = true    := by rfl
example : eqN 3 4 = false   := by rfl
example : leN 2 5 = true    := by rfl
example : leN 5 2 = false   := by rfl
example : leN 4 4 = true    := by rfl
example : subN 7 3 = 4      := by rfl
example : subN 3 7 = 0      := by rfl

/-
In each case the last equation removes one constructor from *both* arguments.
Hence the recursive call is on smaller arguments.
-/

/-
__Exercise__ (`ltN`): define `ltN n m`, which tests whether `n < m`.
Hint: `n < m` holds exactly when `n + 1 ≤ m`.  Reuse `leN`.
-/

def ltN (n m : Nat) : Bool := sorry

example : ltN 2 3 = true  := by sorry
example : ltN 3 3 = false := by sorry
example : ltN 4 3 = false := by sorry

end Comparing_natural_numbers


/-

## Proofs of properties of natural numbers

In the rest of the lecture we exploit Lean to formally prove some properties involving Nat.

-/


section Proofs_by_simplification

/-
Most proofs we have seen so far just compute functions on concrete values and check equality:
-/

example : addN 1 1 = 2 := by rfl

/-
Here the tactic `rfl` works because both sides reduce by computation to the same number.
-/

/-
Besides these simple cases, `rfl` can also prove more interesting facts involving
quantified variables.  For example, since `addN` recurses on its *second* argument,
if in a property such argument is zero, then `rfl` works, since `addN n 0` can be computed.
-/

theorem addN_zero (n : Nat) : addN n 0 = n := by
  rfl

/-
The `rfl` tactic also works for the following property, which holds by unfolding the
definition of `addN`.
-/

theorem addN_succ_right (n m : Nat) : addN n (m + 1) = (addN n m) + 1 := by rfl

/-
__Exercise__: prove the corresponding theorems for `mulN`:
* `mulN_zero`: n * 0 = 0;
* `mulN_succ`: n * (m+1) = n * m + n
-/

theorem mulN_zero (n : Nat) : mulN n 0 = 0 := by sorry

theorem mulN_succ (n m : Nat) : mulN n (m + 1) = addN (mulN n m) n := by sorry


end Proofs_by_simplification



section Proofs_by_rewriting

/-
### Rewriting

Theorems are not only to be proved: they can be *used* in the proofs of other theorems.
The tactic `rw [h]`, where `h` is an equation `a = b`, replaces `a` by `b` in the goal.
-/

theorem succ_addN_zero : ∀ n : Nat, Nat.succ (addN n 0) = Nat.succ n := by
  intros n          --- chooses a name for the quantified variable
  rw [addN_zero]    --- addN n 0 = n

/-
To understand why such proof works, place the cursor at the left of the `rw` and
look at the goal in the Infoview:

  (addN n 0).succ = n.succ

We know from theorem `addN_zero` that `addN n 0 = n`. Therefore, after rewriting we
have an equality.
-/

/-
Here is another example of application of the `rw` tactic.
-/
theorem addN_id : ∀ n m : Nat,
  n = m →
  n + n = m + m := by
  intros n m        --- choose names for universally quantified variables
  intros h          --- move the antecedent of the implication into the hypotheses
  rw [h]            --- rewrite h in the goal using the hypothesis h (left-to-right)

/-
Note a small difference between the previous proofs:
* In `succ_addN_zero`, the equality used in `rw` is taken from another theorem (`addN_zero`)
* In `addN_id`, the equality used in `rw` is taken from the *context*.
-/

/-
It is important to note that rewritings have a direction. In the previous proofs, this
direction was implicitly from *left-to-right*.  For example, after the application of
`rw [h]` in `addN_id`, the goal is reduced into `m = m` (check the Infoview).

It is also possible to apply rewriting *right-to-left* (check the difference in the Infoview).
-/
theorem addN_id₂ : ∀ n m : Nat,
  n = m →
  n + n = m + m := by
  intros n m        --- choose names for universally quantified variables
  intros h          --- move the antecedent of the implication into the hypotheses
  rw [<-h]          --- rewrite h in the goal using the hypothesis h (right-to-left)


/-
### Facts that do *not* hold by computation

What about the symmetric statement

    addN 0 n = n

where `n` is an arbitrary natural number?  The expression `addN 0 n` cannot
be computed until we know which natural number `n` is, because `addN` inspects
its second argument.  If you try

    example (n : Nat) : addN 0 n = n := by
      rfl

Lean reports an error.  We need a new idea: reason by *cases* or by *induction*.

-/

end Proofs_by_rewriting



section Proofs_by_case_analysis

/-
### Case analysis

The `cases` tactic is the proof counterpart of pattern matching in definitions.
For a natural number `n` there are two cases:

* `n = 0`;
* `n = k + 1` for some natural number `k`.

Lean creates one goal for each case.  Consider the statement that `leN n 0` is
true if and only if `n` is zero, expressed by comparing it with `isZero n`.
Neither side can be computed while `n` is unknown, but each case can be.
-/

theorem leN_zero_right (n : Nat) : leN n 0 = isZero n := by
  cases n with
  | zero   => rfl
  | succ _ => rfl

/-
After `cases n with`, we write one alternative for each constructor.
In the `succ` case Lean would give a name to the number inside the successor; here
we do not need it, so we use the wildcard `_`.

__Exercise__: Prove in the same way that `isZero n = eqN n 0`.
-/

theorem isZero_eq_eqN (n : Nat) : isZero n = eqN n 0 := by
  sorry


/-
### Case analysis on an equality

Let us prove that `Nat.succ` is injective: two natural numbers with the same
successor are equal.
-/

theorem succN_injective : ∀ n m : Nat, Nat.succ n = Nat.succ m → n = m := by
  intros n m h
  cases h
  rfl

/-
After `intros n m h`, Lean shows (it may print `n.succ` for `Nat.succ n`):

    n m : Nat
    h : Nat.succ n = Nat.succ m
    ⊢ n = m

Until now we used `cases` on natural numbers.  Here we use it on the
hypothesis `h`, which is itself a *proof*.

Equality is an inductive type with one constructor:

    Eq.refl a : a = a

(Actually, the term `rfl` is a shorthand for this constructor. In tactic mode, the
`rfl` tactic closes an equality goal by constructing such a proof.)

Thus, when we write `cases h` in our proof, Lean considers the only possible constructor
case for an equality proof: the case where `h` is a reflexivity proof.

Let us see what this means in our example. A reflexivity proof for `Nat.succ n` has type:

    Eq.refl (Nat.succ n) : Nat.succ n = Nat.succ n

But the type of `h` is:

    Nat.succ n = Nat.succ m

To make these two types agree, Lean must match:

    Nat.succ n    with    Nat.succ m

Both expressions are built using the same constructor, `Nat.succ`, so their
arguments must match. Lean therefore *unifies* `m` with `n`.

Indeed, the context and goal then become:

    n : Nat
    h : Nat.succ n = Nat.succ n         (this may be removed from the Infoview)
    ⊢ n = n

The final goal is a reflexive equality, so `rfl` proves it.

This does not mean that every equality proof must literally be written using
`rfl`: equality proofs may be obtained from hypotheses or other theorems.
Rather, it means that `Eq.refl` is the only constructor case that must be
considered when eliminating an equality proof.
-/

/-
Note that if `h` states an impossible equality, such as

    h : Nat.succ n = 0

the reflexive constructor case would be impossible: `Nat.succ` and `Nat.zero`
are different constructors. Consequently, `cases h` would close the goal
without producing any new goals.
-/

theorem succ_ne_zero_example (n : Nat) : Nat.succ n = 0 → False := by
  intro h
  cases h


end Proofs_by_case_analysis


section Proofs_by_exact

/-
### Closing a goal with `exact`

Let us prove that equality is transitive: if `a = b` and `b = c`, then `a = c`.
Formally, the statement says: for all natural numbers `a`, `b`, `c`,
if `a = b`, then if `b = c`, then `a = c` (parentheses are only used for clarity).
-/

theorem eq_trans : ∀ a b c : Nat, (a = b) → (b = c) → (a = c) := by
  intros a b c      --- choose names for quantified variables
  intros h1         --- move assumption `a = b` to context
  intros h2         --- move assumption `b = c` to context
  rw [h1]           --- rewrites `h1` in the goal
  exact h2          --- applies `h2` to close the goal

/-
The `intros` tactic moves the assumptions of the statement to the context,
giving them names.  After the three `intros`, Lean shows:

    a b c : Nat
    h1 : a = b
    h2 : b = c
    ⊢ a = c

Hypotheses are proofs.  `h1` is a proof of `a = b`, and `h2` is a proof of `b = c`.
We have to prove `a = c`.

The tactic `rw [h1]` replaces `a` by `b` in the goal.  The goal becomes

    ⊢ b = c

`rw` tries to close the goal with `rfl`, but `b` and `c` are different variables,
so the goal stays open.

Now the goal is exactly the statement of the hypothesis `h2`.  The tactic
`exact h2` closes the goal by providing a proof of *exactly* what remains to
be proved.  In general:

    exact t     closes the current goal if `t` is a proof of the goal.

The term `t` is often a hypothesis, as here, or a theorem applied to arguments,
such as `addN_zero n`.

We can rewrite the statement in an alternative way, omitting quantifiers.
The proof is the same.
-/

theorem eq_trans₂ (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2

/-
We can also rewrite within the context. We illustrate this feature on the same statement.
Check how the context changes in the Infoview.
-/

theorem eq_trans₃ (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [<- h1] at h2
  exact h2


/-
__Exercise__: (`addN_zero_eq`) Use `rw` and `exact` to prove the following property.
-/

theorem addN_zero_eq (n m : Nat) (h : n = m) : addN n 0 = m := by
  sorry

/-
__Exercise__: (`addN_zero_trans`) Prove the following property.
-/

theorem addN_zero_trans : ∀ a b c : Nat, a = b → b = c → addN a 0 = c := by
  sorry

end Proofs_by_exact



section Proofs_with_have

/-
## Intermediate facts with `have`

A proof can be easier to understand if we divide it into smaller steps.
The `have` tactic lets us prove an intermediate fact and give it a name.
-/

example (a b c : Nat) (hab : a = b) (hbc : b = c) :
    Nat.succ a = Nat.succ c := by
  have hac : a = c := by    -- first prove the intermediate fact `a = c`
    rw [hbc] at hab         -- (look at the changed hypothesis)
    exact hab
  cases hac                 -- then use the intermediate fact `hac`.
  rfl

/-
The general form is:

    have name : proposition := by
      proof

Lean temporarily changes the goal to `proposition`. Once that proposition has
been proved, the original goal is restored and the new fact is available as
`name`.

Using `have` is useful when an intermediate result has a clear meaning or will
be used later in the proof.
-/


end Proofs_with_have



section Proofs_by_backward_reasoning

/-
### Backward reasoning

Let us use `succN_injective` to prove that two successors can be removed on
both sides of an equation. Note that `succN_injective a b` is not an equation.
It is an implication:

    succN_injective a b : Nat.succ a = Nat.succ b → a = b

Its *conclusion* is `a = b`, and its *premise* is `Nat.succ a = Nat.succ b`.
We can use such a theorem to reason *backwards*: to prove the conclusion, it is
enough to prove the premise.  Lean offers two ways of doing it.

#### First way: `rw` with a conditional equation
-/

theorem succ_succ_injective (a b : Nat) : a.succ.succ = b.succ.succ → a = b := by
  intro h
  rw [<- succN_injective a b]
  rw [<- succN_injective a.succ b.succ]
  exact h

/-
After `intro h`, Lean shows:

    h : a.succ.succ = b.succ.succ
    ⊢ a = b

The theorem `succN_injective a b` has the equation `a = b` as conclusion, so
`rw` can use it.  The arrow `<-` (also written `←`) means "from right to left":
`b` is replaced by `a`.  The goal becomes `a = a`, which `rw` closes by `rfl`.
The premise of the theorem does not disappear: it becomes the new goal,

    ⊢ a.succ = b.succ

The second `rw` does the same one level up and leaves

    ⊢ a.succ.succ = b.succ.succ

which is the hypothesis `h`.  So `exact h` finishes the proof.

#### Second way: `apply`

The tactic `apply` expresses the same idea directly.
-/

theorem succ_succ_injective₂ (a b : Nat) : a.succ.succ = b.succ.succ → a = b := by
  intro h
  apply succN_injective a b
  apply succN_injective a.succ b.succ
  exact h

/-
The rule is:

    apply t     where `t : P → Q` and the current goal is `Q`:
                replaces the goal `Q` by the goal `P`.

In words: "to prove `Q` it is enough to prove `P`, because `t` turns a proof
of `P` into a proof of `Q`".  Let us follow our proof:

    after intro h:
        h : a.succ.succ = b.succ.succ
        ⊢ a = b

    after apply succN_injective a b:
        ⊢ a.succ = b.succ              -- the premise

    after apply succN_injective a.succ b.succ:
        ⊢ a.succ.succ = b.succ.succ    -- the premise again

The last goal is exactly `h`, so `exact h` closes it.  (Lean may print
`a.succ` as `a + 1`: it is the same statement.)

Some details worth remembering:

* If `t` has several premises, `t : P1 → P2 → Q`, then `apply t` creates one
  goal for each premise, in order.
* If `t` has no premises, `apply t` simply closes the goal, like `exact t`.
* The goal must match the *conclusion* of `t`.  If it does not, Lean reports
  an error showing both statements, as with `exact`.
* Often Lean can find the arguments by itself.  Try writing `apply succN_injective`
  without `a b`: Lean compares the conclusion `?n = ?m` with the goal `a = b`.

Compare the three tools we now know for using a theorem `t`:

    exact t     the statement of `t` is exactly the goal;
    rw [t]      `t` is an equation, and we want to rewrite with it;
    apply t     `t` is an implication, and its conclusion is the goal:
                we continue with its premises.

The `apply` proof is also more flexible than `rw`: `rw` needs the conclusion
to be an equation, while `apply` works with any statement.

Finally, we can also reason *forwards*, from the hypothesis to the goal, by
applying the theorem to a proof, in one single step:

    exact succN_injective a b (succN_injective a.succ b.succ h)

All three proofs are correct.  The `rw` and `apply` versions work backward from
the goal and show a new goal after each step, which makes them easy to follow
in the Infoview.  The `exact` version builds the whole proof at once.
-/

end Proofs_by_backward_reasoning


/-
## Summary

We do not need to know every tactic in Lean to do this.  A small toolkit is
already enough for many elementary proofs:

* `rfl`       -- close an equality that follows by computation;
* `rw [h]`    -- rewrite the goal using the equation `h` (left-to-right);
* `rw [<-h]`  -- rewrite the goal using the equation `h` (right-to-left);
* `exact`     -- closes the goal using a hypothesis in the context;
* `apply`     -- applies an implication in the context to a goal;
* `simp`      -- repeatedly simplify using definitions and known lemmas;
* `have`      -- prove intermediate facts;
* `cases`     -- split an inductive value into its constructors;
-/


section Exercises

/-
## Exercises
-/

/-
### Exercise: Equivalent definitions of successor
-/

theorem addN_one_right (n : Nat) : addN n 1 = Nat.succ n := by
  sorry


/-
### Exercise: Repeated rewriting

Use `addN_succ_right` twice.  Observe the goal in the Infoview after each
application of `rw`.
-/

theorem addN_two_steps (n m : Nat) :
    addN n (m + 1 + 1) = addN n m + 1 + 1 := by
  sorry


/-
### Exercise: Rewriting a hypothesis

Rewrite both occurrences of `addN` in `h`, using `addN_zero n` and
`addN_zero m`.  Then close the goal with `exact`.
-/

theorem addN_zero_cancel (n m : Nat)
    (h : addN n 0 = addN m 0) : n = m := by
  sorry


/-
### Exercise: Rewriting from right to left

Use `hab` from right to left in the goal, and then use `exact`.
-/

theorem eq_from_common_left (a b c : Nat)
    (hab : a = b) (hac : a = c) : b = c := by
  sorry


/-
### Exercise: Case analysis on a natural number

Prove the result by considering the `zero` and `succ` cases for `n`.  Both
resulting goals can be closed by computation.
-/

theorem leN_eq_eqN_zero (n : Nat) : leN n 0 = eqN n 0 := by
  sorry


/-
### Exercise: Case analysis on an impossible equality

Introduce the equality as a hypothesis and then perform case analysis on it.
-/

theorem zero_ne_succ (n : Nat) : 0 = Nat.succ n → False := by
  sorry


/-
### Exercise: Backward reasoning with two premises

Use `apply eq_trans₂ a b c`.  This creates two goals: solve them using the
hypotheses `hab` and `hbc`.
-/

theorem eq_trans_apply (a b c : Nat)
    (hab : a = b) (hbc : b = c) : a = c := by
  sorry


/-
### Exercise: Repeated backward reasoning

Use `succN_injective` three times with `apply`, and finish with `exact h`.
-/

theorem succ_succ_succ_injective (a b : Nat) :
    Nat.succ (Nat.succ (Nat.succ a)) =
      Nat.succ (Nat.succ (Nat.succ b)) →
    a = b := by
  sorry


/-
### Exercise: Intermediate facts with `have`

First use `have` and `succN_injective` to obtain proofs of `a = b` and
`b = c`.  Then combine these intermediate facts to prove `a = c`.
-/

theorem eq_from_succ_chain (a b c : Nat)
    (hab : Nat.succ a = Nat.succ b)
    (hbc : Nat.succ b = Nat.succ c) : a = c := by
  sorry


/-
### Exercise: Simplification using a hypothesis

Use `simp [h]` to replace `eqN a b` with `false` and compute its Boolean
negation.
-/

theorem not_eqN_of_false (a b : Nat) (h : eqN a b = false) :
    !(eqN a b) = true := by
  sorry


/-
### Exercise: Summing up equal numbers

Solve this by way of rewriting the right theorems or assumptions.
-/

theorem plus_id : ∀ n m o : Nat, n = m → m = o → n + m = m + o := by
  sorry


/-
### Exercise: Multiplying by zero

Solve this by way of rewriting the right theorems or assumptions.
-/

theorem mult_n_0_m_0 : ∀ n m : Nat, addN (mulN n 0) (mulN m 0) = 0 := by
  sorry


/-
### Exercise: One ain't double

Hint: you can discharge a contradiction `h` with `cases h`.
-/

theorem one_not_double : ∀ n, 1 = mulN 2 n → False := by
  sorry


end Exercises
