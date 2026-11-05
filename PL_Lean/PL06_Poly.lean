set_option autoImplicit false

/-
# Polymorphic functions

In the previous lecture, we defined functions on concrete product and sum types.
For example, we used types such as:

    Nat → Nat
    Nat ⊕ Bool → Bool ⊕ Nat
    (Nat × Nat → Nat) → (Nat → Nat → Nat)

Several of those definitions did not really depend on the particular types
`Nat` and `Bool`.  Swapping the components of a pair, for example, works in the
same way independently of the types of its components.

In this lecture we study how to write a single definition that works uniformly
for many types.  This idea is called **polymorphism**.

Our main application will be the type of **lists**.  We will see several
algorithms on lists that are naturally polymorphic, as they do not depend on
the types of the list elements.

By the end of the lecture, you should be able to:

* distinguish a type parameter from an ordinary value parameter;
* read the type of a polymorphic function, such as `(A : Type) → A → A`, and
  explain what it promises;
* read and define functions with explicit and implicit type parameters;
* explain, informally, why a polymorphic function must treat all types uniformly;
* understand why Lean sometimes displays universe variables such as `u`;
* construct lists and inspect them by pattern matching;
* define recursive and higher-order functions on lists;
* prove simple properties of lists by induction.

Exercise difficulties use the same relative scale as in previous lectures:

* **1/4:** one direct idea;
* **2/4:** two ideas must be combined;
* **3/4:** a more substantial construction or proof;
* **4/4:** an optional challenge.

You find additional extended exercises in the file `PL06_PolyEx.lean`.

-/


section Motivation

/-
## Why polymorphism?

Consider the following two identity functions:
-/

def identityNat (n : Nat) : Nat :=
  n

def identityBool (b : Bool) : Bool :=
  b

example : identityNat 5 = 5 := by rfl
example : identityBool true = true := by rfl

/-
Their implementations are identical.  Only their types are different.
Duplicating the definition for every possible type would be boring
(and we could never write all the defs, since there are infinitely many types).

Lean allows a function to receive a **type** as an argument.  This is possible
because, in Lean, types are ordinary terms: `Nat` is a term just like `5`,
as well as `Type`, namely the "type of types".

In the following definition, `A` is a **type parameter**, while `x` is an
ordinary **value parameter**:
-/

def identityExplicit (A : Type) (x : A) : A :=
  x

#check identityExplicit
#check (identityExplicit)   -- parentheses: print the type as an arrow type
#check identityExplicit Nat
#check identityExplicit Bool

example : identityExplicit Nat 5 = 5 := by rfl
example : identityExplicit Bool true := by rfl

/-
Let us look carefully at what Lean tells us.

The function `identityExplicit` has *two* parameters:

* `A : Type` is a type parameter: its value is a type such as `Nat`;
* `x : A` is a value parameter: the *type* of `x` is given by the first parameter.

The order matters: the declaration of `x` mentions `A`, so `A` must be
declared first.  In general, the type of a parameter and the result type may
depend on the parameters that come before.

Consequently, the *type* of `identityExplicit` is

    (A : Type) → A → A

This is called a **dependent function type**: the name `A` that is bound in
front of the first arrow is *used* in the rest of the type.  Read it as

    "for every type A, a function from A to A".

Lean also accepts the notation `∀ A : Type, A → A` for the same type.
When the result type does *not* mention the argument, we obtain the ordinary arrow:
`A → B` is just an abbreviation for `(_ : A) → B`.

What is the type of an application to a type?  Lean **substitutes** the
argument for the bound name in the rest of the type:

    identityExplicit Nat  : Nat → Nat       -- replace A by Nat  in A → A
    identityExplicit Bool : Bool → Bool     -- replace A by Bool in A → A

Thus, `identityExplicit` describes a family of identity functions, one for
each possible choice of `A`.

Technically, Lean represents this form of polymorphism using the dependent
function type described above.  We do not need the general theory of dependent
types in order to define and use polymorphic functions.
-/


/-
__Checkpoint 1__  Without running anything, write down the types of the following
three expressions, then place the cursor on each `#check` and compare.

Next, decide which of the three commented-out lines Lean would reject, and
*why*.  Remove the comment marker to test your guess.
-/

#check identityExplicit Nat 5
#check identityExplicit Bool
#check identityExplicit (List Nat)

-- #check identityExplicit Nat true
-- #check identityExplicit Bool true
-- #check identityExplicit 5 Nat


/- __Exercise (difficulty: 1/4)__ Define a function that, given a value `x` of
an arbitrary type, returns a pair with `x` both in left and in right position.
The type parameter is explicit for the moment.
-/

def duplicateExplicit (A : Type) (x : A) : A × A :=
  sorry

example : duplicateExplicit Nat 4 = (4, 4) := by sorry
example : duplicateExplicit Bool false = (false, false) := by sorry

end Motivation



section Implicit_parameters

/-
## Implicit type parameters

In an application such as

    identityExplicit Nat 5

the argument `5` already tells Lean that the relevant type is `Nat`.
Writing `Nat` explicitly is therefore redundant.

Parameters written between braces `{...}` are **implicit**.
Lean tries to infer their values from the surrounding expression.
-/

def identityImplicit {A : Type} (x : A) : A :=
  x

#check identityImplicit
#check @identityImplicit

#eval identityImplicit 5
#eval identityImplicit true

example : identityImplicit 12 = 12 := by rfl
example : identityImplicit "Ciao" = "Ciao" := by rfl

/-
In `identityImplicit 5`, Lean sees that `5 : Nat` and infers `A := Nat`.
Similarly, it infers `A := Bool` in `identityImplicit true`.

The implicit argument has not disappeared.  The symbol `@` asks Lean to show
and accept implicit arguments explicitly:
-/

#eval @identityImplicit Nat 5
#eval @identityImplicit Bool true

/-
Compare the two applications:

    identityImplicit 5       -- Lean infers the type argument
    @identityImplicit Nat 5  -- we provide the type argument explicitly

Implicit arguments are a convenience provided by Lean's elaborator (the part of
Lean that turns what you write into a fully explicit expression).  They do not
change the meaning of the function.  In particular, the braces are not what
makes the definition polymorphic: `identityExplicit` was already polymorphic.
Braces only let Lean omit and reconstruct the type argument.

(Why did we set `autoImplicit false` at the top of the file?  Without this
option, Lean would silently treat an unknown name such as `A` in a signature as
an implicit parameter.  That is convenient for experts, but it hides exactly
the thing we want to see in this lecture: every type parameter should be
visible in the signature.)
-/


/-
__Checkpoint 2__  Which of the following four lines does Lean accept?
Decide first, then remove the comment markers one by one.

Below, `emptyList` has an implicit parameter but *no* value parameter.
How can Lean possibly find `A`?
-/

-- #check identityImplicit 5
-- #check identityImplicit Nat 5
-- #check @identityImplicit Nat 5
-- #check @identityImplicit 5

def emptyList {A : Type} : List A :=
  []

#check (emptyList : List Nat)
#check (emptyList : List Bool)

-- #eval emptyList      -- what do you expect?  Try it.


/- __Exercise (difficulty: 1/4)__ Rewrite `duplicateExplicit` using an implicit
type parameter. -/

def duplicate {A : Type} (x : A) : A × A :=
  sorry

example : duplicate 4 = (4, 4) := by sorry
example : duplicate false = (false, false) := by sorry


/-
### Type abstraction and type application

Functions in Lean are created with `fun`.  A polymorphic function is created
in exactly the same way; its first parameter just happens to be a type:
-/

#check fun (A : Type) (x : A) => x

example : identityExplicit = fun (A : Type) (x : A) => x := by rfl

/-
So in Lean:

* **type abstraction** ("this function works for every type A") is an ordinary
  `fun` whose parameter has type `Type`;
* **type application** ("use it at the type `Nat`") is an ordinary function
  application, as in `identityExplicit Nat`.

There is no separate machinery for polymorphism.  Implicit arguments only
decide *who writes* the type application: you (`@identityImplicit Nat 5`) or
the elaborator (`identityImplicit 5`).
-/


/-
__Checkpoint 3__  Predict which of the following types are legit.
-/

-- #check @duplicate Nat 4
-- #check @duplicate 4
-- #check duplicate 4
-- #check (duplicate 4).1 + 1
-- #check (duplicate 4) + 1


end Implicit_parameters



/-
## A brief note about universes

We just said that `Type` is "the type of types".  But `Type` itself is a term,
so it must have a type too.  Let us ask Lean:
-/

#check Nat
#check Type
#check Type 1

/-
There cannot be a single type of all types satisfying

    Type : Type

because this would make Lean's logic inconsistent (this is known as Girard's
paradox, a cousin of Russell's paradox).  Lean instead organizes types into a
hierarchy of **universes**:

    Type 0 : Type 1
    Type 1 : Type 2
    Type 2 : Type 3
    ...

`Nat`, `Bool`, and `String` belong to `Type 0`.  When we simply write `Type`,
we mean `Type 0`.
-/

/-
__Checkpoint 4__  Which universe do you expect each of the following to live in?
(`List` is a *function* from types to types; we study it below.)
-/

#check Type → Type
#check (A : Type) → A → A
#check List
#check List Nat

/-
Surprisingly, the type of the identity function is not in `Type 0`.
Since it quantifies over all types in `Type`, it is "too big" to be one of them.
-/

/-
We can declare names for arbitrary universe levels:
-/

universe u v w

/-
The following is the universe-polymorphic version of the identity function:
-/

def identityU {A : Type u} (x : A) : A :=
  x

#check @identityU

/-
The definition works for a type `A` in any universe `u`.
Lean normally infers both `u` and `A`, so using the function remains simple:
-/

example : identityU 7 = 7 := by rfl
example : identityU true = true := by rfl

example : identityU Nat = Nat := by rfl    -- we could not do this with `identityImplicit`
example : identityU (Nat × Bool) = (Nat × Bool) := by rfl

/-
For the rest of the lecture, we will omit universes in polymorphic definitions.
This has a downside, in that these functions are less general than they could be,
but it has the benefit of making our definitions easier to read.
-/

section Polymorphic_functions


/-
## Polymorphic functions on familiar types

We now generalize some functions from the previous lecture.
-/

def firstP {A : Type} {B : Type} (p : A × B) : A :=
  p.1

def secondP {A : Type} {B : Type} (p : A × B) : B :=
  p.2

def swapP {A : Type} {B : Type} (p : A × B) : B × A :=
  (p.2, p.1)

example : firstP (3, true) = 3 := by rfl
example : secondP (3, true) = true := by rfl
example : swapP (3, true) = (true, 3) := by rfl
example : swapP ("Lean", 4) = (4, "Lean") := by rfl

/-
Note that `swapP` has two type parameters, since the two components may have
different types. Its implementation does not need to know them anyway.
-/


/- __Exercise (difficulty: 1/4)__ Define a polymorphic function that replaces
the first component of a pair while preserving the second component.  Note that
the new first component may have a *different* type from the old one, which is
why the signature has three type parameters. -/

def replaceFirst {A : Type} {B : Type} {C : Type}
    (newFirst : C) (p : A × B) : C × B :=
  sorry

example : replaceFirst false (3, "hello") = (false, "hello") := by sorry


/-
### Polymorphic functions on `Option`

`Option A` represents either a value of type `A` or no value.
The definitions of `Option` and its constructors are polymorphic:

    none   : Option A
    some x : Option A       if x : A
-/

def getOrElseP {A : Type} (o : Option A) (fallback : A) : A :=
  match o with
  | none   => fallback
  | some x => x

example : getOrElseP (some 7) 0 = 7 := by rfl
example : getOrElseP none 0 = 0 := by rfl
example : getOrElseP (some "Ciao") "unknown" = "Ciao" := by rfl


/- __Exercise (difficulty: 1/4)__ Define `mapOptionP`.  If the option contains
an element of type `A`, apply `f` to obtain a `B`.  Preserve `none`. -/

def mapOptionP {A : Type} {B : Type}
    (f : A → B) (o : Option A) : Option B :=
  sorry

example : mapOptionP Nat.succ (some 4) = some 5 := by sorry
example : mapOptionP Nat.succ none = none := by sorry


/- __Exercise (difficulty: 1/4)__ Prove that swapping a polymorphic pair twice
returns the original pair. -/

theorem swapP_twice {A : Type} {B : Type} (p : A × B) :
    swapP (swapP p) = p := by
  sorry


/- __Exercise (difficulty: 1/4)__ Prove that mapping the identity function over
an option leaves it unchanged. -/

#check identityImplicit

theorem mapOptionP_identity {A : Type} (o : Option A) :
    mapOptionP (fun x => x) o = o := by
  sorry


/-
### Uniform behaviour (parametricity)

A function with type

    {A : Type} → A → A

must work for every possible `A`.  It cannot assume that its argument is a
natural number, a Boolean, or a string.  In particular, it cannot add its
argument, negate it, or inspect its constructors.

Lean enforces this.  The following definition is *rejected*:

    def bad {A : Type} (x : A) : A := 0

Lean looks for a way to write `0` as a value of the unknown type `A`, and
reports that it cannot find one (it fails to synthesize `OfNat A 0`).

Without receiving any additional operations, the only value of type `A`
available to the function is its argument.  This uniformity is the intuitive
idea behind **parametric polymorphism**.  It is a *restriction* on what the
function can do, and at the same time a *guarantee* for whoever uses it: from
the type alone we learn a lot about the function.
-/


/-
__Checkpoint 5__  The type `{A : Type} → A → A → A` has (at least) two
inhabitants that behave differently.  Define them.
-/

def pickFirst {A : Type} (x y : A) : A :=
  sorry

def pickSecond {A : Type} (x y : A) : A :=
  sorry

example : pickFirst 10 20 = 10      := by sorry
example : pickSecond 10 20 = 20     := by sorry
example : pickFirst "a" "b" = "a"   := by sorry
example : pickSecond "a" "b" = "b"  := by sorry

/-
__Checkpoint 6__  Define (total, terminating) functions with the given types.
-/

example : {A : Type} → A → A          := sorry

-- Define two different functions with the given type
example : {A : Type} → A → Option A   := sorry
example : {A : Type} → A → Option A   := sorry

-- Define two different functions with the given type
example : {A : Type} → A → Bool       := sorry
example : {A : Type} → A → Bool       := sorry

/-
Note how much the type alone tells us!  This phenomenon is called
**parametricity**; we will see a concrete consequence for lists later (the
theorem `mapL_reverseL`).
-/


end Polymorphic_functions



section Lists

/-
## Polymorphic lists

A list contains zero or more values of the **same** type.
Lean's list type is polymorphic:
-/

#check List
#check List Nat
#check List (Nat × Bool)

/-
`List` by itself is a **type constructor**: it must be applied to a type.
For example, applying `List` to `Nat` produces the type `List Nat`;
In terms of the previous sections: `List` is a function of type `Type u → Type u`,
and `List Nat` is the result of applying it.

Conceptually, Lean's built-in list type has the following definition:

    inductive List (A : Type u) where
      | nil  : List A
      | cons : A → List A → List A

We do not repeat this declaration below since `List` is already defined by Lean.

A list therefore has two possible forms (using Lean's notation):

* `[]`, the empty list;
* `x :: xs`, a non-empty list with head `x` and tail `xs`.

The notation `[a, b, c]` abbreviates:

    a :: b :: c :: []
-/

def numbers : List Nat :=
  [1, 2, 3, 4]

def truthValues : List Bool :=
  [true, false, true]

def labelledNumbers : List (String × Nat) :=
  [("zero", 0), ("one", 1), ("two", 2)]

example : [1, 2, 3] = 1 :: 2 :: 3 :: [] := by rfl

/-
The following would not be accepted because all elements must have the same type:

    def badList := [1, true]       -- type error

The reason is visible in the type `List A`: there is only *one* `A`, chosen
once for the whole list.  If we really need to mix two kinds of elements, we
use a list over a sum type from the previous lecture:
-/

def mixedList : List (Nat ⊕ Bool) :=
  [Sum.inl 1, Sum.inr true]


/-
__Checkpoint 7__

The constructors of `List` are themselves polymorphic functions.  Predict
the types of the following expressions, and which ones will be rejected.
-/

-- #check [1,2,3]
-- #check [[1],[2],[3]]
-- #check [[1],2,[3]]
-- #check [some 1,none,some 3]
-- #check [some 1,none,some false]
-- #check [Sum.inl 10, Sum.inr true, Sum.inl 20]
-- #check [Sum.inl 10, Sum.inr 20]
-- #check [Sum.inl 10, Sum.inl true]
-- #check [Sum.inl 10, Sum.inl 5]

section Pattern_matching_on_lists

/-
## Pattern matching on lists

Since a list has two constructors, a complete pattern match normally has two branches:
one for `[]` and one for `x :: xs`.
-/

def headOptionL {A : Type} (xs : List A) : Option A :=
  match xs with
  | []     => none
  | x :: _ => some x

example : headOptionL ([10, 20, 30] : List Nat) = some 10 := by rfl
example : headOptionL ([] : List Nat) = none := by rfl

/-
The result is an `Option A` because an empty list has no first element.
Using `Option` makes this possibility explicit in the return type.
We will see in Checkpoint 9 that, because of parametricity, there is no alternative:
a function `List A → A` cannot exist.
-/


/- __Exercise (difficulty: 1/4)__ Define a function that removes the first
element of a list.  The tail of the empty list is again the empty list. -/

def tailL {A : Type} (xs : List A) : List A :=
  sorry

example : tailL ([10, 20, 30] : List Nat) = [20, 30] := by sorry
example : tailL ([] : List Nat) = [] := by sorry


/- __Exercise (difficulty: 1/4)__ Test whether a list is empty. -/

def isEmptyL {A : Type} (xs : List A) : Bool :=
  sorry

example : isEmptyL [true, false] = false    := by sorry
example : isEmptyL ([] : List Bool) = true  := by sorry

/- Notice that the type annotation in the last example is necessary: try it! -/
-- example : isEmptyL [] = true  := by sorry


/-
__Exercise (difficulty: 2/4)__ Prove that a list `l` is empty if and only if
`headOptionL l` returns `none`. You do not need induction.
-/

theorem empty_no_head (A : Type) (l : List A) :
  isEmptyL l = true ↔ headOptionL l = none := by
  sorry


/- __Exercise__ Formalize and prove a theorem stating that the tail of a list `l` is
  empty if `l` is empty (use the functions `isEmptyL` and `tailL` given before).
-/

--- theorem nonempty_has_tail ...

end Pattern_matching_on_lists



section Recursive_list_functions

/-
## Structural recursion on lists

As with natural numbers, pattern matching may be combined with recursion.
In the non-empty case, a structurally recursive function calls itself on the
tail `xs`, which is structurally smaller than `x :: xs`.

The length does not depend on the values stored in the list, so the head is
matched by a wildcard.
-/

def lengthL {A : Type} : List A → Nat
  | []      => 0
  | _ :: xs => 1 + lengthL xs

example : lengthL ([10, 20, 30] : List Nat) = 3 := by rfl
example : lengthL ([] : List Bool) = 0 := by rfl

/-
The same definition works for lists in every element type because it never
inspects an element.  Look at the type: `A` occurs only in the *argument*, not
in the result, so the result cannot contain any element of the list.
-/


/- __Exercise (difficulty: 1/4)__ Define the sum of a list of natural numbers.
This functions is *not* polymorphic because the addition operation is specific to `Nat`.
-/

def sumL : List Nat → Nat
  := sorry

example : sumL [2, 3, 4] = 9 := by sorry

/-
The next function joins two lists.  It recursively traverses the first list
and places each of its elements in front of the second list.
-/

def appendL {A : Type} : List A → List A → List A
  | [],      ys => ys
  | x :: xs, ys => x :: appendL xs ys

example : appendL [1, 2] [3, 4] = [1, 2, 3, 4] := by rfl
example : appendL ([] : List Nat) [3, 4] = [3, 4] := by rfl


/-
__Checkpoint 8__ Compute `appendL [1,2] [3]` by hand.
Write each step in a comment, unfolding exactly one equation of `appendL` at a time,
and say which equation you used and which values are used for the variables x, xs and ys.

    appendL (1 :: 2 :: []) (3 :: [])
  = 1 :: appendL (2 :: []) (3 :: [])     -- eqn 2, with x = 1, xs = [2], ys = [3]
  = ...
-/


/- __Exercise (difficulty: 1/4)__ Define `replicateL n x`, which constructs a
list containing `n` copies of `x`. -/

def replicateL {A : Type} : Nat → A → List A
  := sorry

example : replicateL 4 true = [true, true, true, true] := by sorry
example : replicateL 0 "Ciao" = [] := by sorry


/- __Exercise (difficulty: 2/4)__ Return the last element of a list, if one
exists.  Notice that the recursive call is made on the non-empty tail. -/

def lastOptionL {A : Type u} : List A → Option A
  := sorry

example : lastOptionL ([10, 20, 30] : List Nat) = some 30 := by sorry
example : lastOptionL ([] : List Nat) = none := by sorry


/-
__Checkpoint 9__  Define functions with the given types, whenever they exists.
-/

example : {A : Type} → List A → List A := sorry
example : {A B : Type} → List A → List B := sorry
example : {A : Type} → List A → Nat := sorry
example : {A : Type} → List A → A := sorry

end Recursive_list_functions



section Higher_order_list_functions

/-
## Higher-order functions on lists

Polymorphism and higher-order functions are especially useful together.
Recall that a higher-order function receives or returns another function.

The function `mapL` receives a transformation `f : A → B` and applies it to
every element of a list:
-/

def mapL {A B : Type} (f : A → B) : List A → List B
  | []      => []
  | x :: xs => f x :: mapL f xs

example : mapL Nat.succ [1, 2, 3] = [2, 3, 4] := by rfl
example : mapL (fun b : Bool => !b) [true, false, true] = [false, true, false] := by rfl

/-
Read its type carefully:

    mapL : (A → B) → List A → List B

The function may change the type of the elements.  For example:
-/

example : mapL (fun n => if n > 2 then true else false) [1, 2, 3] = [false, false, true] := by rfl

/-
We can obtain the same effect of the last `mapL` more succincrly using `decide`.
-/

example : mapL (fun n => decide (n > 2)) [1, 2, 3] = [false, false, true] := by rfl

/-
__Checkpoint 10__  Write down the types of these partial applications.
-/

#check mapL Nat.succ
#check mapL (fun n : Nat => decide (n > 2))
#check mapL (fun b : Bool => !b)


/- __Exercise (difficulty: 1/4)__ Define `filterL`.  It preserves precisely
the elements for which the Boolean predicate `p` returns `true`. -/

def filterL {A : Type u}
    (p : A → Bool) : List A → List A
  := sorry

example : filterL (fun n : Nat => decide (n > 2)) [1, 2, 3, 4] = [3, 4] := by sorry


/- __Exercise (difficulty: 1/4)__ Define `allL` and `anyL`.

* `allL p xs` is true when `p` is true for *all* elements of `xs`;
* `anyL p xs` is true when `p` is true for *at least one* element of `xs`.

Think carefully about the results for the empty list.
-/

def allL {A : Type u} (p : A → Bool) : List A → Bool
  := sorry

def anyL {A : Type u} (p : A → Bool) : List A → Bool
  := sorry

example : allL (fun n : Nat => decide (n > 0)) [1, 2, 3] = true   := by sorry
example : allL (fun n : Nat => decide (n > 0)) [1, 0, 3] = false  := by sorry
example : allL (fun n : Nat => decide (n > 0)) [] = true          := by sorry
example : anyL (fun n : Nat => decide (n > 5)) [1, 8, 3] = true   := by sorry
example : anyL (fun n : Nat => decide (n > 5)) [1, 2, 3] = false  := by sorry
example : anyL (fun n : Nat => decide (n > 5)) [] = false         := by sorry


/- __Exercise (difficulty: 1/4)__ Count the elements satisfying a predicate. -/

def countIfL {A : Type u} (p : A → Bool) : List A → Nat
  := sorry

example : countIfL (fun n : Nat => decide (n > 2)) [1, 3, 2, 4, 5] = 3 := by sorry



section Equality_as_an_argument

/-
### When a polymorphic function needs an additional operation

It is easy to define a membership test specifically for natural numbers:
-/

def containsN (target : Nat) : List Nat → Bool
  | []      => false
  | x :: xs => (x == target) || containsN target xs

example : containsN 3 [1, 2, 3, 4] = true := by rfl
example : containsN 8 [1, 2, 3, 4] = false := by rfl

/-
Can we simply replace `Nat` with an arbitrary type `A`?  The recursive
structure would still work, but Lean would not know how to compare two
arbitrary values of type `A`.
-/


/-
__Checkpoint 11__  Why does the following definition fail?  What does
the error message say, and how does this relate to Checkpoint 6?
How can you fix the problem?

    def containsBad {A : Type} (target : A) : List A → Bool
      | []      => false
      | x :: xs => (x == target) || containsBad target xs
-/

/-
Lean reports that it cannot synthesize an instance of `BEq A`: it does not know
any way to compare two values of the arbitrary type `A` for equality.  This is
exactly the phenomenon of the previous section: a polymorphic function cannot
use any operation on `A` unless that operation is *provided*.
-/

/-
One solution is to receive the equality test as an additional explicit argument:
-/

def containsBy {A : Type}
    (equal : A → A → Bool) (target : A) : List A → Bool
  | []      => false
  | x :: xs => equal x target || containsBy equal target xs

example : containsBy (fun a b : Nat => a == b) 3 [1, 2, 3, 4] = true := by rfl
example : containsBy (fun a b : String => a == b) "Ciao" ["Hi", "Ciao"] = true := by rfl

/-
The implementation is still uniform: it does not know how values of type `A`
are represented.  All type-specific work is performed by the `equal` argument.

The type of `containsBy` says it all: for every `A`, *given* a way to compare
two `A`s, we can search a list of `A`s.  Parametricity is not violated; the
function simply uses an operation that is part of its own signature.
-/

/-
Writing the comparison function by hand at every call is tedious.
A more elegant solution is to use Lean's **type classes**.
-/

def containsB {A : Type u} [BEq A] (target : A) : List A → Bool
  | []      => false
  | x :: xs => (x == target) || containsB target xs

example : containsB 3 [1, 2, 3, 4] = true := by rfl
example : containsB 8 [1, 2, 3, 4] = false := by rfl

/-
The parameter `[BEq A]` is an implicit argument: Lean searches for a registered
instance of the type class `BEq` for the type `A`.
This is how Lean provides overloading (*ad hoc* polymorphism).
No further details are needed for now: just think of `[BEq A]` as
"`A` must come with an equality test".
-/

end Equality_as_an_argument

end Higher_order_list_functions



section Induction_on_lists

/-
## Proofs by induction on lists

Lists are inductive values, so their properties are commonly proved by
induction.  Compare the shapes of natural numbers and lists:

    Nat                         List A
    --------------------        --------------------------
    0     (Nat.zero)            []        (List.nil)
    n+1   (Nat.succ n)          x :: xs   (List.cons x xs)

Induction on a list therefore produces two cases:

* the base case `[]`;
* the inductive case `x :: xs`, with an induction hypothesis about `xs`.

We begin with a property that holds by computation.
-/

theorem appendL_nil_left {A : Type} (xs : List A) :
    appendL [] xs = xs := by
  rfl

/-
__Checkpoint 12__  Predict whether the symmetrical theorem can be proved by `rfl`.
Think before uncommenting:

-- example {A : Type} (xs : List A) : appendL xs [] = xs := by rfl
-/

/-
We can prove `appendL_nil_right` by induction on the structure of the list.
-/

theorem appendL_nil_right {A : Type} (xs : List A) :
    appendL xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>   -- ih is the induction hypothesis
      rw [appendL]    -- check the context in the InfoView
      rw [ih]


/- __Exercise (difficulty: 2/4)__ Prove that list append is associative. -/

theorem appendL_associative {A : Type} (xs ys zs : List A) :
    appendL (appendL xs ys) zs = appendL xs (appendL ys zs) := by
  sorry


/- __Exercise (difficulty: 2/4)__ Prove that the length of an append is the
sum of the two lengths. -/

theorem lengthL_appendL {A : Type} (xs ys : List A) :
    lengthL (appendL xs ys) = lengthL xs + lengthL ys := by
  sorry


end Induction_on_lists



section Folding_lists

/-
## Folding a list

The recursive functions `sumL`, `mapL`, and many others share the same traversal pattern.
The **fold** combinators capture this general pattern.

They take three arguments:
* a function `f`,
* a value `init`, and
* a list `l`.
Then, they combine the elements of `l` using the function `f`;
the value `init` is used as an initializer. The order in which the elements are
combined depends on the direction of the fold, i.e. “right” or “left”.

The behaviour of `foldRightL f init` is informally defined as:

    foldRightL f init [] = init
    foldRightL f init [x₁] = f x₁ init
    foldRightL f init [x₁, x₂] = f x₁ (f x₂ init)
    foldRightL f init [x₁, x₂, x₃] = f x₁ (f x₂ (f x₃ init))
    ...
-/

def foldRightL {A : Type} {B : Type} (f : A → B → B) (init : B) : List A → B
  | []      => init
  | x :: xs => f x (foldRightL f init xs)


/-
We use the new combinator to define a function `sumFold` that sums all the
elements of a list. In this case, the init element is 0, while the combining
function is the addition operator `Nat.add`.

According to our informal definition, we have:
foldRightL Nat.add 0 [] = 0
foldRightL Nat.add 0 [x₁] = Nat.add x₁ 0 = x₁ + 0 = x₁
foldRightL Nat.add 0 [x₁, x₂] = Nat.add x₁ (Nat.add x₂ 0) = x₁ + (x₂ + 0) = x₁ + x₂
-/

def sumFold : List Nat → Nat :=
  foldRightL Nat.add 0          -- Nat.add := fun x acc => x + acc

example : sumFold [1, 2, 3, 4] = 10 := by rfl


/-
We now use `foldRightL` to redefine the map combinator.
-/

def mapFold {A : Type} {B : Type} (f : A → B) (xs : List A) : List B :=
  foldRightL (fun x accumulator => f x :: accumulator) [] xs

example : mapFold Nat.succ [1, 2, 3] = [2, 3, 4] := by rfl


/-
__Checkpoint 13__  `foldRightL` has *two* type parameters: `A` for the elements
of the list and `B` for the accumulated result.  Predict the types
of the following three expressions.  In which of them are `A` and `B` different?
-/

#check @foldRightL
#check foldRightL (fun (x : Nat) (acc : Nat) => x + acc) 0
#check foldRightL (fun (x : Nat) (acc : Bool) => acc && decide (x > 0)) true

/-
__Checkpoint 14__  Define the length of a list using `foldRightL`.  The
elements are never inspected, so `A` can be anything, whereas the accumulator
has type `Nat`.
-/

def lengthFold {A : Type} (xs : List A) : Nat :=
  sorry

example : lengthFold ["a", "b", "c"] = 3  := by sorry
example : lengthFold ([] : List Bool) = 0 := by sorry

end Folding_lists



section Pipe_operator

/-
## The pipe operator

Recall that function application associates to the left: `f g x` means
`(f g) x`, not `f (g x)`.  To apply a function to the *result* of another call
we must add parentheses.  For example, suppose we want to compute 2·(3²)²
using the functions `squareN` and `doubleN`:
-/

def doubleN (n : Nat) : Nat := n + n
def squareN (n : Nat) : Nat := n * n

example : doubleN (squareN (squareN 3)) = 162 := by rfl

/-
Note that as the expression becomes more complex, adding the necessary parentheses
becomes increasingly error-prone, and the expression becomes less and less readable.

Lean offers two notations that avoid these parentheses.

The first one is `f <| x`, which means exactly `f x`, but has very low
precedence and associates to the right.  Hence the following means
`doubleN (squareN (squareN 3))`:
-/

example : (doubleN <| squareN <| squareN <| 3) = 162 := by rfl

/-
The second one is the **pipe operator** `|>`.  It writes the same chain in the
order in which the computation happens, from left to right, like a Unix pipeline:
-/

example : (3 |> squareN) = 9 := by rfl
example : (3 |> squareN |> squareN) = 81 := by rfl
example : (3 |> squareN |> squareN |> doubleN) = 162 := by rfl

/-
How does it work?  The notation `x |> f` is an abbreviation for `f x`: Lean
rewrites it before type checking.  The operator associates to the left, so
`x |> f |> g` means `g (f x)`.

To see the idea at the level of ordinary functions, consider the following function.
It takes a value `x` of any type `A` and a function of type `A → B`, and applies
the function to the value:
-/

def pipe {A B : Type} (x : A) (f : A → B) : B := f x

example : pipe 3 squareN = 9 := by rfl
example : (3 |> squareN) = pipe 3 squareN := by rfl

/-
Notice that our `pipe` is not exactly how Lean implements `|>`, and we deliberately
do not attach the symbol `|>` to it.  However, as long as the right-hand side is a
function, `x |> f` and `pipe x f` behave in the same way.

Two details are important in practice:

1. **The piped value becomes the last argument.**  More generally,
   `x |> f a b` is rewritten to `f a b x`.  This works nicely with partial
   application: `mapL g` is a function of type `List A → List B`, so
   `xs |> mapL g` is `mapL g xs`.  It also explains why functions such as
   `mapL f xs`, `filterL p xs`, and `foldRightL f z xs` take the list as their
   *last* argument: it makes them convenient to use in a pipeline.

2. **The pipe has very low precedence**, lower than `+` and even than `=`.
   Therefore a pipeline inside a larger expression must be put in parentheses.
   For instance, `3 |> squareN = 9` would be read as `3 |> (squareN = 9)`, which
   is a type error; this is why the examples above are written as
   `(3 |> squareN) = 9`.
-/


/- __Checkpoint 15__ Predict the values of the following pipelines -/

example : (3 |> squareN  |> squareN |> doubleN) = sorry := by sorry
example : (10 |> Nat.sub 3) = sorry := by sorry
example : (10 |> (fun x => Nat.sub x 3)) = sorry := by sorry


/-
Pipelines are particularly useful to process lists, combining the functions
`mapL`, `filterL`, and folds.

The following pipeline replaces every even element with `1` and every odd element with `0`,
and then adds up the results; in other words, it counts the even elements:
-/

example :
  ([1,2,3,4,5,6,7]
  |> mapL (fun x => if x % 2 = 0 then 1 else 0)
  |> sumFold)
  = 3 := by rfl

/-
Compare it with the equivalent expression without the pipe, where the
operations are read from the inside out:
-/

example :
  sumFold
    (mapL (fun (x : Nat) => if x % 2 = 0 then 1 else 0)
      [1, 2, 3, 4, 5, 6, 7])
  = 3 := by rfl


/- __Checkpoint 15__ Define a function `sumSqEven` that computes the
sum of the squares of all the even elements of a list. Combine map, filter and fold
with the pipe operator.
-/

def sumSqEven (xs : List Nat) : Nat := sorry

example : sumSqEven [] = 0 := by sorry
example : sumSqEven [1, 3, 5] = 0 := by sorry
example : sumSqEven [1, 2, 3, 4, 5] = 20 := by sorry


end Pipe_operator


end Lists
