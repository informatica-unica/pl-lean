import PL_Lean.PL01_Basics

section Exercises

/-
# Exercises

Replace each `sorry` with a definition or proof.

Try to solve each exercise before looking back at similar examples.
-/


/-
## Exercise: Negation agrees with pattern matching (difficulty: 1/4)

Prove the following theorem. Hint: split into the two cases for `b`, then use `rfl`.
-/

theorem negB_eq_negMatch : ∀ b : Bool,
    negB b = negMatch b := by
  sorry


/-
## Exercise: Conjunction agrees with pattern matching (difficulty: 1/4)

Prove the following theorem.
-/

theorem andB_eq_andMatch : ∀ a b : Bool,
  andB a b = andMatch a b := by
  sorry


/-
## Exercise: De Morgan's law (difficulty: 1/4)

Prove the following Boolean form of one of De Morgan's laws.
-/

theorem deMorgan_nand (a b : Bool) :
    !(a && b) = ((!a) || (!b)) := by
  sorry


/-
## Exercise: Associativity of AND (difficulty: 2/4)

State and prove the associativity of conjunction: a && (b && c) = (a && b) && c
-/

--- theorem and_associative (a b : Bool) : ... := sorry

/-
Hint: mind the priority of the operators && and =.
You can put your mouse over them in the Infoview to see what operands Lean
automatically groups together in the absence of parentheses.
-/



section Nor

/-
## Exercise: NOR (difficulty: 2/4)

The NOR between two Boolean values is true exactly when both inputs are false.

Define the NOR connective in 3 versione:
* `norB`, using Lean's Boolean operators;
* `norIf`, using conditional expressions;
* `norMatch`, using pattern matching.

Prove that the three implementations are equivalent.
Then, prove that NOR enjoys commutativity.
-/

def norB (a b : Bool) : Bool :=
  sorry

def norIf (a b : Bool) : Bool :=
  sorry

def norMatch (a b : Bool) : Bool :=
  sorry

example (a b : Bool) : norB a b = norIf a b := by
  sorry

example (a b : Bool) : norIf a b = norMatch a b := by
  sorry

theorem nor_commutative (a b : Bool) :
    norB a b = norB b a := by
  sorry

end Nor



section All_three

/-
## Exercise: All three (difficulty: 2/4)

Define a function that returns true exactly when all three arguments are true.
First use Boolean operators.  Then try a conditional or pattern matching.
Finally, show that the two definitions are equivalent.
-/

def allThree (a b c : Bool) : Bool :=
  sorry

example : allThree true true true = true := by
  sorry

example : allThree true false true = false := by
  sorry

def allThreeMatch (a b c : Bool) : Bool :=
  sorry

example (a b c : Bool) : allThree a b c = allThreeMatch a b c := by
  sorry

end All_three



/-
## Exercise: Multiplexer (difficulty: 3/4)

Write a function of type:

  mux2 : Bool → Bool → Bool → Bool

such that `mux2 s0 a b` equals to `a` if `s0` is true, otherwise it equals to `b`.

Try with different implementation styles, using:
* the built-in logical connectives `!`, `&&`, `||`;
* conditional expressions;
* pattern matching.

Then, using pattern matching, write a function of type:

  mux4 : Bool → Bool → Bool → Bool → Bool → Bool → Bool

such that `mux4 s1 s0 a0 a1 a2 a3` equals to `ai` if `s1 s0` is the binary encoding of `i`.

Now, write `mux4_from_mux2`, an alternative implementation of `mux4` that reuses `mux2`.

Finally, prove that `mux4` and `mux4_from_mux2` are equivalent.
-/

def mux2 (s0 a b : Bool) : Bool :=
  sorry

def mux4 (s0 s1 a0 a1 a2 a3 : Bool) : Bool :=
  sorry

def mux4_from_mux2 (s0 s1 a0 a1 a2 a3 : Bool) : Bool :=
  sorry

example (s0 s1 a0 a1 a2 a3 : Bool) :
  mux4 s0 s1 a0 a1 a2 a3 = mux4_from_mux2 s0 s1 a0 a1 a2 a3 := by
  sorry

end Exercises
