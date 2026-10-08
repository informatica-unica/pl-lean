/-
The following `import` is used to bring here the definitions of the previous lecture.

If you are working on `https://live.lean-lang.org/`, then remove the `import` and
copy-and-paste the code of the previous lecture before this one.
-/
import PL_Lean.PL02_Nat


set_option autoImplicit false


section Induction

/-
## Induction: the proof counterpart of recursion

We noted in the previous lecture that case analysis is not enough to prove `addN 0 n = n`:
in the successor case we get the goal for `k + 1`, but to solve it we need to know the
result for `k`. This is exactly what *mathematical induction* provides.

Suppose we want to prove a property `P n` for every natural number `n`.
The induction principle says that it is enough to prove:

1. `P 0`                       -- the base case;
2. `P n -> P (n + 1)`          -- the inductive case.

The second part says that if the property is true for an arbitrary `n`, then
it is true for its successor.

In Lean, the `induction` tactic exposes exactly these cases.  In the inductive case,
we also get the *induction hypothesis* `ih`: the statement for the smaller number.

-/

#check addN_succ_right    -- this lemma will be used in the proof: check it

theorem zero_addN (n : Nat) : addN 0 n = n := by
  induction n with
  | zero => rfl               -- base case
  | succ n' ih =>             -- inductive case (note `ih` in the Infoview)
      rw [addN_succ_right]    -- addN 0 (n' + 1) -> (addN 0 n') + 1)
      rw [ih]

/-
Let us follow the proof.  After `induction n with`, Lean shows two goals:

    case zero:   addN 0 0 = 0
    case succ:   ih : addN 0 n' = n'
                 ⊢ addN 0 (n' + 1) = n' + 1

* The first goal follows by computation, so `rfl` works.
* In the second goal, we use two rewritings:
  1. `rw [addN_succ_right]` rewrites `addN 0 (n' + 1)` into `addN 0 n' + 1`.
  2. Then `rw [ih]` replaces `addN 0 n'` by `n'`, and the goal becomes `n' + 1 = n' + 1`,
     which `rw` closes by itself.

This proof highlights an important correspondence:

    PROGRAMMING                  PROVING
    ------------------------------------------------
    match n with ...             cases n with ...
    recursive call on n'         induction hypothesis about n'
    base case                    base case
    recursive case               inductive case

The proof has the same shape as the recursive function it talks about.

-/

/-
As another example, we consider a variant of `addN_succ_right` where the successor is in the
first argument.  We still induct on `m`, since `addN` is recursive on its second argument.
-/

theorem addN_succ_left (n m : Nat) : addN (n + 1) m = addN n m + 1 := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    rw [addN_succ_right]      -- rewrite addN_succ in the LHS of the goal
    rw [addN_succ_right]      -- rewrite addN_succ in the RHS of the goal
    rw [ih]

/-
In the previous proof, we could have just written:
  | succ m' ih => rw [addN_succ_right,addN_succ_right,ih]
I split the rewritings in three steps so that you can check their effects in the Infoview.

Tactic proofs of this shape are often written in a shorter way using `simp`,
which repeatedly rewrites using the definitions and lemmas we give it.  For
example, the inductive case above could be written

    | succ m' ih => simp [addN, ih]

We will use both styles.  The explicit `rw` version is better for understanding
the proof, `simp` is faster to write.
-/

/-
We can now prove commutativity of our addition function.  This is a slightly
larger proof, and it shows how earlier lemmas are reused.
-/

theorem addN_comm (n m : Nat) : addN n m = addN m n := by
  induction m with
  | zero =>
    rw [addN_zero]
    rw [zero_addN]
  | succ m' ih =>
    rw [addN_succ_right]
    rw [addN_succ_left]
    rw [ih]

/-
The proof above is a useful milestone.  We have gone from a short recursive
program to a mathematical property about the program, and Lean has checked the
proof mechanically.
-/

end Induction




section Exercises

/-
## Exercises
-/


/-
### Exercise: Adding successors

Prove the following property. Hint: use existing properties about addN and successors
-/

theorem addN_self_succ (n : Nat) : addN (n + 1) (n + 1) = addN n n + 1 + 1 := by
  sorry


/-
### Exercise: Left identity of mulN

Prove that 0 is the left identity of multiplication.
Hint: by induction on `n`.  The inductive case needs `mulN_succ`, `addN_zero`, and
the induction hypothesis `ih`.  You can use them with `rw [...]` or inside `simp [...]`.
-/

theorem zero_mulN (n : Nat) : mulN 0 n = 0 := by
  sorry


/-
### Exercise: Reflexivity of eqN

Prove that `eqN` is reflexive. Hint: proceed by induction on `a`, and use the `exact` tactic.
-/

theorem eqN_refl (a : Nat) : eqN a a = true := by
  sorry


/-
### Exercise: Alternative characterization of even (n + 1)

Prove that `isEven (n+1)` is true if and only if `isEven n` is false.
Hint: `simp` knows that ! is involutory
-/

theorem isEven_succ (n: Nat) : isEven (n+1) = !(isEven n) := by
  sorry


/-
### Exercise: Doubled numbers are even

Hint: by induction on `n`.
-/

theorem isEven_doubleN (n: Nat) : isEven (doubleN n) = true := by
  sorry


/-
### Exercise: Double and addition

Hint: by induction on `n`.
-/

theorem doubleN_addN (n: Nat) : doubleN n = addN n n := by
  sorry


/-
### Exercise: Associativity of addN

Prove that `addN` is associative.

Hint: induction on `k`.  In the successor case, unfold the additions with
`addN_succ_right`, and finish with the induction hypothesis.
-/

theorem addN_assoc (n m k : Nat) : addN (addN n m) k = addN n (addN m k) := by
  sorry


end Exercises
