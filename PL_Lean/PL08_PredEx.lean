import PL_Lean.PL08_Pred

section Exercises

/-
In the exercises, you are free to write proofs in term or in tactic mode
(unless otherwise specified).
-/

section Universal

/- __Exercise (difficulty: 1/4)__ Two universal quantifiers commute. -/

theorem forall_forall_swap {A B : Type} {R : A → B → Prop} :
    (∀ x, ∀ y, R x y) → ∀ y, ∀ x, R x y :=
  sorry


/- __Exercise (difficulty 1/4)__ Prove the following theorem. -/

example (f : Nat → Nat) (P Q : Nat → Prop) (h1 : ∀ x, P x → Q (f x)) (h2 : ∀ y, P y) :
  ∀ x, Q (f x) := by
  sorry


/- __Exercise (difficulty: 2/4)__ A universal quantifier distributes over conjunction. -/

theorem forall_and_tac {A : Type} {P Q : A → Prop} :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry


/- __Exercise (difficulty: 2/4)__ Same as before, but in term mode. -/

theorem forall_and_term {A : Type} {P Q : A → Prop} :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
  sorry


/- __Exercise (difficulty 2/4)__ Prove the following theorem. -/

example (f : Nat → Nat) (P : Nat → Prop) (h : ∀ x, P x → P (f x)) :
  ∀ x, P x → P (f (f x)) := by
  sorry


/- __Exercise (difficulty: 2/4)__ -/

example: True ↔ (∀ q: Prop, q → q) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Yoneda lemma. -/

theorem yoneda (P : Prop) : P ↔ (∀ Q: Prop, (P → Q) → Q) := by
  sorry

end Universal



section Existential

/- __Exercise (difficulty: 1/4)__ If `P` is satisfied by every element of `A`, and `A` is
inhabited, then there exists some element of `A` that satisfies `P`. -/

example {A : Type} {P : A → Prop} (a : A) :
    (∀ x, P x) → (∃ y, P y) := by
  sorry


/- __Exercise (difficulty: 2/4)__ If `P` is satisfied by some element of `A`, and `Q` is
satisfied when `P x` is satisfied, then `Q` is satisfied. -/

example {A : Type} {P : A → Prop} {Q : Prop} :
    (∃ x, P x) → (∀ x, P x → Q) → Q := by
  sorry


/- __Exercise (difficulty: 2/4)__  -/

example {A : Type} {P Q : A → Prop} :
    (∃ x, P x) → (∀ y, P y → Q y) → (∃ z, Q z) := by
  sorry


/- __Exercise (difficulty: 2/4)__  -/

example {A B : Type} {P : A → B → Prop} :
    (∃ x : A, ∀ y : B, P x y) → (∀ y : B, ∃ x : A, P x y) := by
  sorry


/- __Exercise (difficulty: 2/4)__  -/

example {A : Type} {P : A → Prop} {Q : Prop} :
    (∀ x, P x → Q) ↔ ((∃ x, P x) → Q) := by
  sorry


/- __Exercise (difficulty: 2/4)__ Proof term. -/

theorem exists_forall_forall_exists_term {A B : Type} {R : A → B → Prop} :
    (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
  sorry


/- __Exercise (difficulty: 2/4)__ Proof term. -/

theorem exists_and_term {A : Type} {P Q : A → Prop} :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) :=
  sorry


/- __Exercise (difficulty: 3/4)__ An existential quantifier distributes over disjunction. -/

theorem exists_or_tac {A : Type} {P Q : A → Prop} :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Proof term. -/

theorem exists_or_term {A : Type} {P Q : A → Prop} :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  sorry


end Existential



section Bounded_quantifiers

/- __Exercise (difficulty: 2/4)__ Prove that if every element of `l` satisfies `P`,
and `P` implies `Q` for every object, then every element of `l` satisfies `Q`. -/

theorem bounded_forall_tac {A : Type} {P Q : A → Prop} {l : List A} :
    (∀ x ∈ l, P x) → (∀ x, P x → Q x) → ∀ x ∈ l, Q x := by
  sorry

theorem bounded_forall_term {A : Type} {P Q : A → Prop} {l : List A} :
    (∀ x ∈ l, P x) → (∀ x, P x → Q x) → ∀ x ∈ l, Q x :=
  sorry

/- __Exercise (difficulty: 3/4)__ Prove that if `P` implies `Q` for every object,
and some element of `l` satisfies `P`, then some element of `l` satisfies `Q`. -/

theorem bounded_exists_tac {A : Type} {P Q : A → Prop} {l : List A} :
    (∀ x, P x → Q x) → (∃ x ∈ l, P x) → ∃ x ∈ l, Q x := by
  sorry

theorem bounded_exists_term {A : Type} {P Q : A → Prop} {l : List A} :
    (∀ x, P x → Q x) → (∃ x ∈ l, P x) → ∃ x ∈ l, Q x :=
  sorry

end Bounded_quantifiers



section Negation

/- __Exercise (difficulty: 2/4).__ If every element satisfies `P`, there cannot
exist an element that fails to satisfy `P`. -/

theorem forall_not_exists_not {A : Type} {P : A → Prop} :
    (∀ x, P x) → ¬ (∃ x, ¬ P x) := by
  sorry


/- __Exercise (difficulty: 2/4)__ Proof term. -/

theorem not_exists_forall_not_term {A : Type} {P : A → Prop} :
    (¬ ∃ x, P x) ↔ ∀ x, ¬ P x :=
  sorry


/- __Exercise (difficulty: 2/4)__ Proof term. -/

theorem exists_not_not_forall_term {A : Type} {P : A → Prop} :
    (∃ x, ¬ P x) → ¬ ∀ x, P x :=
  sorry


/- __Exercise (difficulty: 2/4)__ -/

example: False ↔ (∀ q: Prop, q) := by
  sorry

end Negation



section Disproving_false_conjectures

/- __Exercise (difficulty: 1/4)__ Disprove the conjecture. -/

example : ¬ (∀ b : Bool, b = false) := by
  sorry


/-
__Exercise (difficulty: 2/4)__ Disprove the conjecture that every natural number is zero.
Use `1` as a counterexample.
-/

example : ¬ (∀ n : Nat, n = 0) := by
  sorry


/-
__Exercise (difficulty: 3/4)__ Disprove the conjecture that every natural number is even.
Hint: choose a witness for the counterexample and unfold the definition of `Even`.
To close the proof, proceed by `cases` on the `Nat` in the proof context.
-/

example : ¬ (∀ n : Nat, Even n) := by
  sorry


/-
__Exercise (difficulty: 3/4)__  In Checkpoint 3 you saw that the converse of `forall_or`
is not provable.  Now disprove it formally, with the same method as above: choose `Bool`,
and the two predicates `IsTrue` and `IsFalse`.  Every Boolean is true or false,
but it is not true that every Boolean is true, nor that every Boolean is false.
-/

example : ¬ (∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)) := by
  sorry


/-
__Exercise (difficulty: 4/4)__ Consider again the false conjecture:

   ∀ (A : Type) (P Q : A → Prop),
    (∃ x, P x) ∧ (∃ x, Q x) →
      ∃ x, P x ∧ Q x

We can give a more mathematically interesting counterexample by taking:

* `A = Nat`;
* `P x = Even x`;
* `Q x = Odd x`.

There are even numbers and there are odd numbers, but no natural number is
both even and odd.

Assume that `Even` and `Odd` have previously been defined by:

    def Even (n : Nat) : Prop := ∃ k, n = 2 * k
    def Odd  (n : Nat) : Prop := ∃ k, n = 2 * k + 1

Hint: use `omega` to find the final contradiction.
-/

example :
    ¬ (∀ (A : Type) (P Q : A → Prop),
        ((∃ x, P x) ∧ (∃ x, Q x) →
          ∃ x, P x ∧ Q x)) := by
  sorry

end Disproving_false_conjectures



section Classical_boundary

/- __Exercise (difficulty: 2/4)__ Hint: use excluded middle on `∃ x, P x`. -/

theorem exists_or_forall_not {A : Type} {P : A → Prop} :
    (∃ x, P x) ∨ (∀ x, ¬ P x) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Every predicate either holds everywhere or
has a counterexample.

Hint: use excluded middle, then reuse a theorem from the lecture. -/

example {A : Type} {P : A → Prop} :
    (∃ x , ¬ P x) ∨ (∀ y, P y) := by
  sorry


/-
__Exercise (difficulty: 3/4).__ Suppose that every `x` satisfies either `P` or `Q`.
Classically, either every `x` satisfies `P`, or some `x` satisfies `Q`.

Hint:
* use excluded middle on `∀ x, P x`;
* if it is false, obtain an `x` satisfying `¬ P x` (you can reuse a previous result);
* apply the hypothesis to that `x`.
-/

theorem forall_or_exists {A : Type} {P Q : A → Prop} :
    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∃ x, Q x) := by
  sorry


/-
__Exercise (difficulty: 4/4)__ The drinker paradox.

Interpret `A` as the people in a nonempty pub and `P x` as “`x` is drinking”.
The theorem `drinker_paradox` says:

    There is someone such that, if they are drinking, everybody is drinking.

It is called a paradox because this sounds as if one person's drinking somehow
caused everybody else to drink. Logically, however, it is straightforward:

* if everybody is drinking, choose any person;
* otherwise, choose someone who is not drinking. For that person, the
  implication is true because its premise `P x` is false.

Thus, the theorem neither claims that the selected person drinks nor expresses
a causal relationship. The argument is classical because it uses *excluded middle*
on `∀ y, P y`. The parameter `a : A` guarantees that the pub is nonempty.
-/

theorem drinker_paradox {A : Type} (a : A) (P : A → Prop) :
    ∃ x, P x → ∀ y, P y := by
  sorry

end Classical_boundary



section Equality

/- __Exercise (difficulty: 1/4)__ Transitivity of equality. -/

theorem eq_trans {A : Type} {a b c : A} : a = b → b = c → a = c := by
  sorry


/- __Exercise (difficulty: 1/4)__ Equal arguments give equal results (congruence):
if `a = b` then `f a = f b`, for every function `f`. -/

theorem eq_congr {A B : Type} {a b : A} (f : A → B) : a = b → f a = f b := by
  sorry


/- __Exercise (difficulty: 2/4)__ Leibniz's principle: if `a = b` and the predicate `P`
holds for `a`, then it holds for `b`. -/

theorem eq_subst {A : Type} {P : A → Prop} {a b : A} : a = b → P a → P b := by
  sorry


/- __Exercise (difficulty: 1/4)__ Congruence for a function of two arguments. -/

theorem eq_congr₂
    {A B C : Type} {a₁ a₂ : A} {b₁ b₂ : B}
    (f : A → B → C) :
    a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ := by
  sorry

end Equality



section Dependent_types

/- __Exercise (difficulty: 1/4)__ Define an inhabitant of the dependent function type below.
-/

def depFunInhabitant₁ : (b1 b2 : Bool) →
  (match b1,b2 with
    | false,false => Bool
    | false,true  => Nat
    | true,_      => Prop) :=
  sorry

/- __Exercise (difficulty: 2/4)__ Define an inhabitant of the dependent function type below.
-/

def depFunInhabitant₂ : (n : Nat) → (if n<=1 then Bool else Unit) :=
  sorry

/-
__Exercise (difficulty: 2/4)__ The type of the second argument and of the
result both depend on `b`. For a natural number, add one. For a string, append `"!"`.
-/

#eval "hello " ++ "world"

def modifyChoice : (b : Bool) → Choice b → Choice b :=
  sorry

/-
__Exercise (difficulty: 1/4)__ Construct two dependent pairs, one containing
a natural number and one containing a string.
-/

def natChoicePair : (b : Bool) × Choice b :=
  sorry

def stringChoicePair : (b : Bool) × Choice b :=
  sorry


/-
__Exercise (difficulty: 2/4)__ Return the natural number stored in the pair
when the tag is `true`. When the tag is `false`, return the length of the
stored string. `s.length` gives the length of `s`. -/

def choiceSize : ((b : Bool) × Choice b) → Nat :=
  sorry


/-
__Exercise (difficulty: 2/4)__ Return twice `n`, together with a proof that
the result is even.
-/

def doubleWithProof (n : Nat) : {m : Nat // Even m} :=
  sorry

example : (doubleWithProof 7).val = 14 := by
  sorry


/-
__Exercise (difficulty: 1/4)__ Recover the correctness property stored in `sqrt4`.
-/

theorem sqrt4_correct : sqrt4.val * sqrt4.val = 4 :=
  sorry


/-
__Exercise (difficulty: 1/4)__ A subtype stores its witness as data, so it
can always be extracted.
-/

def subtypeWitness {A : Type} {P : A → Prop} :
    {x : A // P x} → A := by
  sorry

/-
__Exercise (difficulty: 3/4).__ Prove the induction principle directly using
`Nat.rec`, without using the `induction` tactic.
-/

theorem nat_induction_term
    {P : Nat → Prop}
    (h0 : P 0)
    (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n :=
  sorry


end Dependent_types



section Divisibility

/-
Number Theory gives us an interesting application of dependent types:
the notion of **divisibility**.
In the realm of Integers, we say an integer `d` divides an integer `n` if `n`
is a multiple of `d`.

Stated as a proposition, there exists a number `k` that can multiply `d` to yield `n`.
-/

def DivDef (d n : Int) := ∃ k, n = d * k

infix:55 " | " => DivDef

/-
To prove that an integer divides another, we must come up with the factor `k`.
-/

example : 2 | 10 := by exists 5
example : 5 | 10 := by exists 2
example : 5 | -15 := by exists -3

/-
On the flip side, when we have a divisibility hypothesis we can extract the factor `k`
and derive something else algebraically.
-/

example (z : Int) : 4 | z → 2 | z := by
  intro h
  rcases h with ⟨k, hk⟩
  exists k * 2
  rw [hk]
  omega


example : ¬ 3 | 10 := by
  intro contra
  rcases contra with ⟨k, hk⟩
  omega

/-
We've introduced the operator `|` to make the theorems and proofs look nicer but
keep in mind that it's an existential proposition in disguise: we prove it with `exists`
when it appears in the goal and unpack it with `rcases` when it is an assumption.

The same applies for the congruence notation we introduce later.

As you can see in the example proofs above, the `omega` tactic is your friend.
Exploit it to quickly prove boring arithmetic equations. You should also rely on
the algebraic theorems of the `Int` library often to do the following exercises.
-/


/-
__Exercise (difficulty: 1/4)__ Prove that 1 divides any number.
-/

theorem one_div_any (z : Int) : 1 | z := by
sorry


/-
__Exercise (difficulty: 1/4)__ Prove that any number divides zero.
-/

theorem any_div_zero (z : Int) : z | 0 := by
sorry


/-
__Exercise (difficulty: 2/4)__ Zero only divides itself.
-/
theorem zero_div_zero (z : Int) : 0 | z ↔ z = 0 := by
sorry


/-
__Exercise (difficulty: 3/4)__ Divisibility is transitive.

Hint: you will need `Int.mul_assoc` after locating the witness.
-/

theorem div_trans (x y z : Int) : x | y → y | z → x | z := by
sorry


section Congruences

/-
We say that two integers `a` and `b` are _congruent modulus `m`_ if `m` divides their difference.
The classical meaning of this is that `a` and `b` leave the same remainder when divided by `m`.

Since it is a divisibility statement under the hood, we prove and work with congruences
using the same tactics of existential statements.
-/

def CongrDef (a b m : Int) := m | a - b

/- Use `\equiv` for the symbol `≡` -/
notation a " ≡ " b " (mod " m ")" => CongrDef a b m

example : 10 ≡ 3 (mod 7) := by exists 1
example : 10 ≡ -4 (mod 7) := by exists 2
example : (-1) ≡ 10 (mod 11) := by exists -1


/-
__Exercise (difficulty: 1/4)__ Every pair of integers is congruent modulus 1.
-/

theorem any_cong_one (a b : Int) : a ≡ b (mod 1) := by
sorry


/-
__Exercise (difficulty: 2/4)__ A multiple of `m` leaves zero as remainder when divided by `m`.

This theorem bridges divisibility and congruence.
-/

theorem div_imp_mod_zero (a m : Int) : m | a → a ≡ 0 (mod m) := by
sorry


/-
__Exercise (difficulty: 3/4)__ Congruence modulus `m` is a symmetric relation over integers.

Hint: massage the goal with `Int.neg_sub` and `Int.mul_neg`.
-/

theorem mod_symm (a b m : Int) : a ≡ b (mod m) → b ≡ a (mod m) := by
sorry


/-
__Exercise (difficulty: 1/4)__ Shifting by multiples of the modulus is a closed operation.
-/

theorem mod_shift (k d m : Int) : (m * k + d) ≡ d (mod m) := by
sorry


/-
__Exercise (difficulty: 2/4)__ Two numbers that differ only by multiples of ten
leave the same remainder when divided by 2.
-/

theorem divisibility_2 (k d : Int) : (10 * k + d) ≡ d (mod 2) := by
sorry

/-
Note: since any integer can be decomposed as `10 * k + d`, where `d` is the last digit,
this means divisibility by 2 depends only on the last digit of a decimal number.

Let's derive a more general statement!
-/

/-
__Exercise (difficulty: 4/4)__ Divisibility by 2^n depends only on the last n digits of a decimal number.

Hint: by induction on `n`. Simplify with the exponents with `Int.pow_succ` in the inductive case.
-/

theorem divisibility_pow2 (k d : Int) : ∀ n : Nat, (10^n * k + d) ≡ d (mod 2^n) := by
sorry

end Congruences

end Divisibility


end Exercises
