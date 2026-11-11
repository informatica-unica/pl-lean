import PL_Lean.PL07_Prop


/-
# Exercises on propositional logic and the Curry-Howard isomorphism
-/

section Exercises


section Permutation_combinator

/- ## Permutation combinator (difficulty: 2/4)

Prove that the order of the two hypotheses of a curried function can be swapped.
Give both tactic proof and term proof.
-/

theorem flip_term {P Q R : Prop} : (P → Q → R) → Q → P → R :=
  sorry

theorem flip_tac {P Q R : Prop} : (P → Q → R) → Q → P → R := by
  sorry

end Permutation_combinator



section S_combinator

/- ## S combinator (difficulty: 2/4)

Prove the S combinator of the lambda-calculus, both in tactic and in term mode:

    (P → Q → R) → (P → Q) → P → R  .

Hint: `apply f` produces *two* goals, one for each argument of `f`; use a bullet `·`
for each of them.
-/

theorem s_term {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R :=
  sorry

theorem s_tac {P Q R : Prop} : (P → Q → R) → (P → Q) → P → R := by
  sorry

end S_combinator



section Conjunction_associativity

/- ## Associativity of conjunction (difficulty: 2/4)

Prove both the data version and the logical version, each in tactic mode and in term mode.
-/

def assoc_prod_tac {A B C : Type} : (A × B) × C → A × (B × C) := by
  sorry

def assoc_prod_term {A B C : Type} : (A × B) × C → A × (B × C) :=
  sorry

theorem and_assoc_tac {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  sorry

theorem and_assoc_term {P Q R : Prop} : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  sorry


end Conjunction_associativity


section Disjunction_associativity

/- ## Associativity of disjunction (difficulty: 3/4)

Prove associativity of disjunction in tactic mode and in term mode.
Hint: in tactic mode, `rcases h with p | q | r` splits the three cases of
`P ∨ (Q ∨ R)` at once, and each goal needs a different sequence of `left` and `right`;
in term mode, use a `match` with three branches and nested patterns such as
`Or.inr (Or.inl q)`.
-/

theorem or_assoc_tac {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  sorry

theorem or_assoc_term {P Q R : Prop} : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R :=
  sorry

end Disjunction_associativity


section Distributivity

/- ## Distributivity (difficulty: 2/4)

Prove the following distributivity laws, first on data and then on propositions.
-/

def distr_term {A B C : Type} : A × (B ⊕ C) → (A × B) ⊕ (A × C) :=
  sorry

theorem and_or_tac {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem and_or_term {P Q R : Prop} : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  sorry

theorem or_and_tac {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) := by
  sorry

theorem or_and_term {P Q R : Prop} : (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R) :=
  sorry

end Distributivity


section Triple_negation

/- ## Triple negation (difficulty: 2/4)

Prove that triple negation collapses: `¬¬¬P → ¬P`. -/

theorem not_not_not_tac {P : Prop} : ¬¬¬P → ¬P := by
  sorry

theorem not_not_not_term {P : Prop} : ¬¬¬P → ¬P :=
  sorry

end Triple_negation


section De_Morgan_Laws

/- ## De Morgan's Lawas (difficulty: 3/4)

Prove De Morgan's law for disjunction, in both directions.
-/

theorem not_or_tac {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  sorry

theorem not_or_term {P Q : Prop} : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  sorry

theorem and_not_tac {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  sorry

theorem and_not_term {P Q : Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  sorry

/- The converse implication, `¬(P ∧ Q) → ¬P ∨ ¬Q`, is **not** constructively provable. -/

theorem not_and_tac {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

theorem not_and_term {P Q : Prop} : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  sorry

end De_Morgan_Laws


section Iff

/-
## If and only if (difficulty: 2-3/4)

`P ↔ Q` means `(P → Q) ∧ (Q → P)`.  In Lean it is a structure with two fields, `mp`
(the forward implication) and `mpr` (the backward one).  Hence a proof of `P ↔ Q` is a
**pair of functions**, exactly like a type isomorphism `A ≃ B` is a pair of functions
`A → B` and `B → A` (previous lab).

The proposition `True` has exactly one proof, `True.intro` (the tactic `trivial` finds it).
It corresponds to the type `Unit`, whose only value is `()`.
-/

#check and_swap_tac

theorem and_swap_iff_tac {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  sorry

theorem and_swap_iff_term {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  sorry



/- Prove the equivalence between "`P` and `Q` imply
`R`" and "`P` implies (`Q` implies `R`)".  Tactic proof and term proof.
Hint: you proved both directions earlier (`curry_tac`, `uncurry_tac`); you may reuse
them, or write the proof from scratch.  Read the two proofs of each direction with
`#print`. -/

theorem curry_iff_tac {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) := by
  sorry

theorem curry_iff_term {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) :=
  sorry


/- __Exercise (difficulty: 2/4)__ Combine your De Morgan theorems into a single
equivalence: `¬(P ∨ Q) ↔ ¬P ∧ ¬Q`.  Tactic proof and term proof. -/

theorem de_morgan_tac {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

theorem de_morgan_term {P Q : Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  sorry

end Iff

end Exercises
