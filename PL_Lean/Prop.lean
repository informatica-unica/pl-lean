/-
# Propositional Logic in Lean

Working with the type `Bool` is nice because we're so accustomed to its counterparts in other programming languages.

But we're going to move away from it and in this lesson focus on a key mechanic of Lean called *propositions*. Propositions are used in Lean and in mathematics to model logical statements. They are formal specifications of the properties of programs we want to verify.

Lean provides a rich and powerful type to model mathematical propositions: the type `Prop` and its associated theorem library.
-/

#check Prop
-- #eval Prop -- we can't evaluate `Prop`: it is a type

/-
The elements of `Prop` are called propositions. We denote them with latin capital letters: P, Q, R and so on. The notation `P : Prop` stands for "P is a proposition".

Every example and theorem we saw in the first lesson revolved around a proposition, which was specified between the `:` and `:=` tokens.

By default, two propositions are defined in any Lean program: `True` and `False`.
-/

#check True -- it is a memeber of `Prop`
#print True -- it has one constructor: `True.intro`

#check False -- it is a memeber of `Prop`
#print False -- zero constructors: we can't build a value of it

/-
Given a proposition `P : Prop`, its elements are called *proofs*. Proofs are values of `P` witnessing the fact that `P` is true. Proving a proposition `P` means building a value of type `P`.

Proofs are opened with the keyword `by` and built incrementally using tactics. So, what you type after the `:=` symbol in examples and theorems is the proof of the previous logical statement.

Let's start proving the simplest of propositions: `True`. `True` has one element, its constructor `True.intro`, which is the proof that `True` is indeed true.

To use its constrctor in its proof, we need the tactic `exact`. When the goal is `P` and we have a value `p : P` in the proof's context or in the global environment, `exact p` closes the goal. In general, `exact` accepts any expression that evaluates to a value of type `P`.

Try using `exact` to prove `True`:
-/

example : True := by sorry

/-
`False` on the other hand, can't be proved, because we can't build a value belonging to its type (we saw above that it has no constructors). `False` represents the empty set. Prositions that can not be proved are equivalent to `False`.

## Logical connectives

We can build larger and more interesting propositions out of existing ones using *logical connectives*. In this tutorial we'll study the connectives `→`, `∧`, `∨` and their associated tactics.

Logical connectives form compound propositions; the *structure* of a compound proposition arises from which connectives appear where and it conveys the tactics required to build its proof.

Each logical connective is characterized by its own *introduction* and *elimination* rules:
* Introduction rules allow us to *build* proofs of the compound proposition
* Elimination rules allow us to *destruct* the compound proposition when it is an assumption to prove something else.

### Implication

The first operation we see is the implication, written `→`.
The proposition `P → Q` states that if `P` holds, then `Q` also holds.
We refer to `P` as the *antecedent* and `Q` as the *consequent* of the implication.

When the goal is `P → Q`, we can use the tactic `intro`, which moves the `P` from the goal into the proof context and transforms the goal to `Q`. This is the introduction rule of implication.

After this move we can work with the assumption `p : P` to build a proof of `Q`. We can use `exact` if we can come up with a value that promptly proves `Q`. Try it now:
-/

example {P : Prop} : P → P := by sorry

/-
A goal composed of iterated implications gives you as many hypotheses to work with as there are arrows. This behaviour follows from the fact that the implication operator `→` is right-associative. You can introduce these hypotheses and name their proof objects however you like by specifying their names after `intro`, as in `intro p q r`. Try it:
-/

example {P Q R S T : Prop} : P → S → R → T → Q → R := by sorry

/-
When we have an implication `h : P → Q` as an hypothesis and the goal asks us to prove `Q`, we can *apply* `h` to the goal, transforming it to `P`. This is the first elimination rule of implication which lets us reason backwards, from the consequence to the premise. If we then have `P` in our context, `exact p` will solve the goal and we're done.

There's also the tactic `assumption`, which closes the goal automatically when one of the hyposetheses exactly matches the goal. Try using either strategy in the following exercise:
-/

example {P Q : Prop} : P → (P → Q) → Q := by sorry

/-
We can also apply an implication `h : P → Q` in our context to another object `p : P` in the context, resulting in a new proposition of type `Q`. This second form of elimination rule of implication enables *forward reasoning*, exploiting the premises at hand to obtain the conclusion.

To give a name to the result of applying `h` to `p`, called `h p`, we can use the tactic `have`.

`have q : Q := h p` lets us refer to `h p` as `q` in the rest of the proof. The `: Q` part is optional and lets us specify the expected type of the expression in the definition; you should include it if it makes your proof easier to read later on. Use `have` to solve this exercise:
-/

example {P Q R S : Prop} : P → (Q → R → S) → (P → Q) → (P → R) → S := by
sorry

/-
### Conjunction

A logical conjunction holds when both of its conjuncts hold. So, when our goal is a conjunction `P ∧ Q`, we are required to prove both of its terms. To do so, we employ `constructor` tactic splits the proof into two sub-goals, a first one that has you prove `P` and a second one that has you prove `Q`. Closing both goals means you have proved the conjunction successfully.
-/

example {P Q : Prop} : P → Q → P ∧ Q := by sorry

/-
Conversely, having a conjuction `h : P ∧ Q` in your context is great, it means you have a proof of both `P` and `Q`, so more material to work with! To access the left proof `p : P` write `h.1`. To access the right proof `q : Q` write `h.2`.
-/

theorem and_true_right {B : Prop} : B ∧ True → B := by sorry

/-
### Disjunction

A logical disjunction holds when either of its alternatives hold. Logical disjunction is *inclusive*, meaning that it still holds when both terms hold.
Proving a disjunction is an easier task than proving a conjunction: to prove `P ∨ Q` it suffices to prove either the left or the right side. If you want to prove `P`, use `left`, where to prove `Q` you use `right`. After finishing either proof you'll have successfully proved `P ∨ Q`. Try using both:
-/

example {P Q : Prop} : (P → P ∨ Q) ∧ (Q → P ∨ Q) := by sorry

/-
On the other hand, exploiting an disjunction `h : P ∨ Q` in our context requires more effort, because it splits your proof into two parallel realities: one where `P` holds and `Q` is missing, and the other where `Q` holds and `P` is missing. In other words, if the goal is `R`, we are asked to prove `P → R` and `Q → R` separately.

The tactic `cases` enters such proof state. It takes as argument the hypothesis to destruct into its cases, `cases h`. First it asks you prove the first sub-goal where you have `p : P`, then Lean automatically switches the context to the second sub-goal where you have `q : Q`.

Note: `cases` has the drawback that it chooses the names of the new objects automatically; these might not suit your naming conventions and could probably hurt the readibility of your proof!

The tactic `rcases` ("recursive cases") is a better tool most of the time because it lets us specify a pattern by which to name the objects introduced in each alternative case. To destruct and assign names to the cases of a disjunction `h : P ∨ Q`, we write `rcases h with p | q` where `p | q` is the pattern.
-/

theorem or_symm {P Q : Prop} : P ∨ Q → Q ∨ P := by sorry

/-
### Co-implication

`P ↔ Q` is defined in Lean and in logic as `(P → Q) ∨ (Q → P)`. It asserts that an implication that holds in both directions. This definition establishes a *logical equivalence* among `P` and `Q`: if `P` holds, then `Q` holds and vice versa. Being a conjunction under the hood, to prove a proposition `P ↔ Q` we reuse the introduction rule of conjuction, therefore we must prove both of its sides using `constructor`. Try it now:
-/

example {P : Prop} : P ↔ P := by sorry

/-
Conversely, having a `p : P ↔ Q` in your assumptions means that you can obtain a proof for `Q` from one of `P` and vice versa, depending on the context at hand of course. The elimination rules for conjunction apply here too: given the proof of a co-implication `h`, you can access its left side with `h.1` and its right side with `h.2`.
-/

example {A B : Prop} (a : A) : (B ↔ A) → B := by sorry

/-
### Exercises

Solve the exercises below with the tactics we've introduced in this lesson.
-/

-- Does the opposite implication hold?
example {P Q : Prop} : P ∧ Q → P ∨ Q := by sorry


theorem arg_swap_left {P Q R : Prop} : (P → Q → R) → (Q → P → R) := by sorry

theorem arg_swap_right {P Q R : Prop} : (Q → P → R) → (P → Q → R) := by sorry

-- In the proof of this equivalence, you should reuse the previous two via `exact`.
theorem arg_swap {P Q R : Prop} : (Q → P → R) ↔ (P → Q → R) := by sorry


theorem conj_universal {P Q R : Prop} : (R → P ∧ Q) ↔ (R → P) ∧ (R → Q) := by sorry

theorem disj_universal {P Q R : Prop} : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by sorry


theorem or_associative {P Q : Prop} : P ∧ Q → P ∨ Q := by sorry


theorem and_or_distributivity {P Q R : Prop} : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by sorry
