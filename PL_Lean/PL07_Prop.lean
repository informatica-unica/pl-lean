set_option autoImplicit false

/-
# Propositional logic and the Curry–Howard isomorphism

In the previous lectures we wrote *programs* as functions between given types.
In this lecture we write *proofs*, and we discover that the two activities are equivalent:

    a proposition is a type, and a proof of a proposition is a program of that type.

This observation is the **Curry–Howard isomorphism**.

This is the foundation of Lean and of every proof assistant based on type theory.

Here is the correspondence that we will build, one row at a time:

    Logic                 Types (programs)             Lean
    --------------------  ---------------------------  ---------------------------
    P → Q   (implies)     A → B     (functions)        P → Q
    P ∧ Q   (and)         A × B     (pairs)            P ∧ Q
    P ∨ Q   (or)          A ⊕ B     (tagged unions)    P ∨ Q
    True                  Unit                         True
    False                 Empty                        False
    ¬P      (not)         A → Empty                    ¬P   (i.e., P → False)
    P ↔ Q   (iff)         (A → B) × (B → A)            P ↔ Q

By the end of the lecture, you should be able to:

* understand what `p : P` means when `P` is a proposition;
* prove propositional tautologies in **tactic mode** and in **term mode**, and
  translate a proof from one mode to the other;
* explain why both modes produce the same object;
* state the Curry–Howard dictionary (implication, conjunction, disjunction, falsity,
  negation) and relate it to the typing rules `T-Abs`, `T-App`, `T-Pair`, `T-Proj`,
  `T-Inl`, `T-Inr`, `T-Case` of the theory lectures;
* decide whether a propositional formula is provable *constructively* by asking
  whether you can write a program of the corresponding type.

Exercise difficulties use the same relative scale as in previous lectures:

* **1/4:** one direct idea;
* **2/4:** two ideas must be combined;
* **3/4:** a more substantial construction or proof;
* **4/4:** an optional challenge.

You find additional extended exercises in the file `PL07_PropEx.lean`.

A peculiarity of this lab lecture is:

    **Every theorem is proved twice: once in tactic mode, once in term mode.**

Writing both versions is what makes the Curry–Howard isomorphism visible.  Exercises
therefore come in pairs, with names ending in `_tac` and `_term`.  After solving a
pair, run `#print` on both names and compare what Lean shows you.

Whenever the cursor is inside a tactic proof, the infoview shows the *proof state*:

    P Q : Prop
    h : P ∧ Q
    ⊢ Q ∧ P

Above the turnstile `⊢` are the **hypotheses** (the typing context Γ of the theory
lectures); below it is the **goal** (the type that we must inhabit).  A tactic
transforms the proof state; the proof is finished when there are no goals left.
In the comments of this file we write a proof state on one line as
`h : P ∧ Q ⊢ Q ∧ P`.
-/

section Types_and_proofs

/-
## Types and proofs

So far, the notation `e : T` has expressed that a *term* `e` has a *type* `T`:

    5 : Nat          true : Bool          [1, 2, 3] : List Nat

In Lean, the same notation has a logical meaning:

* a **proposition** is a type `P` whose kind is `Prop`;
* a **proof** of `P` is a term `p` of type `P`.  Read `p : P` as "`p` is a proof of `P`".
-/

#check Prop
#check (2 + 2 = 4)          -- a proposition: it is a type, of kind Prop
#check (rfl : 2 + 2 = 4)    -- a proof of that proposition

/-
In Lean, the command `theorem` is used to define terms typed as propositions
while terms with any type can be defined with the command `def`.
-/

theorem two_plus_two : 2 + 2 = 4 := rfl   -- accepted
-- theorem three : Nat := 3               -- rejected, since `Nat` is not a proposition.

/-
The correspondence between programs and logic is summarised as follows:

    Programming          Logic
    ------------------   --------------------------
    type  `A : Type`     proposition  `P : Prop`
    term  `a : A`        proof  `p : P`
    writing a program    proving a theorem
-/


/-
__Checkpoint 1__  Which of the following examples is a *proof* and which is a *program*?
Is `2 + 2 = 5` a proposition?  Can you prove it?
-/

example : 2 + 2 = 4 := rfl
example : Nat := 2 + 2
example : Bool := true

/-
__Checkpoint 2__  Predict the types of the following three expressions,
then check them.  Which familiar functions are they?  Notice that the second and
third mention `Prop` in the binder: they are *polymorphic* in a proposition `P`,
exactly like the polymorphic functions of the previous lab were polymorphic in a type.
-/

#check (fun {A : Type} (a : A) => a)
#check (fun {P : Prop} (p : P) => p)
#check (fun {A B : Type} (a : A) (_ : B) => a)
#check (fun {P Q : Prop} (p : P) (_ : Q) => p)


end Types_and_proofs



section Implication

/-
## Implication

The constructive interpretation of implication is:

    a proof of `P → Q` is a function that transforms any proof of `P` into a proof of `Q`.

So a proof of an implication is literally a function, and *using* an implication
is *function application*.  There are two ways to write such a function in Lean:

* **term mode**:    write the function, `:= fun p => ...`;
* **tactic mode**:  write `:= by` followed by a list of tactics, and Lean builds the
  function for us.

Let us start by considering the implication

    A → A

In term mode, an inhabitant of this type is the identity function:
-/

def id_term_data {A : Type} : A → A :=
  fun a => a

/-
When interpreting the type A → A as a logic proposition, it turns out to be a tautology:

    P → P

The code is identical: only the types change (`Type` vs. `Prop`).
-/
theorem id_term {P : Prop} : P → P :=
  fun p => p

/-
Also in tactic mode, the two proofs are identical:
-/

def id_tac_data {A : Type} : A → A := by
  intro a        -- a : A ⊢ A
  exact a

theorem id_tac {P : Prop} : P → P := by
  intro p        -- p : P ⊢ P
  exact p

/-
Two tactics are enough for implication:

* `intro x` — the goal is `A → B`; assume `x : A` and continue with the goal `B`.
  This is the lambda: it builds `fun x => ?`.
* `exact h` — the term `h` has exactly the type of the goal: close the goal with it.
-/


/- Now consider the type:

    A → (B → A)

  Functions inhabiting this type take an input of type A, and output a function in B → A.
  Equivalently, they take an input of type A, then another input of type B, and output
  a value of type A.

  Such function can be defined in various equivalent ways:
-/

def k_term_data {A B : Type} : A → B → A :=
  fun (a : A) => fun (_b : B) => a

def k_term_data₂ {A B : Type} : A → B → A :=
  fun (a : A) (_b : B) => a

def k_term_data₃ {A B : Type} : A → B → A :=
  fun a _ => a

/-
When interpreting the type A → B → A as a logic proposition, it turns out again
to be a tautology, known as the **K combinator**:

    P → (Q → P)

As before, we can prove such proposition by using the same term:
-/

theorem k_term {P Q : Prop} : P → Q → P :=
  fun p => fun _ => p

/-
__Checkpoint 3__  Prove the K combinator in tactic mode.
(Hint: after `intro p q`, one of the two hypotheses is useless.)
-/

theorem k_tac {P Q : Prop} : P → Q → P := by
  sorry


/-
Now consider the type:

  (A → B) → (B → C) → A → C

Terms of this type are functions that take two inputs: a function `f` in A → B and
a function `g` in B → C, and return a function in A → C. We have already seen that
this is exactly the behaviour of function composition:
-/

def imp_trans_term_data {A B C : Type} (f : A → B) (g : B → C) : A → C :=
  g ∘ f

/- Or, equivalently: -/

def imp_trans_term_data₂ {A B C : Type} : (A → B) → (B → C) → A → C :=
  fun f g a => g (f a)

/-
In logic, the type above is a proposition stating that implication is transitive:

  (P → Q) → (Q → R) → P → R

In term mode, we can prove such proposition exactly as before:
-/

theorem imp_trans_term {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  fun f g p => g (f p)

/-
In tactic mode, we start by introducing `f`, `g`, and `p`. We then use `apply`,
which reasons *backwards*: we reduce the goal `R` into `Q` by applying `g : Q → R`.
Then, we reduce the new goal `Q` into `P` by applying `f : P → Q`.
Now the goal is `P`, which is exactly one of the hypotheses in the context.
-/

theorem imp_trans_tac {P Q R : Prop} : (P → Q) → (Q → R) → P → R := by
  intro f g p      -- f : P → Q,  g : Q → R,  p : P  ⊢ R
  apply g          -- ⊢ Q     (goal R, and g : Q → R)
  apply f          -- ⊢ P     (goal Q, and f : P → Q)
  exact p          -- p : P


/-
The tactics and the terms correspond as follows.

    Tactic        Term                      Rule of the lambda-calculus
    ------------  ------------------------  ---------------------------
    intro x       fun x => ...              T-Abs
    exact h       h                         T-Var
    apply f       f ?                       T-App (read backwards)
-/


/-
## Exercise: Modus Ponens (difficulty: 1/4)

Consider the type:

    A → (A → B) → B

It is inhabited by functions that take as input an element `a : A` and a function
`f : A → B`, and return an element of type `B`. Constructing such term is easy.
-/

theorem mp_term_data {A B : Prop} : A → (A → B) → B :=
  sorry

/-
In logic, the type above is a proposition known as **modus ponens**:

    P → (P → Q) → Q

From a proof of `P` and a proof of `P → Q`, obtain a proof of `Q`.
Write proofs (both in term mode and tactic mode) for it.
-/

theorem mp_term {P Q : Prop} : P → (P → Q) → Q :=
  sorry

theorem mp_tac {P Q : Prop} : P → (P → Q) → Q := by
  sorry


end Implication



section Conjunction

/-
## Conjunction

The constructive interpretation of conjunction is:

    a proof of `P ∧ Q` is a pair `⟨p, q⟩` where `p` is a proof of `P` and `q` is a proof of `Q`.

This means that **proving** a conjunction is similar to witnessing an element in a
product type `A × B`:

* **term mode**:    write the pair `⟨p,q⟩`;
* **tactic mode**:  split the proof in two cases with `constructor`, and then we prove
separately `p` and `q`.

Symmetrically, **using** a conjunction `h` in the proof context is similar to projecting
the elements of a pair in a product type:

* **term mode**:    write the projections `h.1` or `h.2`;
* **tactic mode**:  extract the two conjuncts with `rcases h with ⟨p,q⟩`.

Let us start by considering the implication

    A × B → A

We prove it first on data and then on propositions, both in term and in tactic mode.
-/

def fst_term {A B : Type} : A × B → A :=
  fun p => p.1

/- or, equivalently: -/
def fst_term₂ {A B : Type} : A × B → A :=
  fun (a, _) => a

/-
A note on angle brackets `⟨` and `⟩` (typed `\<` and `\>`).

If an inductive type has exactly one constructor (for instance, any `structure`), Lean
lets us build its terms without writing the name of the constructor, using the
*anonymous constructor* notation `⟨ ... ⟩`. For example:

* The product `A × B` is notation for `Prod A B`, a structure whose single constructor
  `Prod.mk` takes two arguments.  Hence `⟨a, b⟩ : A × B` means `Prod.mk a b`, which is
  also written `(a, b)`.
* The conjunction `P ∧ Q` is a structure `And P Q` whose single constructor `And.intro`
  takes a proof of `P` and a proof of `Q`.  Hence `⟨p, q⟩ : P ∧ Q` means `And.intro p q`.

Therefore, we can rewrite the previous proof using angle brackets:
 -/

def fst_term₃ {A B : Type} : A × B → A :=
  fun ⟨a, _⟩ => a

/- The same proofs for propositions. `Type` becomes `Prop`, `×` becomes `∧`. -/

theorem and_left_term {P Q : Prop} : P ∧ Q → P :=
  fun h => h.1

theorem and_left_term₂ {P Q : Prop} : P ∧ Q → P :=
  fun ⟨p, _⟩ => p

/-
In tactic mode, extracting the elements of a pair can be done with `rcases`:
-/

def fst_tac {A B : Type} : A × B → A := by
  intro p
  rcases p with ⟨a, _⟩
  exact a

/- The same proof for propositions. -/

theorem and_left_tac {P Q : Prop} : P ∧ Q → P := by
  intro h
  rcases h with ⟨p, _⟩
  exact p


/-
Now let us use `#print` to look at what these proofs really are. For Lean, a proof is always a *term*, even when you wrote it in tactic mode.
-/

#print and_left_tac
#print and_left_term

/-
This is a key point: a tactic proof is just a recipe that builds a term.
When the tactics have finished, Lean checks the resulting term with its
core trusted kernel, exactly as it does for a proof written directly in term mode.
-/


/-
__Checkpoint 4__  The two proofs `and_left_tac` and `and_left_term` look different.
Do you expect Lean to accept the following claim, which says that they are *equal*?
And what about the second and the third claims?
-/

-- example : @and_left_tac = @and_left_term := rfl
-- example (a b : Nat) : a = b := rfl
-- example : @fst_term = @fst_tac := rfl

/-
The first claim is accepted. Indeed, Lean treats all proofs of the same proposition as
definitionally equal (this is called *proof irrelevance*): for a proposition, it does not
matter *how* it was proved, only *that* it was proved.  So the tactic proof and the term
proof are, for Lean, the same object.

The second claim is (of course) rejected: two arbitrary numbers are not always equal.

The third claim is accepted, but not because of proof irrelevance: `A × B` is a type of data, not a proposition.  It is accepted because the two functions are *definitionally* equal. Unfolding the definitions, `rcases` produces `Prod.casesOn p (fun a _ => a)`, and Lean reduces this to `p.1` using *structure eta*: a pair `p` is definitionally equal to the
pair `(p.1, p.2)` of its projections.  For data, `rfl` succeeds only when equality can be
checked by unfolding and computation, which is stronger than "computing the same result
on every input".
-/


/-
Now consider the type:

  (A × B) → (B × A)

Terms of this type are functions that take as input a pair of type `A × B` and return
a swapped pair of type `B × A`. We already know how to write such function:
-/

def prod_swap_term {A B : Type} : A × B → B × A :=
  fun h => ⟨h.2, h.1⟩

/-
In tactic mode, we give two alternative proofs.
In the first proof, we extract the pair components, and then we split the goal
into two cases using `constructor`.
In the second proof, we use `exact` to provide directly a term with the expected type.
-/

def prod_swap_tac {A B : Type} : A × B → B × A := by
  intro h
  rcases h with ⟨a, b⟩   -- a : A, b : B ⊢ B ∧ A
  constructor
  . exact b
  . exact a

def prod_swap_tac₂ {A B : Type} : A × B → B × A := by
  intro h
  rcases h with ⟨a, b⟩   -- a : A, b : B ⊢ B ∧ A
  exact ⟨b,a⟩

/-
__Checkpoint 5__ Check that the same proofs hold when switching from types to propositions.
-/

theorem and_swap_term {P Q : Prop} : P ∧ Q → Q ∧ P :=
  sorry

theorem and_swap_tac {P Q : Prop} : P ∧ Q → Q ∧ P := by
  sorry


/- ## Exercise: Currying and uncurrying (difficulty: 2/4)

Prove the logical equivalent of currying/uncurring in types, both in tactic mode and in term mode.
Hint: to use a hypothesis `f : P ∧ Q → R` you must first build a proof of `P ∧ Q`;
to use `h : P ∧ Q` as a function argument, take its components `h.1` and `h.2`. -/

theorem curry_tac {P Q R : Prop} : (P ∧ Q → R) → P → Q → R := by
  sorry

theorem curry_term {P Q R : Prop} : (P ∧ Q → R) → P → Q → R :=
  sorry

theorem uncurry_tac {P Q R : Prop} : (P → Q → R) → P ∧ Q → R := by
  sorry

theorem uncurry_term {P Q R : Prop} : (P → Q → R) → P ∧ Q → R :=
  sorry

end Conjunction



section Disjunction

/-
## Disjunction

The constructive interpretation of disjunction is:

    a proof of `P ∨ Q` is either a proof of `P` or a proof of `Q`, tagged with the information of which one it is.

The tags are the two constructors `Or.inl p` and `Or.inr q`.

This means that **proving** a disjunction is similar to witnessing an element in a
sum type `A ⊕ B`:

* **term mode**:    use type constructors `Sum.inl` and `Sum.inr`;
* **tactic mode**:  use tactic `left` to prove `P`, or tactic `right` to prove `Q`.

Symmetrically, **using** a disjunction `h` in the proof context is similar to case
analysis:

* **term mode**:    `match h with | ...`;
* **tactic mode**:  `rcases h with p | q`.

Let us start by considering the implication

    A ⊕ B → B ⊕ A

We prove it first on data and then on propositions, both in term and in tactic mode.
-/

def sum_swap_term {A B : Type} : A ⊕ B → B ⊕ A :=
  fun s => match s with
  | .inl a => .inr a      -- implicit constructor Sum
  | .inr b => .inl b

/- The same proof term can be used to prove the corresponding proposition: -/
theorem or_swap_term {P Q : Prop} : P ∨ Q → Q ∨ P :=
  fun s => match s with
  | .inl p => .inr p      -- implicit constructor Or
  | .inr q => .inl q

/- In tactic mode, we prove either the left or the right branch of `B ⊕ A`.
   The actual case depends on which case holds in the hypothesis `B ⊕ A`. -/
def sum_swap_tac {A B : Type} : A ⊕ B → B ⊕ A := by
  intro s
  rcases s with a | b
  . right
    exact a
  . left
    exact b

/- The same tactic can be used to prove the corresponding proposition: -/
theorem or_swap_tac {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro h              -- h : P ∨ Q ⊢ Q ∨ P
  rcases h with p | q  -- two goals:  p : P ⊢ Q ∨ P   and   q : Q ⊢ Q ∨ P
  · right              -- ⊢ P
    exact p
  · left               -- ⊢ Q
    exact q


/-
__Checkpoint 6__  In `or_swap_tac`, put the cursor after the line
`rcases h with p | q` and read the infoview.  How many goals are there?
Which hypotheses does each goal have?  Why a disjunction cannot be used to prove
something that needs both `p` and `q`?
-/


/-
__Checkpoint 7__  Decide, without trying, which of the following are provable.
Ask yourself for each one: *can I write a total function of this type?*
(Think of what the function receives as input, and which values it can build.)

    (a)  P ∧ Q → P
    (b)  P ∨ Q → P
    (c)  P → P ∨ Q
    (d)  P → P ∧ Q
    (e)  P ∧ Q → P ∨ Q
    (f)  P ∨ Q → P ∧ Q
-/


/- ## Exercise: Elimination Rule (difficulty: 2/4)__

Prove the *elimination rule* of disjunction: if `P` implies `R` and `Q` implies `R`, then `P ∨ Q` implies `R`.  Tactic proof and term proof.
-/

theorem or_elim_tac {P Q R : Prop} : (P → R) → (Q → R) → P ∨ Q → R := by
  sorry

theorem or_elim_term {P Q R : Prop} : (P → R) → (Q → R) → P ∨ Q → R :=
  sorry

end Disjunction



section Falsity_and_negation

/-
## Falsity and negation

The data type `Empty` is not inhabited: its has no introduction rules.
The elimination rule for the empty type is:

    Empty.elim : Empty → A

meaning that any type A, there is always a function from Empty to A:

In tactic mode, using an hypothesis `h` of type Empty is done by case analysis on `h`.
Since Empty has no constructors, there will be **zero** cases.

The logical correspondent of type `Empty` is `False`, a proposition with no proof.
The elimination rule for `False` is:

    False.elim : False → P

This means that a contradiction proves anything ("ex falso quodlibet").
As for the `Empty` type, a `False` in the context can be eliminated by case analysis.
-/

def empty_elim_term {A : Type} : Empty → A :=
  fun e => Empty.elim e

theorem false_elim_term {P : Prop} : False → P :=
  fun h => False.elim h

def empty_elim_tac {A : Type} : Empty → A := by
  intro e
  cases e

theorem false_elim_tac {P : Prop} : False → P := by
  intro h
  cases h

/-
In constructive logic, negation `¬P` is defined as `P → False`. This holds in Lean too.

So, a proof of `¬P` is a function that transforms any (hypothetical) proof of `P`
into a proof of `False`. To *prove* `¬P` we `intro` a proof of `P` and derive a contradiction. To *use* an hypothesis `h : ¬P` we apply it to a proof of `P`.
-/

example {P : Prop} : (¬P) = (P → False) := rfl

/-
Let us prove that every proposition implies its double negation:

    P → ¬¬P.

By expanding the negation into `P` implies `False`, this becomes:

    P → (P → False) → False

Again we first write the same program on data, replacing `False` by `Empty`.

In term mode, the proof is straightforward.
-/

def not_not_intro_term_data {A : Type} : A → (A → Empty) → Empty :=
  fun a k => k a

theorem not_not_intro_term {P : Prop} : P → ¬¬P :=
  fun p np => np p

/- In tactic mode, the proof is essentially the same. -/

def not_not_intro_tac_data {A : Type} : A → (A → Empty) → Empty := by
  intro a
  intro na
  exact na a

/- Alternatively, you can do backward reasoning with `apply`. -/
def not_not_intro_tac_data₂ {A : Type} : A → (A → Empty) → Empty := by
  intro a
  intro na
  apply na
  exact a

/- The same tactics work when switching from types to propositions. -/
theorem not_not_intro_tac {P : Prop} : P → ¬¬P := by
  intro p       -- p : P ⊢ ¬¬P
  intro np      -- np : ¬P ⊢ False
  exact np p

/-
In words: given a proof `p` of `P`, and a refutation `np` of `P`, we apply the refutation
to the proof, and obtain a contradiction.
-/


/- __Checkpoint 8__  Is the converse, `¬¬P → P`, provable?  Start a proof in tactic mode:

    theorem dne_attempt {P : Prop} : ¬¬P → P := by
      intro h        -- h : ¬¬P ⊢ P
      ...

What goal do you have?  What can you do with `h`?  Why are you stuck?
-/

/- We now prove that from a contradiction, anything follows: `P → ¬P → Q`.  -/

theorem explosion_tac {P Q : Prop} : P → ¬P → Q := by
  intro p np
  have nq : False → Q := by
    intro f
    cases f
  apply nq
  apply np
  exact p

/- In this proof, we have explicitly replaced the goal Q with False, and then we proved
False using the assumptions ¬P and P in the context.

The tactic `contradiction` allows us to prove any goal when ¬P and P are in the context.
-/

theorem explosion_tac_contradiction {P Q : Prop} : P → ¬P → Q := by
  intro p np
  contradiction

/- In term mode, the proof is direct: first obtain `False` by applying `np` to `p`,
and then obtain `Q` by applying `False.elim` to `False` -/
theorem explosion_term {P Q : Prop} : P → ¬P → Q :=
  fun p np => False.elim (np p)


/- ## Exercise: Contrapositive (difficulty: 2/4)

Give tactic proof and term proof of:

    (P → Q) → ¬Q → ¬P
-/

theorem contrapositive_term {P Q : Prop} : (P → Q) → ¬Q → ¬P :=
  sorry

theorem contrapositive_tac {P Q : Prop} : (P → Q) → ¬Q → ¬P := by
  sorry

end Falsity_and_negation


section True

/-
## Unit and True

Type type `Unit` is inhabited by exactly one value, `()`.
-/

def unit_term : Unit := ()

/-
The logical correspondence is with the proposition `True`, which has one canonical proof:

    True.intro : True
-/

theorem true_term : True :=
  True.intro

/- The same proof can be written in tactic mode (we can alternatively use `trivial`). -/
theorem true_tactic : True := by
  exact True.intro

/- We prove that the type:

    A → Unit

  is inhabited by a function that discards the input and returns the Unit value.
-/

def fun_unit_term {A : Type} : A → Unit :=
  fun _ => ()

/- We can similarly prove that `True` follows from any proposition `P`. -/

theorem imp_true_term {P : Prop} : P → True :=
  fun _ => True.intro

/- The corresponding tactic proof introduces the assumption and then ignores it. -/
theorem imp_true_tactic {P : Prop} : P → True := by
  intro _
  trivial

/- __Exercise (difficulty: 1/4__ Prove that `True` is neutral for conjunction.
Conversely, from a proof of `P`, we can construct a proof of `True ∧ P`. -/

theorem true_and_elim {P : Prop} : True ∧ P → P := by
  sorry

theorem true_and_intro {P : Prop} : P → True ∧ P := by
  sorry

end True



section Classical_boundary

/-
## The classical boundary

Several familiar tautologies are **not** provable in the constructive logic that we have
used so far.  Three important ones are:

    P ∨ ¬P                  excluded middle
    ¬¬P → P                 double-negation elimination
    ¬(P ∧ Q) → ¬P ∨ ¬Q      the second De Morgan law

In constructive logic, a proof of `P ∨ ¬P` would have to say *which* side holds, that is, it
would be a program that *decides* an arbitrary proposition `P`.  Such a program does
not exist.  (For `Bool` we can decide by computation, as we did in the first lab: that
is why `b || !b = true` was provable by cases.  For an arbitrary proposition there is
nothing to compute.)

Lean offers classical reasoning as an *axiom*: `Classical.em : ∀ P, P ∨ ¬P`.
Exploiting it we can prove the missing implications:
-/

theorem dne_tac {P : Prop} : ¬¬P → P := by
  intro h
  rcases Classical.em P with p | np
  · exact p
  · exfalso
    exact h np

/-
Lean can tell us which axioms a theorem depends on.  Compare the two commands below:
the constructive theorem should report that it depends on no axioms, while the classical
one mentions the axiom of choice (from which `Classical.em` is derived).
-/

#print axioms and_swap_tac
#print axioms dne_tac


/- __Exercise (difficulty: 3/4)__ Prove the converse of the contrapositive,
`(¬Q → ¬P) → (P → Q)`, which is classical. -/

theorem contrapositive_conv_tac {P Q : Prop} : (¬Q → ¬P) → (P → Q) := by
  sorry

theorem contrapositive_conv_term {P Q : Prop} : (¬Q → ¬P) → (P → Q) :=
  sorry

end Classical_boundary
