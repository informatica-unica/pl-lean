import PL_Lean.PL06_Poly

/-
# Exercises on polymorphic functions
-/

section Exercises


section Type_reconstruction

/-
## Exercise: type reconstruction (difficulty: 1-2/4)

Define functions with the given types.  There may be several correct solutions.
Here it is not important that your functions do something useful: you just need
to respect the types.
-/

example {A : Type} : A → List A :=
  sorry

example {A : Type} : List A → Option A :=
  sorry

example {A : Type} {B : Type} : (A → B) → Option A → Option B :=
  sorry

example {A : Type} {B : Type} : (A → B) → List A → List B :=
  sorry

example {A : Type} {B : Type} : List (A × B) → List A :=
  sorry

example {A B : Type} : List A → List B → List (A × B) :=
  sorry

example {A : Type} : List A -> List (A ⊕ A) :=
  sorry


end Type_reconstruction



section Properties_of_map

/-
## Properties of `mapL`
-/

/- __Exercise (difficulty: 1/4)__ Mapping the identity leaves a list unchanged. -/

theorem mapL_identity {A : Type} (xs : List A) :
    mapL (fun x => x) xs = xs := by
  sorry


/- __Exercise (difficulty: 2/4)__ Mapping preserves the length of a list. -/

theorem lengthL_mapL {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    lengthL (mapL f xs) = lengthL xs := by
  sorry


/- __Exercise (difficulty: 2/4)__ Mapping over an append is equivalent to
mapping over the two lists separately and then appending the results. -/

theorem mapL_appendL {A : Type} {B : Type}
    (f : A → B) (xs ys : List A) :
    mapL f (appendL xs ys) = appendL (mapL f xs) (mapL f ys) := by
  sorry


/- __Exercise (difficulty: 2/4)__ Mapping twice can be replaced by mapping the
composition of the two functions once. -/

theorem mapL_composition {A : Type} {B : Type} {γ : Type}
    (f : B → γ) (g : A → B) (xs : List A) :
    mapL f (mapL g xs) = mapL (fun x => f (g x)) xs := by
  sorry


end Properties_of_map



section Properties_of_filter

/-
## Properties of `filterL`
-/

/- __Exercise (difficulty: 2/4)__ Prove the two extreme behaviours of
`filterL`: an always-true predicate preserves every element, while an
always-false predicate removes every element. -/

theorem filterL_true {A : Type} (xs : List A) :
    filterL (fun _ => true) xs = xs := by
  sorry

theorem filterL_false {A : Type} (xs : List A) :
    filterL (fun _ => false) xs = [] := by
  sorry


/- __Exercise (difficulty: 3/4)__ Filtering an appended list is equivalent to
filtering each part separately and appending the results. -/

theorem filterL_appendL {A : Type}
    (p : A → Bool) (xs ys : List A) :
    filterL p (appendL xs ys) =
      appendL (filterL p xs) (filterL p ys) := by
  sorry


end Properties_of_filter



section Properties_of_fold


/- __Exercise (difficulty: 2/4)__ Define list append using `foldRightL`. -/

def appendWithFold {A : Type} (xs ys : List A) : List A :=
  sorry

example : appendWithFold [1, 2] [3, 4] = [1, 2, 3, 4] := by sorry


/- __Exercise (difficulty: 4/4, optional)__ Prove that `mapFold` is equivalent to `mapL`. -/

theorem mapWithFold_equiv_mapL {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    mapFold f xs = mapL f xs := by
  sorry

end Properties_of_fold



section Reversing_lists

/-
## Reversing a list

To reverse a non-empty list, we reverse its tail and append the original head at the end.
-/

def reverseL {A : Type} : List A → List A
  | []      => []
  | x :: xs => appendL (reverseL xs) [x]

example : reverseL ([1, 2, 3, 4] : List Nat) = [4, 3, 2, 1] := by rfl
example : reverseL ([] : List Bool) = [] := by rfl


/- __Exercise (difficulty: 2/4)__ Prove that reversing preserves length.  The
proof uses the previously established theorem `lengthL_appendL`. -/

theorem lengthL_reverseL {A : Type} (xs : List A) :
    lengthL (reverseL xs) = lengthL xs := by
  sorry


/-
In Checkpoint 9 we observed that a function of type
`{A : Type} → List A → List A` can only rearrange, drop, or duplicate the
elements it receives, because it cannot look inside them.  Therefore such a
function must *commute* with `mapL`: it should not matter whether we first
transform every element and then rearrange the list, or first rearrange the
list and then transform the elements.
-/

/- __Exercise (difficulty: 2/4)__ Prove that `reverseL` commutes with `mapL`.
Hint: induction on `xs`; in the inductive case use `mapL_appendL`.  After
rewriting, the two sides differ only by a computation that `rfl` can
perform. -/

theorem mapL_reverseL {A : Type} {B : Type} (f : A → B) (xs : List A) :
    mapL f (reverseL xs) = reverseL (mapL f xs) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Prove how `reverseL` interacts with append.
The order of the two lists is reversed. -/

theorem reverseL_appendL {A : Type} (xs ys : List A) :
    reverseL (appendL xs ys) = appendL (reverseL ys) (reverseL xs) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Prove that reversing twice returns the
original list.  Use `reverseL_appendL` in the inductive case. -/

theorem reverseL_twice {A : Type} (xs : List A) :
    reverseL (reverseL xs) = xs := by
  sorry

end Reversing_lists



section Fold_left

/-
## Exercise: Fold left

The combinator `foldLeftL` can be informally defined as follows:

    foldLeftL f init [] = init
    foldLeftL f init [x₁] = f init x₁
    foldLeftL f init [x₁, x₂] = f (f init x₁) x₂
    foldLeftL f init [x₁, x₂, x₃] = f (f (f init x₁) x₂) x₃
    ...
-/

/- __Exercise (difficulty: 1/4)__ Define the function `foldLeftL`. -/

def foldLeftL {A : Type} {B : Type} (f : A → B → A) (init : A) : List B → A :=
  sorry

example : foldLeftL Nat.add 0 [1,2,3] = 6 := by sorry

/-
Note that the fold right and the fold left combinators yield the same result when
the combining function f is associative, and init is a (left and right) identity of f.

For instance, they would associate the addition operator on the list `[1,2,3]` as follows:

  foldRightL Nat.add 0 [1,2,3] = 1 + (2 + (3 + 0) ) = 6
  foldLeftL  Nat.add 0 [1,2,3] = ((0 + 1) + 2) + 3 = 6

Since addition is associative and 0 is its neutral element, the result is the same.
When the combining function is not associative, we can obtain different results:
-/

example : foldRightL Nat.sub 0 [1,2,3] = 1 := by rfl
example : foldLeftL  Nat.sub 0 [1,2,3] = 0 := by sorry

/-
This is because:

  foldRightL Nat.sub 0 [1,2,3] = 1 - (2 - (3 - 0) ) = 1 - (2 - 3) = 1 - 0 = 1
  foldLeftL  Nat.sub 0 [1,2,3] = ((0 - 1) - 2) - 3 = (0 - 2) - 3 = 0 - 3 = 0
-/

/- __Exercise (difficulty: 2/4)__ Formalize a theorem saying that `foldRightL`
and `foldLeftL` are equivalent whenever the function `f` is associative and `init`
is a left and right identity of `f`. Then, prove it (here you can use generative AI).
-/

end Fold_left



section Zipping

/-
## Exercise: zipping lists (difficulty: 2/4)

Define `zipL`, which combines corresponding elements of two lists into pairs.
Stop as soon as either input list ends.
-/

def zipL {A : Type} {B : Type} : List A → List B → List (A × B) :=
  sorry

example : zipL [1, 2, 3] [true, false, true] =
    [(1, true), (2, false), (3, true)] := by
  sorry

example : zipL [1, 2, 3] [true] = [(1, true)] := by sorry


/- __Exercise (difficulty: 2/4)__ Define `unzipL`, which separates a list of
pairs into a pair of lists. -/

def unzipL {A : Type} {B : Type} :
    List (A × B) → List A × List B :=
  sorry

example : unzipL [(1, true), (2, false)] = ([1, 2], [true, false]) := by
  sorry


/- __Exercise (difficulty: 3/4)__ Prove that unzipping after zipping recovers
both lists when they have the same recursive shape.  Using the same list of
pairs avoids the unequal-length case of `zipL`. -/

theorem unzipL_map_pair {A : Type} {B : Type}
    (f : A → B) (xs : List A) :
    unzipL (mapL (fun x => (x, f x)) xs) = (xs, mapL f xs) := by
  sorry

end Zipping



section Optional_lists

/-
## Exercise: a list of optional results (difficulty: 2/4)

Define a function that turns a `List (Option A)` into an `Option (List A)`.
It succeeds only when every element is `some`.
-/

def collectOptionsL {A : Type} : List (Option A) → Option (List A) :=
  sorry

example : collectOptionsL [some 1, some 2, some 3] = some [1, 2, 3] := by sorry
example : collectOptionsL [some 1, none, some 3] = none := by sorry


/- __Exercise (difficulty: 3/4)__ Prove that a list made entirely of `some`
values is collected successfully. -/

theorem collectOptionsL_map_some {A : Type} (xs : List A) :
    collectOptionsL (mapL some xs) = some xs := by
  sorry

end Optional_lists



section Searching

/-
## Exercise: searching a list (difficulty: 2/4)

Define `findL p xs`, which returns the first element satisfying `p`, or `none`
if no element satisfies the predicate.
-/

def findL {A : Type} (p : A → Bool) : List A → Option A :=
  sorry

example : findL (fun n : Nat => decide (n > 3)) [1, 5, 4, 8] = some 5 := by sorry
example : findL (fun n : Nat => decide (n > 9)) [1, 5, 4, 8] = none   := by sorry


/- __Exercise (difficulty: 3/4)__ If the predicate is always false, `findL`
always returns `none`. -/

theorem findL_false {A : Type} (xs : List A) :
    findL (fun _ => false) xs = none := by
  sorry


end Searching


end Exercises
