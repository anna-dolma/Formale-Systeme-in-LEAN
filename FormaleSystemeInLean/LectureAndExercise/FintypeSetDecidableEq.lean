import FormaleSystemeInLean.LectureAndExercise.Powertype

/-!
Given a type α with decidable equality and a Fintype instance T (which means that there are only finitely many αs),
we can prove that equality is also decidable for Set α. A typeclass instance for this is needed for the powerset construction in lecture 4.
-/

/-- Two lists with the same elements (ignoring order and duplicates) map to the same set via List.toSet. -/
theorem toSet_eq_iff_lists_have_same_members (X Y : Set α) (l k : List α) : l.toSet = X → k.toSet = Y → ((∀ a, a ∈ l ↔ a ∈ k) ↔ X = Y) := by
  intro X_eq Y_eq
  unfold List.toSet at *
  constructor
  . intro mem_iff
    apply Set.ext
    intro x
    constructor
    . intro x_mem
      rw [← X_eq] at x_mem
      rw [← Y_eq]
      simp only [Membership.mem] at *
      specialize mem_iff x
      apply mem_iff.mp x_mem
    . intro x_mem
      rw [← Y_eq] at x_mem
      rw [← X_eq]
      simp only [Membership.mem] at *
      specialize mem_iff x
      apply mem_iff.mpr x_mem
  . intro xy_eq
    intro x
    rw [← X_eq, ← Y_eq] at xy_eq
    grind

/--
If α is a finite type and membership is decidable for every Set α then two sets X and Y are equal iff their corresponding lists have the same members.
We need to assume (DecidablePred S) for every (S : Set α) in order to obtain a list with the same elements as S by filtering Fintype.elems for members of S.
-/
theorem set_eq_iff_filter_has_same_members (α : Type u) (h : ∀ (S : Set α), DecidablePred S) (T : Fintype α) (X Y : Set α) : X = Y ↔ (∀ a, a ∈ T.elems.filter ( · ∈ X) ↔ a ∈ T.elems.filter ( · ∈ Y)) := by
  constructor
  . intro xy_eq
    intro x
    simp only [List.mem_filter, decide_eq_true_eq, and_congr_right_iff]
    intro x_mem
    rw [xy_eq]
  . intro h
    simp only [List.mem_filter, decide_eq_true_eq, and_congr_right_iff] at h
    apply Set.ext
    intro x
    have x_mem_elems := T.complete x
    apply h x x_mem_elems

/--
If α is a finite type and membership is decidable for every Set α then two sets X and Y are equal iff their corresponding lists are equal.
We need to assume (DecidablePred S) for every (S : Set α) in order to obtain a list with the same elements as S by filtering Fintype.elems for members of S.
-/
theorem set_eq_iff_filter_eq (α : Type u) (h : ∀ (S : Set α), DecidablePred S) (T : Fintype α) (X Y : Set α) : X = Y ↔ T.elems.filter ( · ∈ X) = T.elems.filter ( · ∈ Y) := by
  constructor
  . intro eq
    rw [eq]
  . intro eq
    apply Set.ext
    intro x
    constructor
    . intro x_mem
      have x_mem_filter : x ∈ T.elems.filter ( · ∈ X ) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        . apply T.complete x
        . exact x_mem
      rw [eq] at x_mem_filter
      grind
    . intro x_mem
      have x_mem_filter : x ∈ T.elems.filter ( · ∈ Y ) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        . apply T.complete x
        . exact x_mem
      rw [← eq] at x_mem_filter
      grind

instance {α : Type u} [T : Fintype α] [DecidableEq α] [h : ∀ (S : Set α), DecidablePred S] : DecidableEq (Set α) := by
  intro X Y
  have aux := set_eq_iff_filter_eq α h T X Y
  simp only [aux]
  by_cases h : List.filter (fun x => decide (x ∈ X)) Fintype.elems
    = List.filter (fun x => decide (x ∈ Y)) Fintype.elems
  . apply isTrue h
  . apply isFalse h
