import FormaleSystemeInLean.LectureAndExercise.Fintype

set_option linter.unusedSectionVars false

def Set (α : Type u) := α -> Prop

-- The following type class instances are just allowing us to use some basic notation like ∅, ∈ or ∪ with the right definitions..
instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Membership α (Set α) where
  mem S a := S a

instance : Union (Set α) where
  union A B := fun e => e ∈ A ∨ e ∈ B

instance : Inter (Set α) where
  inter A B := fun e => e ∈ A ∧ e ∈ B

instance : HasSubset (Set α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

instance : HasSSubset (Set α) where
  SSubset A B := A ⊆ B ∧ ¬ B ⊆ A

instance : SDiff (Set α) where
  sdiff A B := fun e => e ∈ A ∧ ¬(e ∈ B)

def Set.powerset (α : Type u) (S : Set α) := fun x => x ⊆ S

def Set.map (f : α → β) (S : Set α) [Fintype α] : Set β :=
  fun b => ∃ (a : α), a ∈ S ∧ f a = b

-- Set extensionality: Two sets are equal if they contain the same elements. This is not something we define but we can prove it!
theorem Set.ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
  intro h; apply funext; intro e; apply propext; specialize h e; exact h

theorem Set.not_empty_contains_element (X : Set α) : X ≠ ∅ -> ∃ e, e ∈ X := by
  intro neq
  apply Classical.byContradiction
  intro contra
  apply neq
  apply Set.ext
  intro e
  simp only [not_exists] at contra
  specialize contra e
  simp only [contra, false_iff]
  simp [Membership.mem, EmptyCollection.emptyCollection]

theorem Set.empty_eq (A : Set α) : (∀ (x : α), ¬x ∈ A) -> A = ∅ := by
  intro h
  apply Set.ext
  intro a
  simp only [EmptyCollection.emptyCollection]
  constructor
  . intro e_mem
    simp only [Membership.mem]
    apply h a
    exact e_mem
  . intro e_mem
    simp only [Membership.mem] at e_mem

theorem Set.empty_iff (A : Set α) : A = ∅ ↔ ∀ a, a ∉ A := by
  constructor
  . intro A_eq
    simp only [EmptyCollection.emptyCollection] at *
    intro a
    intro contra
    simp only [A_eq, Membership.mem] at contra
  . intro h
    apply Set.ext
    intro e
    simp only [EmptyCollection.emptyCollection]
    constructor
    . intro e_mem
      simp only [Membership.mem]
      apply h e
      exact e_mem
    . intro e_mem
      simp only [Membership.mem] at e_mem

def Powertype (α : Type u) := Set α

instance : Membership α (Powertype α) where
  mem S a := S a

def List.toSet (l : List α) : Set α := fun e => e ∈ l

def List.power_upto (l : List α) (n : Nat) : List (List α) :=
  let rec loop : Nat → List (List α)
    | 0 => [[]]
    | n+1 => let prev := loop n; prev ++ (prev.flatMap (fun l' => l.map fun e => e:: l'))
  loop n

theorem nil_power (n : Nat) (l : List α) : l = [] -> l.power_upto n = [[]] := by
  intro l_eq
  induction n with
  | zero =>
    unfold List.power_upto List.power_upto.loop
    rfl
  | succ n ih =>
    unfold List.power_upto List.power_upto.loop
    subst l
    simp -- mit was?
    unfold List.power_upto at ih
    rw [ih]
    simp

theorem mem_power_upto_n (T : Fintype α) (l : List α) (n : Nat) : n ≤ T.elems.length → l.length = n → l ∈ T.elems.power_upto n := by
  intro n_le l_len
  cases h : T.elems with
  | nil =>
    rw [nil_power]
    . cases l with
    | nil =>
      grind
    | cons a s =>
      cases n with
      | zero =>
        grind
      | succ n =>
        rw [List.mem_singleton]
        exfalso
        have elems_length : T.elems.length = 0 := by
          rw [List.eq_nil_iff_length_eq_zero] at h
          exact h
        rw [elems_length] at n_le
        contradiction
    . rfl
  | cons b s =>
    induction n generalizing l with
    | zero =>
      unfold List.power_upto List.power_upto.loop
      have l_eq : l = [] := by
        rw [List.eq_nil_iff_length_eq_zero]
        exact l_len
      rw [l_eq]
      grind
    | succ n ih =>
      unfold List.power_upto List.power_upto.loop
      simp
      have l_neq_nil : l ≠ [] := by
        have l_len_gz : l.length > 0 := by
          rw [← Nat.succ_eq_add_one] at l_len
          grind
        rw [List.ne_nil_iff_length_pos]
        exact l_len_gz
      have l_eq : ∃ a l', l = a::l' ∧ l'.length = n := by
        rw [List.ne_nil_iff_exists_cons] at l_neq_nil
        rcases l_neq_nil with ⟨a, l', l_eq⟩
        exists a, l'
        constructor
        . exact l_eq
        . grind
      rcases l_eq with ⟨a, l', l_eq, l'_len⟩
      have aux : n ≤ T.elems.length := by grind
      apply Or.inr
      exists l'
      constructor
      . apply ih l' aux l'_len
      . by_cases ha : a = b
        . apply Or.inl
          rw [← ha]
          exact l_eq
        . apply Or.inr
          exists a
          constructor
          . have a_mem : a ∈ b::s := by
              have complete := T.complete
              specialize complete a
              rw [h] at complete
              exact complete
            grind
          symm
          exact l_eq

theorem inclusion_succ (T : Fintype α) (l : List α) (n : Nat) : l.length ≤ T.elems.length -> l ∈ T.elems.power_upto n -> l ∈ T.elems.power_upto (n+1) := by
  intro l_len l_mem
  unfold List.power_upto List.power_upto.loop
  simp
  apply Or.inl
  exact l_mem

theorem inclusion (T : Fintype α) (l : List α) (n : Nat) (m : Nat) : n ≤ m -> l ∈ T.elems.power_upto n -> l ∈ T.elems.power_upto m := by
  intro le l_mem
  induction le with
  | refl =>
    simp_all
  | @step k b ih =>
    unfold List.power_upto List.power_upto.loop
    simp
    apply Or.inl
    exact ih

theorem powerlist (T : Fintype α) (l : List α) : l.length ≤ T.elems.length -> l ∈ T.elems.power_upto T.elems.length := by
  intro l_len
  cases ht: T.elems with
  | nil =>
    rw [List.eq_nil_iff_length_eq_zero] at ht
    simp only [List.length_nil]
    unfold List.power_upto List.power_upto.loop
    rw [ht, Nat.le_zero, ← List.eq_nil_iff_length_eq_zero] at l_len
    rw [l_len, List.mem_singleton]
  | cons b s =>
    have aux := inclusion_succ T l l.length l_len
    have aux2 := mem_power_upto_n T l l.length l_len rfl
    rw [ht, List.length_cons, Nat.le_add_one_iff] at l_len
    rcases l_len with inl | inr
    . have test := aux aux2
      rw [ht] at test
      rw [List.length_cons]
      have aux3 := inclusion T l l.length s.length inl aux2
      unfold List.power_upto List.power_upto.loop
      simp
      apply Or.inl
      rw [← ht]
      exact aux3
    . rw [inr, ht] at aux2
      rw [List.length_cons]
      exact aux2

/-theorem exists_mem_powertype (T : Fintype α) (S : Set α) [BEq α] [DecidablePred S] : ∃ (l : List α), l = S.toList ∧ l ∈ (T.elems.power_upto T.elems.length)  := by
  exists S.toList
  constructor
  . rfl
  . have l_len : S.toList.length ≤ T.elems.length := by
      unfold Set.toList
      apply List.length_filter_le
    have mem := powerlist T S.toList l_len
    exact mem -/

/-instance (S : Set α) [Fintype α] : DecidablePred S := by

  sorry -/

/-theorem elem_iff_mem (S : Set α) (a : α) [Fintype α] : S.elem a = true ↔ a ∈ S := by
  unfold Set.elem
  simp only [Membership.mem]
  grind

theorem toList_toSet (l : List α) (S : Set α) (T : Fintype α) : l = S.toList → S = l.toSet := by
  intro eq
  apply Set.ext
  intro e
  constructor
  . intro e_mem
    unfold List.toSet
    unfold Set.toList at eq
    rw [eq]
    simp --only [Membership.mem, Set.elem]
    constructor
    . have complete := T.complete
      specialize complete e
      exact complete
    . rw [elem_iff_mem]
      . exact e_mem
  . intro e_mem
    unfold List.toSet at e_mem
    rw [eq] at e_mem
    unfold Set.toList at e_mem
    simp_all --only [Membership.mem, Set.elem] at e_mem
    rcases e_mem with ⟨e_mem, e_elem⟩
    rw [elem_iff_mem] at e_elem
    exact e_elem
    -/

theorem empty_set_if_empty_type (T : Fintype α) (S : Set α) : T.elems = [] → S = ∅ := by
  intro h
  apply Classical.byContradiction
  intro contra
  have exists_elem : ∃ a, a ∈ S := by
    rw [← Ne.eq_1] at contra
    apply Set.not_empty_contains_element
    exact contra
  rcases exists_elem with ⟨a, a_mem⟩
  have aux := T.complete
  specialize aux a
  rw [h] at aux
  contradiction

/-instance [T : Fintype α] [BEq α] : Fintype (Set α) where
  elems := (T.elems.power_upto T.elems.length).map (fun x => x.toSet)
  complete := by
    intro S
    have exists_l := exists_mem_powertype T S
    rcases exists_l with ⟨l, l_eq, l_mem⟩
    rw [List.mem_map]
    exists l
    constructor
    . exact l_mem
    . have aux := toList_toSet l S T l_eq
      symm at aux
      exact aux -/

theorem complete_set_iff [Fintype α] (S : Set α) : (S = fun _ => True) ↔ ∀ (x : α), x ∈ S := by
  constructor
  . intro eq
    intro x
    rw [eq]
    simp only [Membership.mem]
  . intro h
    apply Set.ext
    intro x
    constructor
    . intro x_mem
      simp only [Membership.mem]
    . intro x_mem
      grind

theorem complete_set_eq_fintype_elems (T : Fintype α) : T.elems.toSet = fun _ => True := by
  apply Set.ext
  intro x
  constructor
  . intro x_mem
    trivial
  . intro x_mem
    have x_mem_elems := T.complete x
    simp only [List.toSet, Membership.mem]
    exact x_mem_elems

theorem exists_not_mem_if_ne_complete_set (T : Fintype α) (S : Set α) : (S ≠ fun _ => True) → ∃ a, a ∉ S := by
  intro ne
  rw [Ne.eq_1] at ne
  apply Classical.byContradiction
  intro contra
  simp at contra
  have aux := complete_set_iff S
  have S_eq := aux.mpr contra
  contradiction

theorem ssubset_of_complete_set (T : Fintype α) (S : Set α) : (S ≠ fun _ => True) → S ⊂ (fun _ => True) := by
  intro ne
  constructor
  . intro a a_mem
    trivial
  . intro h
    have aux := exists_not_mem_if_ne_complete_set T S ne
    rcases aux with ⟨x, x_nmem⟩
    let complete_set : Set α := (fun a => True)
    have x_mem : x ∈ complete_set := by
      unfold complete_set
      simp only [Membership.mem]
    have x_mem_S : x ∈ S := h x x_mem
    contradiction

theorem list_of_subset (X Y : Set α) (h : ∃ (l' : List α), Y = l'.toSet) : X ⊆ Y → ∃ (l : List α), X = l.toSet := by
  intro sub
  rcases h with ⟨l', l'_eq⟩
  exists (l'.filter (fun e =>
      have := Classical.propDecidable (e ∈ X)
      decide (e ∈ X)
    ))
  unfold List.toSet
  simp
  apply Set.ext
  intro x
  simp only [Membership.mem]
  constructor
  . intro x_mem
    constructor
    . have x_mem_Y := sub x x_mem
      rw [l'_eq] at x_mem_Y
      simp only [List.toSet, Membership.mem] at x_mem_Y
      exact x_mem_Y
    . exact x_mem
  . intro x_mem
    exact x_mem.right

theorem list_of_subset' (T : Fintype α) (X Y : Set α) (h : ∃ (l' : List α), Y = l'.toSet ∧ l'.length ≤ T.elems.length) : X ⊆ Y → ∃ (l : List α), X = l.toSet ∧ l ∈ (T.elems.power_upto T.elems.length)  := by
  intro sub
  rcases h with ⟨l', l'_eq, l'_length⟩
  exists (l'.filter (fun e =>
      have := Classical.propDecidable (e ∈ X)
      decide (e ∈ X)
    ))
  unfold List.toSet
  simp
  constructor
  . apply Set.ext
    intro x
    simp only [Membership.mem]
    constructor
    . intro x_mem
      constructor
      . have x_mem_Y := sub x x_mem
        rw [l'_eq] at x_mem_Y
        simp only [List.toSet, Membership.mem] at x_mem_Y
        exact x_mem_Y
      . exact x_mem
    . intro x_mem
      exact x_mem.right
  . have l_length : (l'.filter (fun e => have := Classical.propDecidable (e ∈ X); decide (e ∈ X))).length ≤ T.elems.length := by
      grind
    exact powerlist T (l'.filter (fun e => have := Classical.propDecidable (e ∈ X); decide (e ∈ X))) l_length

theorem list_of_fintype_set (T : Fintype α) (S : Set α) : ∃ (l : List α), S = l.toSet := by
  have sub : S ⊆ Fintype.elems.toSet := by
    intro x x_mem
    simp only [List.toSet, Membership.mem]
    exact T.complete x
  have elems_list : ∃ (l : List α), T.elems.toSet = l.toSet := by exists T.elems
  apply list_of_subset S T.elems.toSet elems_list sub

theorem mem_powerlist_of_fintype_set (T : Fintype α) (S : Set α) : ∃ (l : List α), S = l.toSet ∧ l ∈ (T.elems.power_upto T.elems.length) := by
  have sub : S ⊆ Fintype.elems.toSet := by
    intro x x_mem
    simp only [List.toSet, Membership.mem]
    exact T.complete x
  have elems_list : ∃ (l : List α), T.elems.toSet = l.toSet ∧ l.length ≤ T.elems.length := by
    exists T.elems
    constructor
    . rfl
    . rw [Nat.le_iff_lt_or_eq]
      apply Or.inr; rfl
  apply list_of_subset' T S T.elems.toSet elems_list sub

instance [T : Fintype α] [BEq α] : Fintype (Powertype α) where
  elems := (T.elems.power_upto T.elems.length).map (fun x => x.toSet)
  complete := by
    intro S
    have exists_l := mem_powerlist_of_fintype_set T S
    rcases exists_l with ⟨l, l_eq, l_mem⟩
    rw [l_eq, List.mem_map]
    exists l

instance [T : Fintype α] [DecidableEq α] : Fintype (Set α) where
  elems := (T.elems.power_upto T.elems.length).map (fun x => x.toSet)
  complete := by
    intro S
    have exists_l := mem_powerlist_of_fintype_set T S
    rcases exists_l with ⟨l, l_eq, l_mem⟩
    rw [l_eq, List.mem_map]
    exists l

def List.removeDups [DecidableEq α] : List α -> List α
  | [] => []
  | hd::tl => if hd ∈ tl then tl.removeDups else hd::(tl.removeDups)

theorem List.mem_removeDups [DecidableEq α] (l : List α) : ∀ a, a ∈ l ↔ a ∈ l.removeDups := by
  induction l with
  | nil =>
    intro a
    simp only [removeDups]
  | cons b l' ih =>
    unfold removeDups
    intro a
    by_cases b_mem : b ∈ l'
    . simp only [b_mem, ite_true, List.mem_cons, ih]
      by_cases a_eq : a = b
      . simp only [a_eq, true_or]
        specialize ih b
        have aux : b ∈ l'.removeDups := ih.mp b_mem
        simpa using aux
      . simp only [a_eq, false_or]
    . simp only [b_mem, ite_false, List.mem_cons, ih]


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


--to do: für jede menge über einem fintype gibt es eine mit decidable pred

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
