
-- inspired by mathlib
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a : α, a ∈ elems

def Set (α : Type u) := α -> Prop

def Set.elem (S : Set α) (a : α) [DecidablePred S] : Bool :=
  decide (S a)

def Set.toList (S : Set α) [Fintype α] [DecidablePred S] : List α :=
  Fintype.elems.filter (fun x => S.elem x)

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

theorem not_empty_contains_element (X : Set α) : X ≠ ∅ -> ∃ e, e ∈ X := by
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

theorem empty_eq (A : Set α) : (∀ (x : α), ¬x ∈ A) -> A = ∅ := by
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

theorem exists_mem_powertype (T : Fintype α) (S : Set α) [BEq α] [DecidablePred S] : ∃ (l : List α), l = S.toList ∧ l ∈ (T.elems.power_upto T.elems.length)  := by
  exists S.toList
  constructor
  . rfl
  . have l_len : S.toList.length ≤ T.elems.length := by
      unfold Set.toList
      apply List.length_filter_le
    have mem := powerlist T S.toList l_len
    exact mem

-- gegeben: S und irgendein α
-- frage: gilt S α ?
-- es gibt nur endlich viele α, für die S gilt
-- daher muss es eine liste mit elementen aus Fintype.elems geben, die alle α mit S α enthält
instance (S : Set α) [Fintype α] : DecidablePred S := by

  sorry

-- List.remove braucht nur BEq

theorem elem_iff_mem (S : Set α) (a : α) [Fintype α] : S.elem a = true ↔ a ∈ S := by
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

theorem empty_set_if_empty_type (T : Fintype α) (S : Set α) : T.elems = [] → S = ∅ := by
  intro h
  apply Classical.byContradiction
  intro contra
  have exists_elem : ∃ a, a ∈ S := by
    rw [← Ne.eq_1] at contra
    apply not_empty_contains_element
    exact contra
  rcases exists_elem with ⟨a, a_mem⟩
  have aux := T.complete
  specialize aux a
  rw [h] at aux
  contradiction

-- problem: toList verwendet decidablePred
theorem max_card (T : Fintype α) (S : Set α) [BEq α] : S.toList.length ≤ T.elems.length := by
  have complete := T.complete
  cases ht:  T.elems with
  | nil =>
    rw [ht] at complete
    simp only [List.mem_nil_iff] at complete
    rw [List.length_nil, Nat.le_zero]
    have S_eq : S = ∅ := empty_set_if_empty_type T S ht
    have S_toList : S.toList = [] := by
      unfold Set.toList
      sorry
    sorry
  | cons b a =>
    -- entweder S.toList.length = (b::a).length
    -- oder...
    rw [Nat.le_iff_lt_or_eq]
    by_cases hs : S.toList.length = (b :: a).length
    . apply Or.inr
      exact hs
    . simp only [hs]
      apply Or.inl

      sorry

-- daraus soll DecidablePred S folgen
theorem set_of_list (T : Fintype α) (S : Set α) : ∃ (l : List α), l.toSet = S := by
  have complete := T.complete
  have case1 : (S = fun a => True) → S = T.elems.toSet := by
    intro h
    apply Set.ext
    intro e
    constructor
    . intro e_mem
      specialize complete e
      unfold List.toSet
      simp only [Membership.mem]
      exact complete
    . intro e_mem
      rw [h]
      simp only [Membership.mem]
  -- wenn S ≠ T.elems.toSet, dann gibt es eine menge S' so dass S = T.elems \ S'
  -- l = T.elems.removeAll ...
  -- gequirlter quark

  sorry

instance [T : Fintype α] [BEq α] : Fintype (Set α) where
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
      exact aux

theorem list_of_complete_set (T : Fintype α) (S : Set α) : (S = fun _ => True) → ∃ (l : List α), l.toSet = S := by
  intro hs
  exists T.elems
  rw [hs]
  unfold List.toSet
  apply funext
  intro x
  have complete := T.complete
  specialize complete x
  grind

theorem complete_set_eq [Fintype α] (S : Set α) : (S = fun _ => True) ↔ ∀ (x : α), x ∈ S := by
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

theorem exists_not_mem_if_ne_complete_set (T : Fintype α) (S : Set α) : (S ≠ fun _ => True) → ∃ a, a ∉ S := by
  intro ne
  rw [Ne.eq_1] at ne
  apply Classical.byContradiction
  intro contra
  simp at contra
  have aux := complete_set_eq S
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

theorem subset_of_complete_set [Fintype α] (S : Set α) : S ⊆ (fun _ => true) := by
  intro x x_mem
  trivial

theorem list_of_fintype_set (T : Fintype α) (S : Set α) : ∃ (l : List α), l.toSet = S ∧ l ∈ (T.elems.power_upto T.elems.length) := by
  exists (T.elems.filter (fun e =>
      have := Classical.propDecidable (e ∈ S)
      decide (e ∈ S)
    ))
  constructor
  . unfold List.toSet
    simp
    apply Set.ext
    intro x
    simp only [Membership.mem]
    constructor
    . intro h
      rcases h with ⟨mem_elems, mem_S⟩
      exact mem_S
    . intro h
      constructor
      . have complete := T.complete
        specialize complete x
        exact complete
      . exact h
  . have l_length : (T.elems.filter (fun e => have := Classical.propDecidable (e ∈ S); decide (e ∈ S))).length ≤ T.elems.length := by
      grind
    have mem := powerlist T (T.elems.filter (fun e => have := Classical.propDecidable (e ∈ S); decide (e ∈ S))) l_length
    exact mem

instance [T : Fintype α] [BEq α] : Fintype (Powertype α) where
  elems := (T.elems.power_upto T.elems.length).map (fun x => x.toSet)
  complete := by
    intro S
    have exists_l := list_of_fintype_set T S
    rcases exists_l with ⟨l, l_eq, l_mem⟩
    rw [List.mem_map]
    exists l
