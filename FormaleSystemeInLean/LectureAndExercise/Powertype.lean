import FormaleSystemeInLean.LectureAndExercise.Fintype
import FormaleSystemeInLean.LectureAndExercise.Set

set_option linter.unusedSectionVars false


/-!
The powerset DFA (as it is defined in Lecture 4) has subsets of Q (the states of the original NFA)
as its states. However, the automaton definitions in this formalisation don't use finite sets of states
but instead lists over a Fintype Q. So we need to define something like a powerset but for lists.
We also need to prove that the resulting "powerlist" contains only finitely many elements
because the states of an NFA have to be of a Fintype.
-/

def Powertype (α : Type u) := Set α

instance : Membership α (Powertype α) where
  mem S a := S a

/--
The powerset of a set X just contains all possible subsets of X. (See Set.lean)
We define the power of a list l as the list containing all lists up to the length if l with elements from l.
The following recursive function computes all lists with elements from a given list l that have
a length up to n. This includes lists with duplicate elements and all possible sequences.
We do this by repeatedly appending elements of l to all lists we currently have.
-/
def List.power_upto (l : List α) (n : Nat) : List (List α) :=
  let rec loop : Nat → List (List α)
    | 0 => [[]]
    | n+1 => let prev := loop n; prev ++ (prev.flatMap (fun l' => l.map fun e => e:: l'))
  loop n

/-!
This showcases how the power of a list is computed. As you can see, all the
different lists are added to the powerlist multiple times.
-/
#eval [0, 1, 2, 3].power_upto 4
--#eval ([0, 1, 2, 3].power_upto 4).eraseDups

/-!
After defining the power of a list, we can use this function to compute the Powertype of a Fintype
and prove that it is also finite. As a reminder: a Fintype is a type with a corresponding list ("elems")
containing all things of this type (refer to Fintype.lean for further information).

The following 4 theorems are auxiliary results required to prove that for a Fintype T with elements of type α
T.elems.power_upto (T.elems.length) contains all lists of type List α that are at most of the same length as T.elems.
-/

/-- the result of [].power_upto n is [[]] for all n. -/
theorem nil_power (n : Nat) (l : List α) : l = [] -> l.power_upto n = [[]] := by
  intro l_eq
  induction n with
  | zero =>
    unfold List.power_upto List.power_upto.loop
    rfl
  | succ n ih =>
    unfold List.power_upto List.power_upto.loop
    subst l
    simp only [List.map_nil]
    unfold List.power_upto at ih
    rw [ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- T.elems.power_upto n contains every List α of length n -/
theorem mem_power_upto_n (T : Fintype α) (l : List α) : l.length ≤ T.elems.length → l ∈ T.elems.power_upto (l.length) := by
  intro l_length
  induction n_eq : l.length generalizing l with
  | zero =>
    unfold List.power_upto List.power_upto.loop
    rw [← List.eq_nil_iff_length_eq_zero] at n_eq
    rw [n_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  | succ n ih =>
    have l_neq_nil : l ≠ [] := by
        have l_len_gz : l.length > 0 := by
          rw [← Nat.succ_eq_add_one] at n_eq
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
    have l'_len_le : l'.length ≤ T.elems.length := by grind
    have l'_mem := ih l' l'_len_le l'_len
    unfold List.power_upto List.power_upto.loop
    simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    apply Or.inr
    exists l'
    constructor
    . exact l'_mem
    . exists a
      constructor
      . exact T.complete a
      . symm; exact l_eq

-- I left the old version of this theorem here as an example for an overly complicated proof.
theorem mem_power_upto_n' (T : Fintype α) (l : List α) (n : Nat) : n ≤ T.elems.length → l.length = n → l ∈ T.elems.power_upto n := by
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
      simp only [List.map_cons, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
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

/-- If a list l is contained in T.elems.power_upto n, then it is also an element of l ∈ T.elems.power_upto (n+1). -/
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
    simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    apply Or.inl
    exact ih

/-- Now we can finally prove that the powerlist of T.elems contains all lists of length at most T.elems.length: -/
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
    have incl := inclusion_succ T l l.length l_len
    have mem_power := mem_power_upto_n T l l_len
    rw [ht, List.length_cons, Nat.le_add_one_iff] at l_len
    rcases l_len with inl | inr
    . have test := incl mem_power
      rw [ht] at test
      rw [List.length_cons]
      have aux3 := inclusion T l l.length s.length inl mem_power
      unfold List.power_upto List.power_upto.loop
      simp only [List.map_cons, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map]
      apply Or.inl
      rw [← ht]
      exact aux3
    . rw [inr, ht] at mem_power
      rw [List.length_cons]
      exact mem_power

/-!
Now the goal is a Fintype-instance for Powertype α, given an instance Fintype α, or to phrase it differently:
the Powertype of something finite is again finite. Since we defined Powertype as a set, the elements of the
resulting instance have to be sets. We can achieve this by mapping each element of the powerlist to a set.
It remains to prove that every Set α is contained in the resulting list of sets.
-/

/--
If X is a subset of Y and there is a corresponding list for Y, then there must be a list for X as well.
We need to assume that the predicate X is decidable here.
-/
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

/--
If X is a subset of Y and the list for the superset Y has at most the length T.elems.length,
then there is a list for X that is contained in the powerlist of T.elems.
-/
theorem mem_powerlist_of_subset (T : Fintype α) (X Y : Set α) (h : ∃ (l' : List α), Y = l'.toSet ∧ l'.length ≤ T.elems.length) : X ⊆ Y → ∃ (l : List α), X = l.toSet ∧ l ∈ (T.elems.power_upto T.elems.length)  := by
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

/--
Given a Fintype T with elements of type α, every Set containing elements of type α has a list with the same elements.
We can prove this with the help of list_of_subset because every Set α is a subset of T.elems.toSet.
Then the list for the superset Y is just T.elems itself.
-/
theorem list_of_fintype_set (T : Fintype α) (S : Set α) : ∃ (l : List α), S = l.toSet := by
  have sub : S ⊆ Fintype.elems.toSet := by
    intro x x_mem
    simp only [List.toSet, Membership.mem]
    exact T.complete x
  have elems_list : ∃ (l : List α), T.elems.toSet = l.toSet := by exists T.elems
  apply list_of_subset S T.elems.toSet elems_list sub

/--
For the typeclass instance we need a list for each Set α. This list also needs to be an element of T.elems.power_upto T.elems.length.
We already know how to obtain the list (see previous theorem). Obviously the length of T.elems is at most T.elems.length.
Then we can apply mem_powerlist_of_subset using T.elems.toSet as the superset Y and the set S
(for which we want to prove the existence of a list contained in the powerlist) as the subset X.
-/
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
  apply mem_powerlist_of_subset T S T.elems.toSet elems_list sub

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
