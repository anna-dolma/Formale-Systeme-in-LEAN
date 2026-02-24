
theorem List.removeAll_nil_flatten [BEq α] : ∀ (l : List (List α)), (l.removeAll [[]]).flatten = l.flatten := by
  intro l
  induction l with
  | nil =>
    simp
  | cons a l ih =>
    rw [List.cons_removeAll]
    by_cases h : [[]].contains a
    . have a_eq : a=[] := by simp_all
      simp only [h]
      rw [a_eq, List.flatten_cons, List.nil_append, if_neg]
      . exact ih
      . trivial
    . simp only [h]
      rw [if_true]
      have a_eq : ¬(a = []) := by simp_all
      rw [List.flatten_cons, ih]
      rfl
/--
Eliminates duplicates from a list, keeping the rightmost occurrence. (Implementation copied from...)
-/
def List.removeDups [DecidableEq α] : List α -> List α
  | [] => []
  | hd::tl => if hd ∈ tl then tl.removeDups else hd::(tl.removeDups)

/--
Removing duplicates from a list does not change the elements contained in it.
-/
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

instance List.decidableInfix [DecidableEq α] : ∀ (k l : List α), Decidable (k <:+: l)
  | [], l => by
    apply isTrue
    unfold List.IsInfix
    exists l, []
    simp only [append_nil]
  | a :: k, [] => by
    apply isFalse
    unfold List.IsInfix
    simp only [append_assoc, cons_append, append_eq_nil_iff, reduceCtorEq, and_false, exists_const,
      not_false_eq_true]
  | k, b :: l =>
    letI := k.decidableInfix l
    @decidable_of_decidable_of_iff (k <+: b :: l ∨ k <:+: l) _ _
      infix_cons_iff.symm

def List.isInfixOf [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a::s, b::k => a::s <+: b::k ∨ s.isInfixOf k

theorem List.isInfixOf_cons [DecidableEq α] (k l : List α) (a : α) : k.isInfixOf l → k.isInfixOf (a::l) := by
  intro h

  sorry

theorem List.isInfixOf_iff_Infix [DecidableEq α] (k l : List α) : k.isInfixOf l ↔ k <:+: l := by
  induction l generalizing k with
  | nil =>
    cases  k_eq : k with
    | nil =>
      simp only [infix_rfl, iff_true]
      rfl
    | cons hd tl =>
      simp only [infix_nil, reduceCtorEq, iff_false, Bool.not_eq_true]
      rfl
  | cons b s ih =>
    constructor
    . intro h
      unfold isInfixOf at h

      sorry
    . intro h
      unfold isInfixOf
      cases k_eq : k with
      | nil =>
        simp only
      | cons hd tl =>
        simp
        rcases h with ⟨f, g, x⟩
        by_cases hb : hd = b
        . sorry
        .
          sorry
