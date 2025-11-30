
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
