
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
