import FormaleSystemeInLean.LectureAndExercise.lecture1
import FormaleSystemeInLean.LectureAndExercise.lecture3

set_option linter.unusedSectionVars false

-- TO DO VL 4:
-- VL4: NFAs mit nur einem Start-/Endzustand sind äquivalent zu normalen NFAs (nur evtl.)
-- Äquivalenz von NFAs und DFAs mittels Potenzmengenkonstruktion
-- VL 4, Folie 30: NFAs können exponentiell kleiner sein als DFAs (Beispiel)

structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → List Q
  Q0 : List Q
  F : List Q

-- TODO: Fintype (Option Q) should be inferrable from Fintype Q
variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma] [Fintype (Option Q)] [BEq Q] [BEq (Set Q)] [DecidableEq Q]

def NFA.δ_word (nfa : NFA Q Sigma) (R : List Q) : (Word Sigma) → List Q
  | .nil => R
  | .cons a v => nfa.δ_word (R.flatMap (nfa.δ · a)) v

inductive NFA.Run (nfa : NFA Q Sigma) : Q -> Q -> Word Sigma -> Type _
| self (q : Q) : nfa.Run q q []
| step {q1 q2 qf : Q} {a : Sigma} {v : Word Sigma} (r : nfa.Run q2 qf v) (q2_mem : q2 ∈ nfa.δ q1 a) : nfa.Run q1 qf (a :: v)

def NFA.Run.from_start {nfa : NFA Q Sigma} (_ : nfa.Run q0 q w) : Prop := q0 ∈ nfa.Q0
def NFA.Run.accepts {nfa : NFA Q Sigma} (_ : nfa.Run q qf w) : Prop := qf ∈ nfa.F

def NFA.Language (nfa : NFA Q Sigma) : Language Sigma :=
  fun w => ∃ (q0 qf : Q) (r : nfa.Run q0 qf w), r.from_start ∧ r.accepts

theorem δ_subset_δ_word (nfa : NFA Q Sigma) (q : Q) (R : List Q) (a : Sigma) : q ∈ R → nfa.δ q a ⊆ nfa.δ_word R [a] := by
  intro q_mem q' q'_memd
  unfold NFA.δ_word
  have aux : q' ∈ R.flatMap (fun x => nfa.δ x a) := by
    simp only [List.mem_flatMap]
    exists q
  simp only [NFA.δ_word]
  exact aux

-- for every run q1...qn on a word w with q1 ∈ R, qn ∈ δ_word(R, w).
theorem run_imp_mem_δ (nfa : NFA Q Sigma) (q1 qn : Q) (R : List Q) (w : Word Sigma) : nfa.Run q1 qn w → q1 ∈ R → qn ∈ nfa.δ_word R w := by
  intro r q1_mem
  induction r generalizing R with
  | self q =>
    trivial
  | @step qa qb qc a v r qb_mem hr =>
    have aux : qc ∈ nfa.δ_word (nfa.δ qa a) v := hr (nfa.δ qa a) qb_mem
    unfold NFA.δ_word
    have aux2 : ∀ q, q ∈ nfa.δ qa a → q ∈ (List.flatMap (fun x => nfa.δ x a) R) := by
      intro q q_mem
      rw [List.mem_flatMap]
      exists qa
    grind

-- given a set of states R and a state qn ∈ δ(R, w) we can also construct a run for w starting with a state in R.
theorem run_from_δ_word (nfa : NFA Q Sigma) (qn : Q) (R : List Q) (w : Word Sigma) : qn ∈ nfa.δ_word R w → ∃ (q1 : Q) (_ : nfa.Run q1 qn w), q1 ∈ R := by
  intro qn_mem
  induction w generalizing R with
  | nil =>
    simp only [Membership.mem] at qn_mem
    unfold NFA.δ_word at qn_mem
    exists qn
    exists NFA.Run.self qn
  | cons a v ih =>
    simp only [Membership.mem, NFA.δ_word] at qn_mem
    have aux := ih (List.flatMap (fun x => nfa.δ x a) R) qn_mem
    rcases aux with ⟨q, r', q_mem⟩
    have aux2 : ∃ q', q' ∈ R ∧ q ∈ nfa.δ q' a := by
      rw [List.mem_flatMap] at q_mem
      rcases q_mem with ⟨q', q'_mem, q_mem⟩
      exists q'
    rcases aux2 with ⟨q', q'_mem, q'_memd⟩
    exists q'
    exists NFA.Run.step r' q'_memd

-- Using the two previous results, we can show that the two different definitions for the language accepted by an NFA are equal:
-- An NFA has an accepting run q0...qf on a word w iff the set of states reachable from q0 ∈ Q0 contains a qf ∈ F.
theorem acc_run_iff_δ_word_contains_final (nfa : NFA Q Sigma) (w : Word Sigma) : w ∈ nfa.Language ↔ ∃ q ∈ nfa.δ_word nfa.Q0 w, q ∈ nfa.F := by
  constructor
  . intro w_mem
    rcases w_mem with ⟨q0, qf, r, r_s, r_acc⟩
    unfold NFA.Run.accepts at r_acc
    unfold NFA.Run.from_start at r_s
    have qf_mem : qf ∈ nfa.δ_word nfa.Q0 w := run_imp_mem_δ nfa q0 qf nfa.Q0 w r r_s
    exists qf
  . intro h
    unfold NFA.Language
    simp only [Membership.mem]
    rcases h with ⟨qf, q_memd, q_memf⟩
    have run := run_from_δ_word nfa qf nfa.Q0 w q_memd
    rcases run with ⟨q0, r, q0_mem⟩
    exists q0, qf, r

def DFA.to_NFA (M : DFA Q Sigma) : NFA Q Sigma where
  δ := fun q a =>
    match M.δ q a with
    | none => []
    | some q => [q]
  Q0 := [M.q0]
  F := M.F

def List.filterPred (l : List α) (P : α -> Prop) [DecidablePred P] : List α :=
  l.filter (fun a => decide (P a))

def NFA.to_TotalDFA (M : NFA Q Sigma) : TotalDFA (Powertype Q) Sigma where
  δ := fun R a => fun q => ∃ r ∈ R, q ∈ M.δ r a
  q0 := M.Q0.toSet
  F := Fintype.elems.filter (fun x => M.F.toSet ∩ x != ∅)

def TotalDFA.to_NFA (M : TotalDFA Q Sigma) : NFA Q Sigma where
  δ := fun q a => [M.δ q a]--fun q' => q' = M.δ q a
  Q0 := [M.q0]
  F := M.F

theorem totalDFA_NFA_δ_eq (M : TotalDFA Q Sigma) (a : Sigma) (q : Q) : q' ∈ M.to_NFA.δ q a ↔ q' = M.δ q a := by
  simp only [TotalDFA.to_NFA, List.mem_singleton]

theorem totalDFA_NFA_δ_word_eq (M : TotalDFA Q Sigma) (w : Word Sigma) (q : Q) : q' ∈ M.to_NFA.δ_word [q] w ↔ M.δ_word q w = q' := by
  induction w generalizing q with
  | nil =>
    simp only [NFA.δ_word, TotalDFA.δ_word]
    constructor
    . intro eq
      rw [List.mem_singleton] at eq
      symm
      rw [eq]
    . intro eq
      rw [List.mem_singleton]
      symm
      rw [eq]
  | cons a v ih =>
    simp only [NFA.δ_word, TotalDFA.δ_word, Membership.mem]
    have aux := ih (M.δ q a)
    simp -- mit was muss ich simpen?
    exact aux

-- letz fetz
theorem totalDFA_NFA_lang_eq (M : TotalDFA Q Sigma) : M.to_NFA.Language = M.Language := by
  apply Set.ext
  intro w
  rw [acc_run_iff_δ_word_contains_final]
  unfold TotalDFA.Language
  have Q0_eq : M.to_NFA.Q0 = [M.q0] := by
    simp only [TotalDFA.to_NFA]
  constructor
  . intro hq
    rcases hq with ⟨qf, qf_memd, qf_memf⟩
    simp only [Membership.mem]
    simp only [TotalDFA.to_NFA] at qf_memf
    cases w with
    | nil =>
      simp only [NFA.δ_word] at qf_memd
      simp only [TotalDFA.δ_word]
      rw [Q0_eq, List.mem_singleton] at qf_memd
      rw [← qf_memd]
      exact qf_memf
    | cons a v =>
      rw [Q0_eq, totalDFA_NFA_δ_word_eq] at qf_memd
      rw [qf_memd]
      exact qf_memf
  . intro w_mem
    simp only [Membership.mem] at w_mem
    cases w with
    | nil =>
      simp only [TotalDFA.δ_word] at w_mem
      exists M.q0
      constructor
      . rw [Q0_eq]
        simp only [NFA.δ_word, List.mem_singleton]
      . simp only [Membership.mem]
        exact w_mem
    | cons a v =>
      simp only [TotalDFA.δ_word] at w_mem
      exists (M.δ_word (M.δ M.q0 a) v)
      constructor
      . rw [Q0_eq, totalDFA_NFA_δ_word_eq]
        rfl
      . simp only [TotalDFA.to_NFA]
        exact w_mem

theorem δ_NFA_eq_δ_TotalDFA (M : NFA Q Sigma) (a : Sigma) (R : List Q) : M.to_TotalDFA.δ R.toSet a = (M.δ_word R [a]).toSet := by
  simp only [NFA.to_TotalDFA, NFA.δ_word]
  unfold List.toSet
  apply funext
  intro q
  rw [List.mem_flatMap]
  rfl

theorem δ_word_eq_DFA_NFA (M : NFA Q Sigma) (w : Word Sigma) (R : List Q) [BEq (Powertype Q)] : (M.δ_word R w).toSet = M.to_TotalDFA.δ_word R.toSet w := by
  apply Set.ext
  intro q
  induction w generalizing q R with
  | nil =>
    grind
  | cons a v ih =>
    simp only [NFA.δ_word]
    have aux := ih (List.flatMap (fun x => M.δ x a) R) q
    simp only [TotalDFA.δ_word]
    rw [δ_NFA_eq_δ_TotalDFA]
    unfold List.toSet at *
    simp only [Membership.mem] at *
    grind
    --sorry



-- "not_empty_contains_element" but for boolean inequality
theorem ne_empty_contains_element (B : Set α) [BEq (Set α)] [LawfulBEq (Set α)] : B != ∅ -> ∃ a, a ∈ B := by
  intro neq
  apply Classical.byContradiction
  intro contra
  rw [not_exists] at contra
  have aux := empty_eq B contra
  rw [aux] at neq
  simp at neq

theorem NFA_totalDFA_lang_eq (M : NFA Q Sigma) [BEq (Powertype Q)] [LawfulBEq (Set Q)] : M.to_TotalDFA.Language = M.Language := by
  apply Set.ext
  intro w
  unfold TotalDFA.Language
  rw [acc_run_iff_δ_word_contains_final]

  have q0_eq : M.to_TotalDFA.q0 = M.Q0.toSet := rfl
  have := δ_word_eq_DFA_NFA M w M.Q0
  have THIS_COULD_BE_A_SEPARATE_RESULT : ∀ {α} {S : Set α} x, x ∈ S ↔ S x := by simp [Membership.mem]
  rw [THIS_COULD_BE_A_SEPARATE_RESULT]
  rw [q0_eq, ← this]

  simp only [NFA.to_TotalDFA]
  rw [List.mem_filter]
  constructor
  . rintro ⟨_, h⟩
    rcases ne_empty_contains_element _ h with ⟨q, q_mem_f, q_mem_start⟩
    exists q
  . rintro ⟨q, q_mem_start, q_mem_f⟩
    constructor
    . apply Fintype.complete (α := Powertype Q)
    . simp only [bne_iff_ne]
      intro contra
      have : q ∈ M.F.toSet ∩ (M.δ_word M.Q0 w).toSet := by
        constructor
        . exact q_mem_f
        . exact q_mem_start
      rw [contra] at this
      simp [EmptyCollection.emptyCollection, Membership.mem] at this
