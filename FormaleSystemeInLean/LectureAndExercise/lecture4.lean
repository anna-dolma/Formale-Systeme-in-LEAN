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

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma] [Fintype (Option Q)] [BEq Q] [BEq (Set Q)] [DecidableEq Q] [Fintype (Set Q)]

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

/-
def NFA.to_DFA (M : NFA Q Sigma) [DecidablePred R] : DFA (Powertype Q) Sigma where
  δ := fun R a => some (R.toList.flatMap (fun q => M.δ q a)).toSet
  q0 := M.Q0.toSet
  F := Fintype.elems.filter (fun x => M.F.toSet ∩ x != ∅)
-/
def List.filterPred (l : List α) (P : α -> Prop) [DecidablePred P] : List α :=
  l.filter (fun a => decide (P a))

def NFA.to_TotalDFA (M : NFA Q Sigma) : TotalDFA (Powertype Q) Sigma where
  δ := fun R a => fun q => ∃ r ∈ R, q ∈ M.δ r a--(R.toList.flatMap (fun q => M.δ q a)).toSet
  q0 := M.Q0.toSet
  F := Fintype.elems.filter (fun x => M.F.toSet ∩ x != ∅) --(fun R => decide (∃ x, x ∈ R ∧ x ∈ M.F)) --

theorem to_NFA_lang_eq (M : DFA Q Sigma) : M.to_NFA.Language = M.Language := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    simp only [DFA.Language, Membership.mem]
    rw [acc_run_iff_δ_word_contains_final] at w_mem
    rcases w_mem with ⟨qf, qf_memd, qf_memf⟩
    simp only [DFA.to_NFA] at qf_memf
    exists qf
    constructor
    . induction w with
      | nil =>
        simp only [NFA.δ_word, DFA.to_NFA, List.mem_singleton] at qf_memd
        simp only [DFA.δ_word, Option.some_inj]
        rw [qf_memd]
      | cons a v ih =>
        simp only [NFA.δ_word] at qf_memd
        simp only [DFA.δ_word]
        sorry
    . trivial
  . intro w_mem
    simp only [DFA.Language, Membership.mem] at w_mem
    rcases w_mem with ⟨qf, qf_eq, qf_memf⟩
    unfold DFA.δ_word at qf_eq
    rw [acc_run_iff_δ_word_contains_final]
    exists qf
    constructor
    .
      sorry
    . sorry

/-theorem δ_powersetDFA_eq_some (M : NFA Q Sigma) (a : Sigma) (R : Powertype Q) : M.to_DFA.δ R a ≠ none := by
  unfold NFA.to_DFA
  grind

theorem δ_NFA_subset_δ_powersetDFA (M : NFA Q Sigma) (a : Sigma) (R : Powertype Q) : q ∈ R.toList → (M.δ q a).toSet ⊆ M.to_TotalDFA.δ R a := by
  intro q_mem
  intro q' q'_mem
  simp only [NFA.to_TotalDFA]
  unfold List.toSet at *
  simp only [Membership.mem] at *
  --apply List.mem_flatMap_of_mem q_mem
  --exact q'_mem
  sorry -/

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

theorem nonempty_2 (B : Set α) [BEq (Set α)] [LawfulBEq (Set α)] : B != ∅ -> ∃ a, a ∈ B := by
  intro neq
  apply Classical.byContradiction
  intro contra
  rw [not_exists] at contra
  have aux := empty_eq B contra
  rw [aux] at neq
  simp at neq

theorem to_DFA_lang_eq (M : NFA Q Sigma) [LawfulBEq (Set Q)] : M.to_TotalDFA.Language = M.Language := by
  apply Set.ext
  intro w
  unfold TotalDFA.Language
  constructor
  . intro w_mem
    rw [acc_run_iff_δ_word_contains_final]
    simp only [Membership.mem] at *
    cases w with
    | nil =>
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA] at w_mem
      have aux := List.mem_filter.mp w_mem
      rcases aux with ⟨r, t⟩
      have aux2 : ∃ q0, q0 ∈ M.F.toSet ∩ M.Q0.toSet := by
        apply nonempty_2 (M.F.toSet ∩ M.Q0.toSet)
        exact t
      rcases aux2 with ⟨q0, q0_memf, q0_memQ0⟩
      exists q0
    | cons a v =>
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA] at w_mem


      --rcases w_mem with ⟨q, q_memd, q_memf⟩
      /-exists q
      rw [δ_word_eq_DFA_NFA]
      -/
      sorry
  . intro w_mem
    rw [acc_run_iff_δ_word_contains_final] at w_mem
    simp only [Membership.mem]
    rcases w_mem with ⟨q, q_memd, q_memf⟩
    cases w with
    | nil =>
      unfold NFA.δ_word at q_memd
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA]

      --exists q
      sorry
    | cons a v =>
      --rw [δ_word_eq_DFA_NFA] at q_memd
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA]

      --exists q
      sorry
