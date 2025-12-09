import FormaleSystemeInLean.LectureAndExercise.lecture1
import FormaleSystemeInLean.LectureAndExercise.lecture3

set_option linter.unusedSectionVars false

structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → List Q
  Q0 : List Q
  F : List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma] [Fintype (Option Q)]

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
    unfold NFA.δ_word-- at aux
    have aux2 : ∀ q, q ∈ nfa.δ qa a → q ∈ (List.flatMap (fun x => nfa.δ x a) R) := by
      intro q q_mem
      rw [List.mem_flatMap]
      exists qa
    grind

theorem run_from_δ_word (nfa : NFA Q Sigma) (qn : Q) (R : List Q) (w : Word Sigma) : qn ∈ nfa.δ_word R w → ∃ (q1 : Q) (r : nfa.Run q1 qn w), q1 ∈ R := by
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

-- Equality of the two different definitions of the language accepted by an NFA: An NFA has an accepting run q0...qf on a word w iff the set
-- of states reachable from q0 ∈ Q0 contains a qf ∈ F.
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

def NFA.to_DFA (M : NFA Q Sigma) [Fintype (List Q)] : DFA (List Q) Sigma where
  δ := sorry
  q0 := M.Q0
  F := sorry -- Liste mit allen möglichen Listen die aus q ∈ M.F gebildet werden können
