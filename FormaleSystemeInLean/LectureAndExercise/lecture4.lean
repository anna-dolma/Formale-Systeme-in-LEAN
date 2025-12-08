import FormaleSystemeInLean.LectureAndExercise.lecture1

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

-- soll in
theorem run_imp_mem_δ (nfa : NFA Q Sigma) (q1 qn : Q) (R : List Q) (w : Word Sigma) : nfa.Run q1 qn w → q1 ∈ R → qn ∈ nfa.δ_word R w := by
  intro r q1_mem
  -- induktion über den lauf
  induction w generalizing q1 R with
  | nil =>
    unfold NFA.δ_word
    have eq : q1 = qn := by
      cases r; rfl
    subst eq
    exact q1_mem
  | cons a v ih =>
    cases r with
    | @step run mem q_a q_b q_c x y =>
      have no_idea : qn ∈ nfa.δ_word (nfa.δ q1 a) v := by
        apply ih _ (nfa.δ q1 a) x y
      simp only [NFA.δ_word]
      have idk : q1 ∈ R → nfa.δ q1 a ⊆ nfa.δ_word R [a] := by
        intro q_mem q' q1_mem_δ
        unfold NFA.δ_word

        sorry
      sorry

theorem acc_run_iff_δ_word_contains_final (nfa : NFA Q Sigma) (w : Word Sigma) : w ∈ nfa.Language ↔ ∃ q ∈ nfa.δ_word nfa.Q0 w, q ∈ nfa.F := by
  constructor
  . intro w_mem
    rcases w_mem with ⟨q0, qf, r, r_s, r_acc⟩
    unfold NFA.Run.accepts at r_acc
    unfold NFA.Run.from_start at r_s
    exists qf

    constructor
    . sorry

    . sorry
  . intro h
    unfold NFA.Language
    simp only [Membership.mem]

    sorry
