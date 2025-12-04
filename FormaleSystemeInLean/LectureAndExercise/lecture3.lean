import FormaleSystemeInLean.LectureAndExercise.lecture1

structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → Option Q
  q0 : Q
  F : List Q

structure TotalDFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] extends DFA Q Sigma where
  totality: ∀q, ∀a, Option.isSome (δ q a)
  garbage_state: Q


structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → List Q
  Q0 : List Q
  F : List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma]

def DFA.δ_word (dfa : DFA Q Sigma) (q : Q) : (Word Sigma) -> Option Q
| .nil => .some q
| .cons a v => (dfa.δ q a).bind (fun q' => dfa.δ_word q' v)

def DFA.Language (dfa : DFA Q Sigma) : Language Sigma :=
  fun w => ∃ qf, dfa.δ_word dfa.q0 w = some qf ∧ qf ∈ dfa.F

inductive NFA.Run (nfa : NFA Q Sigma) : Q -> Q -> Word Sigma -> Type _
| self (q : Q) : nfa.Run q q []
| step {q1 q2 qf : Q} {a : Sigma} {v : Word Sigma} (r : nfa.Run q2 qf v) (q2_mem : q2 ∈ nfa.δ q1 a) : nfa.Run q1 qf (a :: v)

def NFA.Run.from_start {nfa : NFA Q Sigma} (_ : nfa.Run q0 q w) : Prop := q0 ∈ nfa.Q0
def NFA.Run.accepts {nfa : NFA Q Sigma} (_ : nfa.Run q qf w) : Prop := qf ∈ nfa.F

def NFA.Language (nfa : NFA Q Sigma) : Language Sigma :=
  fun w => ∃ (q0 qf : Q) (r : nfa.Run q0 qf w), r.from_start ∧ r.accepts

-- TO DO VL 3 und 4:
-- totale übergänge, beweis, dass dfa_total = dfa
-- VL4: NFAs mit nur einem Start-/Endzustand sind äquivalent zu normalen NFAs
-- NFA δ für Wörter?
-- Beweis für: Es gibt einen akzeptierenden Lauf für w genau dann wenn δ(Q₀, w) ∩ F = ∅.
-- Äquivalenz von NFAs und DFAs mittels Potenzmengenkonstruktion

def DFA.to_totalDFA (M : DFA Q Sigma) (qₜ : Q) : TotalDFA Q Sigma where
  garbage_state := qₜ
  δ := fun q a =>
    match M.δ q a with
    | .some q => some q
    | .none => some qₜ
  q0 := M.q0
  F := M.F
  totality := by grind

theorem totalDFA_eq_DFA (M₁ : DFA Q Sigma) (qₜ : Q) : M₁.Language = (M₁.to_totalDFA qₜ).Language := by
  apply Set.ext
  intro w
  constructor
  . intro w_mem
    rcases w_mem with ⟨q, δ_eq, q_mem_f⟩
    exists q
    constructor
    . symm at δ_eq
      rw [δ_eq]
      induction w with
      | nil =>
        trivial
      | cons σ w' ih =>
        unfold DFA.δ_word at δ_eq
        unfold DFA.δ_word
        simp only [DFA.to_totalDFA]



        sorry

    . trivial
  . sorry
