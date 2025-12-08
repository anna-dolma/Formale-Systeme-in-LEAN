import FormaleSystemeInLean.LectureAndExercise.lecture1

structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → Option Q
  q0 : Q
  F : List Q

structure TotalDFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q → Sigma → Q
  q0: Q
  F: List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma] [Fintype (Option Q)]

def DFA.δ_word (dfa : DFA Q Sigma) (q : Q) : (Word Sigma) -> Option Q
| .nil => .some q
| .cons a v => (dfa.δ q a).bind (fun q' => dfa.δ_word q' v)

def TotalDFA.δ_word (t_dfa : TotalDFA Q Sigma) (q : Q) : (Word Sigma) → Q
  | .nil => q
  | .cons a v => t_dfa.δ_word (t_dfa.δ q a) v

def TotalDFA.Language (t_dfa : TotalDFA Q Sigma) : Language Sigma :=
  fun w => t_dfa.δ_word t_dfa.q0 w ∈ t_dfa.F

def DFA.Language (dfa : DFA Q Sigma) : Language Sigma :=
  fun w => ∃ qf, dfa.δ_word dfa.q0 w = some qf ∧ qf ∈ dfa.F

-- TO DO VL 3 und 4:
-- totale übergänge, beweis, dass dfa_total = dfa
-- VL4: NFAs mit nur einem Start-/Endzustand sind äquivalent zu normalen NFAs
-- NFA δ für Wörter?
-- Beweis für: Es gibt einen akzeptierenden Lauf für w genau dann wenn δ(Q₀, w) ∩ F = ∅.
-- Äquivalenz von NFAs und DFAs mittels Potenzmengenkonstruktion
-- VL 4, Folie 30: NFAs können exponentiell kleiner sein als DFAs (Beispiel)
-- und reihenfolge wieder herstellen :|

def DFA.to_totalDFA (M : DFA Q Sigma) : TotalDFA (Option Q) Sigma where
  /-δ := fun q a =>
    match q with
      | none => none
      | some q =>
        match M.δ q a with
        | none   => none
        | some q' => some q'-/
  δ := fun q a => q.bind (M.δ · a)
  q0 := .some M.q0
  F := M.F.map fun q => some q

theorem final_iff_final (M : DFA Q Sigma) (q : Q) : q ∈ M.F ↔ some q ∈ M.to_totalDFA.F := by
  constructor
  . intro q_mem
    unfold DFA.to_totalDFA
    grind
  . intro q_mem
    unfold DFA.to_totalDFA at q_mem
    grind

theorem δ_eq_δ (M : DFA Q Sigma) (q : Q) (a : Sigma) : M.δ q a = M.to_totalDFA.δ q a := by
  unfold DFA.to_totalDFA
  simp

theorem δ_none_eq_none (M : DFA Q Sigma) (a : Sigma) : M.to_totalDFA.δ none a = none := by
  trivial -- to do: ohne trivial???

theorem garbage_state (M : DFA Q Sigma) (w : Word Sigma) : M.to_totalDFA.δ_word none w = none := by
  induction w with
  | nil =>
    trivial
  | cons a v ih =>
    unfold TotalDFA.δ_word
    rw [δ_none_eq_none]
    exact ih

theorem final_ne_none (M : DFA Q Sigma) : q ∈ M.to_totalDFA.F → q ≠ none := by
  intro q_mem
  simp only [DFA.to_totalDFA] at q_mem
  rw [List.mem_map] at q_mem
  rcases q_mem with ⟨q', a, b⟩
  rw [←b]
  apply Option.some_ne_none

theorem δ_word_eq_δ_word (M : DFA Q Sigma) (q : Q) (w : Word Sigma) : M.δ_word q w = M.to_totalDFA.δ_word q w := by
  induction w generalizing q with
  | nil =>
    trivial
  | cons a v ih =>
    rw [DFA.δ_word, TotalDFA.δ_word]
    simp only [δ_eq_δ]
    cases hd : M.to_totalDFA.δ (some q) a with
    | none =>
      simp only [Option.bind]
      unfold TotalDFA.δ_word
      cases hv : v with
      | nil =>
        simp
      | cons a' v' =>
        simp only [hv]
        rw [δ_none_eq_none]
        rw [garbage_state]
    | some q' =>
      apply ih

theorem totalDFA_eq_DFA (M : DFA Q Sigma) : M.Language = (M.to_totalDFA).Language := by
  apply Set.ext
  intro w
  unfold TotalDFA.Language DFA.Language
  constructor
  . intro w_mem
    rcases w_mem with ⟨qf, w_acc, qf_mem⟩
    rw [δ_word_eq_δ_word] at w_acc
    rw [final_iff_final] at qf_mem
    --unfold TotalDFA.Language
    have aux : M.to_totalDFA.q0 = some M.q0 := by simp only [DFA.to_totalDFA]
    simp only [Membership.mem, aux]
    rw [w_acc]
    exact qf_mem
  . intro w_mem
    have aux : ∃ qf, M.to_totalDFA.δ_word M.to_totalDFA.q0 w = some qf := by
      rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none]
      simp only [Membership.mem] at w_mem
      apply final_ne_none (Sigma := Sigma) (M := M) (q := M.to_totalDFA.δ_word M.to_totalDFA.q0 w)
      exact w_mem
    rcases aux with ⟨qf, qf_eq⟩
    exists qf
    constructor
    . rw [δ_word_eq_δ_word]
      exact qf_eq
    . simp only [DFA.to_totalDFA, List.mem_map] at w_mem
      rcases w_mem with ⟨qf', qf'_mem, qf'_eq⟩
      simp only [DFA.to_totalDFA] at qf_eq
      rw [qf_eq, Option.some_inj] at qf'_eq
      rw [← qf'_eq]
      exact qf'_mem
