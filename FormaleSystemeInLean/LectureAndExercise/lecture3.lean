import FormaleSystemeInLean.LectureAndExercise.lecture1

set_option linter.unusedSectionVars false

/-!
Formalisation of Lecture 3:
Covers the definition of DFAs and total DFAs, the corresponding languages and how to obtain a total DFA from
a non-total DFA.
Grammars are (for now) not part of this formalisation, so in lecture 3 and 4 all things related to grammars and the
Chomsky Hierarchy is left out.
-/

/--
We define a DFA as a generic structure with two type parameters Q and Sigma. Definitions in the lecture and textbooks usually
define Q and Sigma as finite sets. We already know from lecture 1 that it is sufficient to define Sigma as an arbitrary type.
The states however need to be finite, otherwise it would not be a finite automaton. Therefore we require an instance of Fintype for Q.
For further information on Fintype please refer to the corresponding file.

δ is a function mapping a state of type Q and a symbol of type Sigma to something of type Option Q.
This is how we "encode" that δ is a partial function: if δ(q,a) = None, it is undefined.
-/
structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → Option Q
  q0 : Q
  F : List Q

/--
A total DFA is defined like a DFA except for the transition function δ.
-/
structure TotalDFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q → Sigma → Q
  q0: Q
  F: List Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma]

/--

-/
def DFA.δ_word (dfa : DFA Q Sigma) (q : Q) : (Word Sigma) -> Option Q
| .nil => .some q
| .cons a v => (dfa.δ q a).bind (fun q' => dfa.δ_word q' v)

def TotalDFA.δ_word (t_dfa : TotalDFA Q Sigma) (q : Q) : (Word Sigma) → Q
  | .nil => q
  | .cons a v => t_dfa.δ_word (t_dfa.δ q a) v

def TotalDFA.Language (t_dfa : TotalDFA Q Sigma) : Language Sigma :=
  fun w => t_dfa.δ_word t_dfa.q0 w ∈ t_dfa.F

/--
Given a DFA, a word w is contained in its language iff δ_word(q0,w) is defined and the DFA ends up in a final state when reading w.
-/
def DFA.Language (dfa : DFA Q Sigma) : Language Sigma :=
  fun w => ∃ qf, dfa.δ_word dfa.q0 w = some qf ∧ qf ∈ dfa.F

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

def TotalDFA.to_DFA (M : TotalDFA Q Sigma) : DFA Q Sigma where
  δ := fun q a => .some (M.δ q a)
  q0 := M.q0
  F := M.F

theorem final_iff_final (M : DFA Q Sigma) (q : Q) : q ∈ M.F ↔ some q ∈ M.to_totalDFA.F := by
  simp [DFA.to_totalDFA]

theorem δ_eq_δ (M : DFA Q Sigma) (q : Q) (a : Sigma) : M.δ q a = M.to_totalDFA.δ q a := by
  simp [DFA.to_totalDFA]

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

theorem to_totalDFA_δ_word_eq (M : DFA Q Sigma) (q : Q) (w : Word Sigma) : M.δ_word q w = M.to_totalDFA.δ_word q w := by
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
    rw [to_totalDFA_δ_word_eq] at w_acc
    rw [final_iff_final] at qf_mem
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
    . rw [to_totalDFA_δ_word_eq]
      exact qf_eq
    . simp only [DFA.to_totalDFA, List.mem_map] at w_mem
      rcases w_mem with ⟨qf', qf'_mem, qf'_eq⟩
      simp only [DFA.to_totalDFA] at qf_eq
      rw [qf_eq, Option.some_inj] at qf'_eq
      rw [← qf'_eq]
      exact qf'_mem

theorem to_DFA_δ_eq (M : TotalDFA Q Sigma) (q : Q) (a : Sigma) : M.δ q a = M.to_DFA.δ q a := by
  simp only [TotalDFA.to_DFA]

theorem to_DFA_δ_word_eq (M : TotalDFA Q Sigma) (q : Q) (w : Word Sigma) : M.δ_word q w = M.to_DFA.δ_word q w := by
  induction w generalizing q with
  | nil =>
    trivial
  | cons a v ih =>
    simp only [DFA.δ_word, TotalDFA.δ_word]
    exact ih (M.δ q a)

theorem DFA_eq_totalDFA (M : TotalDFA Q Sigma) : M.Language = (M.to_DFA).Language := by
  apply Set.ext
  intro w
  unfold DFA.Language TotalDFA.Language
  simp only [Membership.mem] at *
  constructor
  . intro w_mem
    exists (M.δ_word M.q0 w)
    constructor
    . rw [to_DFA_δ_word_eq]
      rfl
    . exact w_mem
  . intro w_mem
    rcases w_mem with ⟨qf, qf_eq, qf_mem⟩
    rw [← to_DFA_δ_word_eq, Option.some_inj] at qf_eq
    have q0_eq : M.to_DFA.q0 = M.q0 := by simp only [TotalDFA.to_DFA]
    rw [← q0_eq]
    rw [qf_eq]
    exact qf_mem
