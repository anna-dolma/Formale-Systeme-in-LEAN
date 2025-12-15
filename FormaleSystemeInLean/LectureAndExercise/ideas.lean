import FormaleSystemeInLean.LectureAndExercise.lecture1

set_option linter.unusedSectionVars false

-- inspired by mathlib
class Fintype (α : Type u) where
  elems : List α
  complete : ∀ a : α, a ∈ elems

def List.toSet (l : List α) : Set α := fun e => e ∈ l

def Set.map (f : α → β) (S : Set α) [Fintype α] : Set β :=
  fun b => ∃ (a : α), a ∈ S ∧ f a = b

def Set.toList (S : Set α) [DecidablePred S] [Fintype α] : List α :=
  Fintype.elems.filter (· ∈ S)

structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] where
  𝓠 : Set Q
  δ : Q → Sigma → Option Q
  q0 : Q
  F : Set Q

structure TotalDFA (Q : Type u) (Sigma : Type v) [Fintype Q] where
  𝓠 : Set Q
  δ : Q → Sigma → Q
  q0 : Q
  F : Set Q

structure NFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] [Fintype (Set Q)] where
  𝓠: Set Q
  δ: Q -> Sigma → Set Q
  Q0 : Set Q
  F : Set Q

variable {Q : Type u} {Sigma : Type v} [Fintype Q] [Fintype Sigma] [Fintype (Option Q)] [BEq Q] [BEq (Set Q)] [DecidableEq Q] [Fintype (Set Q)]

def DFA.δ_word (dfa : DFA Q Sigma) (q : Q) : (Word Sigma) -> Option Q
| .nil => .some q
| .cons a v => (dfa.δ q a).bind (fun q' => dfa.δ_word q' v)

def TotalDFA.δ_word (dfa : TotalDFA Q Sigma) (q : Q) : (Word Sigma) -> Q
  | .nil => q
  | .cons a v => dfa.δ_word (dfa.δ q a) v

def NFA.δ_word (nfa : NFA Q Sigma) (R : Set Q) : (Word Sigma) → Set Q
  | .nil => R
  | .cons a v => nfa.δ_word (fun q' => ∃ q, q ∈ R ∧ q' ∈ nfa.δ q a ) v

def DFA.Language (dfa : DFA Q Sigma) : Language Sigma :=
  fun w => ∃ qf, dfa.δ_word dfa.q0 w = some qf ∧ qf ∈ dfa.F

def DFA.to_totalDFA (M : DFA Q Sigma) [DecidablePred M.F] [DecidablePred M.𝓠] : TotalDFA (Option Q) Sigma where
  𝓠 := M.𝓠.map fun q => some q
  δ := fun q a => q.bind (M.δ · a)
  q0 := .some M.q0
  F := M.F.map fun q => some q

def TotalDFA.Language (dfa : TotalDFA Q Sigma) : Language Sigma :=
  fun w => dfa.δ_word dfa.q0 w ∈ dfa.F

inductive NFA.Run (nfa : NFA Q Sigma) : Q -> Q -> Word Sigma -> Type _
| self (q : Q) : nfa.Run q q []
| step {q1 q2 qf : Q} {a : Sigma} {v : Word Sigma} (r : nfa.Run q2 qf v) (q2_mem : q2 ∈ nfa.δ q1 a) : nfa.Run q1 qf (a :: v)

def NFA.Run.from_start {nfa : NFA Q Sigma} (_ : nfa.Run q0 q w) : Prop := q0 ∈ nfa.Q0
def NFA.Run.accepts {nfa : NFA Q Sigma} (_ : nfa.Run q qf w) : Prop := qf ∈ nfa.F

def NFA.Language (nfa : NFA Q Sigma) : Language Sigma :=
  fun w => ∃ (q0 qf : Q) (r : nfa.Run q0 qf w), r.from_start ∧ r.accepts

def NFA.to_TotalDFA (M : NFA Q Sigma) : TotalDFA (Set Q) Sigma where
  𝓠 := M.𝓠.powerset
  δ := fun R a => fun q' => ∃ q, q ∈ R ∧ q' ∈ M.δ q a
  q0 := M.Q0
  F := fun R => ∃ q ∈ R, q ∈ M.F

--+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
-- TotalDFA Theorems

theorem final_iff_final (M : DFA Q Sigma) (q : Q) [DecidablePred M.F] [DecidablePred M.𝓠]  : q ∈ M.F ↔ some q ∈ M.to_totalDFA.F := by
  constructor
  . intro q_mem
    unfold DFA.to_totalDFA
    exists q
  . intro q_mem
    unfold DFA.to_totalDFA at q_mem
    rcases q_mem with ⟨q', q'_mem, sqf_eq⟩
    rw [Option.some_inj] at sqf_eq
    rw [← sqf_eq]
    exact q'_mem

theorem δ_eq_δ (M : DFA Q Sigma) (q : Q) (a : Sigma) [DecidablePred M.F] [DecidablePred M.𝓠]  : M.δ q a = M.to_totalDFA.δ q a := by
  unfold DFA.to_totalDFA
  simp

theorem δ_none_eq_none (M : DFA Q Sigma) (a : Sigma) [DecidablePred M.F] [DecidablePred M.𝓠]  : M.to_totalDFA.δ none a = none := by
  trivial -- to do: ohne trivial???

theorem garbage_state (M : DFA Q Sigma) (w : Word Sigma) [DecidablePred M.F] [DecidablePred M.𝓠]  : M.to_totalDFA.δ_word none w = none := by
  induction w with
  | nil =>
    trivial
  | cons a v ih =>
    unfold TotalDFA.δ_word
    rw [δ_none_eq_none]
    exact ih

theorem final_ne_none (M : DFA Q Sigma) [DecidablePred M.F] [DecidablePred M.𝓠] : q ∈ M.to_totalDFA.F → q ≠ none := by
  intro q_mem
  simp only [DFA.to_totalDFA] at q_mem
  rcases q_mem with ⟨q', a, b⟩
  rw [←b]
  apply Option.some_ne_none

theorem δ_word_eq_δ_word (M : DFA Q Sigma) (q : Q) (w : Word Sigma) [DecidablePred M.F] [DecidablePred M.𝓠] : M.δ_word q w = M.to_totalDFA.δ_word q w := by
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

theorem totalDFA_eq_DFA (M : DFA Q Sigma) [DecidablePred M.F] [DecidablePred M.𝓠] : M.Language = (M.to_totalDFA).Language := by
  apply Set.ext
  intro w
  unfold TotalDFA.Language DFA.Language
  constructor
  . intro w_mem
    rcases w_mem with ⟨qf, w_acc, qf_mem⟩
    rw [δ_word_eq_δ_word] at w_acc
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
    . rw [δ_word_eq_δ_word]
      exact qf_eq
    . simp only [DFA.to_totalDFA] at w_mem
      rcases w_mem with ⟨qf', qf'_mem, qf'_eq⟩
      simp only [DFA.to_totalDFA] at qf_eq
      rw [qf_eq, Option.some_inj] at qf'_eq
      rw [← qf'_eq]
      exact qf'_mem

--+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
-- NFA theorems

-- for every run q1...qn on a word w with q1 ∈ R, qn ∈ δ_word(R, w).
theorem run_imp_mem_δ (nfa : NFA Q Sigma) (q1 qn : Q) (R : Set Q) (w : Word Sigma) : nfa.Run q1 qn w → q1 ∈ R → qn ∈ nfa.δ_word R w := by
  intro r q1_mem
  induction r generalizing R with
  | self q =>
    trivial
  | @step qa qb qc a v r qb_mem hr =>
    have aux : qc ∈ nfa.δ_word (nfa.δ qa a) v := hr (nfa.δ qa a) qb_mem
    unfold NFA.δ_word
    let Z : Set Q := fun q' => ∃ q, q ∈ R ∧ q' ∈ nfa.δ q a
    have aux2 : ∀ q, q ∈ nfa.δ qa a → q ∈ Z := by
      intro q q_mem
      simp only [Z, Membership.mem]
      exists qa
    grind

-- given a set of states R and a state qn ∈ δ(R, w) we can also construct a run for w starting with a state in R.
theorem run_from_δ_word (nfa : NFA Q Sigma) (qn : Q) (R : Set Q) (w : Word Sigma) : qn ∈ nfa.δ_word R w → ∃ (q1 : Q) (_ : nfa.Run q1 qn w), q1 ∈ R := by
  intro qn_mem
  induction w generalizing R with
  | nil =>
    simp only [Membership.mem] at qn_mem
    unfold NFA.δ_word at qn_mem
    exists qn
    exists NFA.Run.self qn
  | cons a v ih =>
    simp only [Membership.mem, NFA.δ_word] at qn_mem
    let Z : Set Q := fun q' => ∃ q, R q ∧ nfa.δ q a q'
    have aux := ih Z qn_mem
    rcases aux with ⟨q, r', q_mem⟩
    have aux2 : ∃ q', q' ∈ R ∧ q ∈ nfa.δ q' a := by
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

theorem δ_NFA_eq_δ_TotalDFA (M : NFA Q Sigma) (a : Sigma) (R : Set Q) : M.to_TotalDFA.δ R a = M.δ_word R [a] := by
  simp only [NFA.to_TotalDFA, NFA.δ_word]

 theorem δ_word_eq_DFA_NFA (M : NFA Q Sigma) (w : Word Sigma) (R : Set Q): M.δ_word R w = M.to_TotalDFA.δ_word R w := by
  induction w generalizing R with
  | nil =>
    simp only [NFA.δ_word, TotalDFA.δ_word]
  | cons a v ih =>
    simp only [NFA.δ_word, TotalDFA.δ_word]
    grind -- warum

theorem to_DFA_lang_eq (M : NFA Q Sigma) : M.to_TotalDFA.Language = M.Language := by
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
      rcases w_mem with ⟨q0, q0_mems, q0_memf⟩
      exists q0
    | cons a v =>
      rcases w_mem with ⟨q, q_memd, q_memf⟩
      exists q
      rw [δ_word_eq_DFA_NFA]
      constructor
      . exact q_memd
      . exact q_memf
  . intro w_mem
    rw [acc_run_iff_δ_word_contains_final] at w_mem
    simp only [Membership.mem]
    rcases w_mem with ⟨q, q_memd, q_memf⟩
    cases w with
    | nil =>
      unfold NFA.δ_word at q_memd
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA]
      exists q
    | cons a v =>
      rw [δ_word_eq_DFA_NFA] at q_memd
      simp only [TotalDFA.δ_word, NFA.to_TotalDFA]
      exists q

def DFA.to_NFA (M : DFA Q Sigma) : NFA Q Sigma where
  𝓠 := M.𝓠
  δ := fun q a =>
    match M.δ q a with
    | none => ∅
    | some q => fun x => x = q
  Q0 := fun q => q = M.q0
  F := M.F

def TotalDFA.to_NFA (M : TotalDFA Q Sigma) : NFA Q Sigma where
  𝓠 := M.𝓠
  δ := fun q a => fun q' => q' = M.δ q a
  Q0 := fun q => q = M.q0
  F := M.F

theorem totalDFA_NFA_δ_eq (M : TotalDFA Q Sigma) (a : Sigma) (q : Q) : q' ∈ M.to_NFA.δ q a ↔ q' = M.δ q a := by
  simp only [TotalDFA.to_NFA, Membership.mem]

theorem totalDFA_NFA_δ_word_eq (M : TotalDFA Q Sigma) (w : Word Sigma) (q : Q) : q' ∈ M.to_NFA.δ_word (fun x => x=q) w ↔ M.δ_word q w = q' := by
  induction w generalizing q with
  | nil =>
    simp only [NFA.δ_word, TotalDFA.δ_word, Membership.mem]
    constructor
    . intro eq; symm; rw [eq]
    . intro eq; symm; rw [eq]
  | cons a v ih =>
    simp only [NFA.δ_word, TotalDFA.δ_word, Membership.mem]
    have aux := ih (M.δ q a)
    simp -- mit was muss ich simpen?
    exact aux

theorem totalDFA_NFA_lang_eq (M : TotalDFA Q Sigma) : M.to_NFA.Language = M.Language := by
  apply Set.ext
  intro w
  rw [acc_run_iff_δ_word_contains_final]
  unfold TotalDFA.Language
  have Q0_eq : M.to_NFA.Q0 = fun q => q = M.q0 := by
        simp only [TotalDFA.to_NFA]
  constructor
  . intro hq
    rcases hq with ⟨qf, qf_memd, qf_memf⟩
    simp only [Membership.mem]
    simp only [TotalDFA.to_NFA] at qf_memf
    cases w with
    | nil =>
      rcases qf_memd
      simp only [TotalDFA.δ_word]
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
    | cons a v =>
      simp only [TotalDFA.δ_word] at w_mem
      exists (M.δ_word (M.δ M.q0 a) v)
      constructor
      . rw [Q0_eq, totalDFA_NFA_δ_word_eq]
        rfl
      . simp only [TotalDFA.to_NFA]
        exact w_mem





theorem to_NFA_lang_eq (M : DFA Q Sigma) : M.to_NFA.Language = M.Language := by
  apply Set.ext
  intro w
  rw [acc_run_iff_δ_word_contains_final]
  unfold DFA.Language
  constructor
  . intro hq
    rcases hq with ⟨qf, qf_memd, qf_memf⟩
    simp only [Membership.mem]
    --unfold NFA.δ_word at qf_memd
    simp only [DFA.to_NFA] at qf_memf

    exists qf
    constructor
    . cases w with
      | nil =>
        rcases qf_memd
        simp only [DFA.δ_word]
      | cons a v =>
        simp only [NFA.δ_word] at qf_memd
        simp only [DFA.δ_word]

        sorry
    . exact qf_memf
  . sorry






def L_01 : Language Char := fun w => w = ['0'] ∨ w = ['1']
def L_1 : Language Char := fun w => w = ['1']
def L_n (n : Nat) : Language Char := fun w => w ∈ (L_01* * L_1) * L_01^(n-1)

def Set.card (S : Set α) [Fintype α] [DecidablePred S] : Nat :=
  (Fintype.elems.filter (fun x => x ∈ S)).length

theorem exists_NFA (n : Nat) [Fintype Char] : ∃ (M : NFA Q Char), M.Language = L_n n := by

  sorry
