import FormaleSystemeInLean.LectureAndExercise.lecture4

/-
structure DFA (Q : Type u) (Sigma : Type v) [Fintype Q] [Fintype Sigma] where
  δ: Q -> Sigma → Option Q
  q0 : Q
  F : List Q

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
-/

section Exercise3

  variable {Sigma : Type u} {Q1 : Type u1} {Q2 : Type u2} [Fintype Q1] [Fintype Q2] [Fintype Sigma]

  structure NFASimulation (nfa1 : NFA Q1 Sigma) (nfa2 : NFA Q2 Sigma) where
    rel : Set (Q1 × Q2)
    start : ∀ q01 ∈ nfa1.Q0, ∃ q02 ∈ nfa2.Q0, (q01, q02) ∈ rel
    step : ∀ {q1 : Q1} {q2 : Q2} {a : Sigma}, (q1, q2) ∈ rel -> ∀ q1' ∈ (nfa1.δ q1 a), ∃ q2' ∈ (nfa2.δ q2 a), (q1', q2') ∈ rel
    final : ∀ {q1 : Q1} {q2 : Q2}, (q1, q2) ∈ rel -> q1 ∈ nfa1.F -> q2 ∈ nfa2.F

  section d

    theorem part_a {nfa1 : NFA Q1 Sigma} {nfa2 : NFA Q2 Sigma} (sim : NFASimulation nfa1 nfa2) : nfa1.Language ⊆ nfa2.Language := by
      have generalized_theorem : ∀ {q1 q1' : Q1} {q2 : Q2} {w : Word Sigma}, (q1, q2) ∈ sim.rel -> ∀ r1 : nfa1.Run q1 q1' w, ∃ q2' : Q2, (q1', q2') ∈ sim.rel ∧ ∃ r2 : nfa2.Run q2 q2' w, True := by
        intro q1 q1' q2 w q1_eq_q2 r1
        induction r1 generalizing q2 with
        | self q => exists q2; constructor; exact q1_eq_q2; exists (.self q2)
        | step r1 q2_mem ih =>
          rcases sim.step q1_eq_q2 _ q2_mem with ⟨_, q2'_mem, q1'_eq_q2'⟩
          specialize ih q1'_eq_q2'
          rcases ih with ⟨q2'', q2''_eq, r2, _⟩
          exists q2''
          constructor
          . exact q2''_eq
          . exists (.step r2 q2'_mem)

      intro w w_mem
      rcases w_mem with ⟨q01, qf1, r1, r1_start, r1_accept⟩
      rcases sim.start q01 r1_start with ⟨q02, r2_start, q01_eq_q02⟩
      exists q02
      rcases generalized_theorem q01_eq_q02 r1 with ⟨qf2, qf1_eq_qf2, r2, _⟩
      exists qf2, r2
      constructor
      . exact r2_start
      . exact sim.final qf1_eq_qf2 r1_accept



    def statesList := ["q0", "q1", "q2"]
    def sigma := ['a', 'b']

    def Q := { q : String // q ∈ statesList }
    def ⅀ := { a : Char // a ∈ sigma }

    instance : Fintype Q where
      elems := statesList.attach
      complete := by
        intro q
        rcases q with ⟨v, p⟩
        unfold statesList at p
        simp only [List.attach, Q, statesList, List.attachWith, List.pmap]
        grind

    instance : Fintype ⅀ where
      elems := sigma.attach
      complete := by
        intro a
        rcases a with ⟨v, p⟩
        unfold sigma at p
        simp only [List.attach, ⅀, sigma, List.attachWith, List.pmap]
        grind

    instance : BEq Q where
      beq := fun q r => if q.val = r.val then true else false

    instance : Fintype (Option Q) where
      elems := statesList.attach.map (some · ) ++ [.none]
      complete := by
        intro q
        simp --only [List.mem_map]
        have some_mem (r : Q) : some r ∈ statesList.attach.map (some · ) ++ [.none] := by simp
        by_cases hq : q = none
        . apply Or.inr; exact hq
        . rw [← Ne.eq_1, Option.ne_none_iff_exists] at hq
          rcases hq with ⟨r, r_eq⟩
          rcases r with ⟨v, p⟩
          apply Or.inl
          exists v, p

    instance : Fintype (Set Q) := inferInstance

    instance : Inter (Powertype Q) where
      inter A B := fun e => e ∈ A ∧ e ∈ B

    instance : BEq (Set Q) where
      beq := sorry--fun X Y => if X = Y then true else false

    instance : BEq (Powertype Q) := sorry

    instance : LawfulBEq (Set Q) where
      rfl := by sorry
      eq_of_beq := sorry

    instance : Fintype (Option (Powertype Q)) := sorry
    instance : BEq (Set (Powertype Q)) := sorry
    instance : DecidableEq (Powertype Q) := sorry

    deriving instance DecidableEq for Q

    def 𝓜 : NFA Q ⅀ where
      δ := fun q σ =>
        match q.val with
          | "q0" => match σ.val with
            | 'a' => [⟨"q2", by simp only [statesList]; grind⟩]
            | 'b' => [⟨"q1", by simp only [statesList]; grind⟩, ⟨"q2", by simp only [statesList]; grind⟩]
            | _ => []
          | "q1" => match σ.val with
            | 'b' => [⟨"q0", by simp only [statesList]; grind⟩, ⟨"q2", by simp only [statesList]; grind⟩]
            | _ => []
          | "q2" => []
          | _ => []
      Q0 := [⟨"q0", by simp only [statesList]; grind⟩]
      F := [⟨"q2", by simp only [statesList]; grind⟩]

    def 𝓜' : TotalDFA (Powertype Q) ⅀ := 𝓜.to_TotalDFA
    def 𝓜'' : NFA (Powertype Q) ⅀ := 𝓜'.to_NFA

    theorem part_b : ∃ (nfa1 : NFA (Powertype Q) ⅀) (nfa2 : NFA Q ⅀), nfa1.Language ⊆ nfa2.Language ∧ ∀ (r : Set ((Powertype Q) × Q)), ¬∃ (sim : NFASimulation nfa1 nfa2), sim.rel = r := by
      exists 𝓜'', 𝓜
      constructor
      . intro w w_mem
        have lang_eq1 : 𝓜.to_TotalDFA.Language = 𝓜.Language := by
          apply NFA_totalDFA_lang_eq 𝓜
        have lang_eq2 : 𝓜''.Language = 𝓜'.Language := by
          unfold 𝓜''
          apply totalDFA_NFA_lang_eq 𝓜'
        unfold 𝓜'' 𝓜' at *
        rw [← lang_eq2] at lang_eq1
        rw [← lang_eq1]
        exact w_mem
      . intro rel
        intro contra
        rcases contra with ⟨sim, sim_eq⟩
        rcases sim with ⟨sim, start, step, final⟩

        have q01_mem : (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩) ∈ 𝓜''.Q0 := by
          unfold 𝓜'' TotalDFA.to_NFA 𝓜' 𝓜 NFA.to_TotalDFA List.toSet
          simp
        have q02_mem : ⟨"q0", by simp only [statesList]; grind⟩ ∈ 𝓜.Q0 := by unfold 𝓜; simp
        have q02_eq : 𝓜.Q0 = [⟨"q0", by simp only [statesList]; grind⟩] := by unfold 𝓜; simp

        have start_mem : sim (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩, ⟨"q0", by simp only [statesList]; grind⟩) := by
          have aux := start (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩) q01_mem
          rcases aux with ⟨q02, q02_mem', mem_sim⟩
          rw [q02_eq, List.mem_singleton] at q02_mem'
          rw [q02_mem'] at mem_sim
          exact mem_sim

        have delta'_q0_eq : 𝓜''.δ (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩) ⟨'b', by simp only [sigma]; grind⟩ = [(fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩)] := by
          unfold 𝓜'' TotalDFA.to_NFA 𝓜' 𝓜 NFA.to_TotalDFA List.toSet
          simp
          apply funext
          intro x
          apply propext
          constructor
          . intro hr
            rcases hr with ⟨r, r_mem, x_mem⟩
            simp only [Membership.mem] at r_mem
            simp only [r_mem] at x_mem
            simp at x_mem
            exact x_mem
          . intro x_eq
            exists ⟨"q0", by simp only [statesList]; grind⟩
            constructor
            . simp only [Membership.mem]
            . simp
              exact x_eq

        have delta_q0_eq : 𝓜.δ ⟨"q0", by simp only [statesList]; grind⟩ ⟨'b', by simp only [sigma]; grind⟩ = [⟨"q1", by simp only [statesList]; grind⟩, ⟨"q2", by simp only [statesList]; grind⟩] := by simp only [𝓜]

        have mem_step : sim ((fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩), ⟨"q2", by simp only [statesList]; grind⟩) := by
          have aux := step (a := ⟨'b', by simp only [sigma]; grind⟩) start_mem
          have mem_delta : (fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩) ∈ 𝓜''.δ (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩) ⟨'b', by simp only [sigma]; grind⟩ := by grind
          specialize aux (fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩)
          have aux2 := aux mem_delta
          rcases aux2 with ⟨r, r_mem, mem_sim⟩
          rw [delta_q0_eq] at r_mem

          have nmem_q1 : ¬sim ((fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩), ⟨"q1", by simp only [statesList]; grind⟩) := by
            intro contra
            have mem_F : (fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩) ∈ 𝓜''.F := by
              simp only [𝓜'', TotalDFA.to_NFA, 𝓜', NFA.to_TotalDFA, List.mem_filter, Fintype.elems, List.mem_map]
              constructor
              . sorry
              . unfold 𝓜 List.toSet
                simp
                intro contra'
                let X : (Powertype Q) := (fun e => e = ⟨"q2", by simp only [statesList]; grind⟩)
                let Y : (Powertype Q) := fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩
                have inter : X ∩ Y = (fun q => q = ⟨"q2", by simp only [statesList]; grind⟩) := by
                  apply Set.ext
                  intro t
                  constructor
                  . intro t_mem
                    rcases t_mem with ⟨l, r⟩
                    simp only [X, Y, Membership.mem] at *
                    grind
                  . intro t_mem
                    simp only [Membership.mem] at t_mem
                    constructor
                    . simp only [X, Membership.mem]; exact t_mem
                    . simp only [Y, Membership.mem]; apply Or.inr; exact t_mem
                simp only [X, Y] at inter
                rw [Set.empty_iff] at contra'
                have nmem := contra' ⟨"q2", by simp only [statesList]; grind⟩
                have mem : ⟨"q2", by simp only [statesList]; grind⟩ ∈ X ∩ Y := by
                  simp only [X, Y, inter]
                  simp only [Membership.mem]
                simp only [X, Y] at mem
                contradiction

            have aux3 := final contra mem_F
            simp only [𝓜, List.mem_singleton] at aux3
            contradiction

          have r_neq : ¬r = ⟨"q1", by simp only [statesList]; grind⟩ := by
            intro contra
            rw [contra] at mem_sim
            contradiction
          have r_eq : r = ⟨"q2", by simp only [statesList]; grind⟩ := by
            simp at r_mem
            grind

          rw [r_eq] at mem_sim
          exact mem_sim

        have delta_undef : ∀ (a : ⅀), ¬∃ r, r ∈ 𝓜.δ ⟨"q2", by simp only [statesList]; grind⟩ a := by
          intro a contra
          rcases contra with ⟨r, r_mem⟩
          simp only [𝓜] at r_mem
          simp_all

        have delta_q1_q2 : (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩) ∈ 𝓜''.δ (fun q => q = ⟨"q1", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩) ⟨'b', by simp only [sigma]; grind⟩ := by
          simp only [𝓜'', TotalDFA.to_NFA, 𝓜', NFA.to_TotalDFA, 𝓜]
          simp
          apply Set.ext
          intro q
          constructor
          . intro q_mem
            simp only [Membership.mem]
            exists ⟨"q1", by simp only [statesList]; grind⟩
            constructor
            . apply Or.inl; rfl
            . simp only [Membership.mem] at q_mem
              simp
              by_cases hq : q = ⟨"q0", by simp only [statesList]; grind⟩
              . rw [hq]

                sorry
              . simp only [hq, false_or] at q_mem
                rw [q_mem]
                constructor

                sorry
          . intro q_mem
            rcases q_mem with ⟨r, r_mem, q_mem⟩
            simp only [Membership.mem] at *

            sorry

        have mem_step2 := step (a := ⟨'b', by simp only [sigma]; grind⟩) mem_step (fun q => q = ⟨"q0", by simp only [statesList]; grind⟩ ∨ q = ⟨"q2", by simp only [statesList]; grind⟩) delta_q1_q2
        rcases mem_step2 with ⟨r, r_mem, mem_sim⟩
        specialize delta_undef ⟨'b', by simp only [sigma]; grind⟩
        contradiction

  end d

end Exercise3
