import FormaleSystemeInLean.Lecture4
import FormaleSystemeInLean.FintypeSetDecidableEq


/-!
This file contains the formalisation of exercise 2.3 c and d which deals with simulations between NFAs.
The exercise sheet is available at https://iccl.inf.tu-dresden.de/w/images/2/28/FS2025-Blatt-02.pdf.
-/
section Exercise3

  variable {Sigma : Type u} {Q1 : Type u1} {Q2 : Type u2} [Fintype Q1] [Fintype Q2] [Fintype Sigma]

  structure NFASimulation (nfa1 : NFA Q1 Sigma) (nfa2 : NFA Q2 Sigma) where
    rel : Set (Q1 × Q2)
    start : ∀ q01 ∈ nfa1.Q0, ∃ q02 ∈ nfa2.Q0, (q01, q02) ∈ rel
    step : ∀ {q1 : Q1} {q2 : Q2} {a : Sigma}, (q1, q2) ∈ rel -> ∀ q1' ∈ (nfa1.δ q1 a), ∃ q2' ∈ (nfa2.δ q2 a), (q1', q2') ∈ rel
    final : ∀ {q1 : Q1} {q2 : Q2}, (q1, q2) ∈ rel -> q1 ∈ nfa1.F -> q2 ∈ nfa2.F

  section d

    /--
    If there is a simulation between nfa1 and nfa2 then the language of nfa1 is a subset of the language of nfa2.
    -/
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


    /-!
    How about the other direction - does language inclusion also imply a simulation between the NFAs recognising the languages?
    We can show that this is not true by giving a counterexample.
    In order to define NFAs we first need Fintypes for Q and Sigma. We cannot just use strings because there are infinitely many of those.
    Instead we use a subtype of String defined by a list of strings (statesList and sigma).
    -/

    def statesList := ["q0", "q1", "q2"]
    def sigma := ['a', 'b']

    def Q := subtype_of_list statesList
    def ⅀ := subtype_of_list sigma

    deriving instance Fintype, DecidableEq for Q, ⅀

    instance : Fintype (Set Q) := inferInstance

    instance : Inter (Powertype Q) where
      inter A B := fun e => e ∈ A ∧ e ∈ B

    --variable {h : ∀ (S : Set Q), DecidablePred S}
    variable [DecidableEq (Set Q)]

    /--
    Finally we can define the NFA 𝓜.
    -/
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
          | _ => []
      Q0 := [⟨"q0", by simp only [statesList]; grind⟩]
      F := [⟨"q2", by simp only [statesList]; grind⟩]

    /-!
    For our counterexample we will use 𝓜 and its powerset DFA 𝓜'. Their languages are equal but there is not simulation between 𝓜 and 𝓜'.
    Simulations are defined for NFAs so we convert 𝓜' back into an NFA 𝓜''.
    -/


    def 𝓜' : TotalDFA (Powertype Q) ⅀ := 𝓜.to_TotalDFA
    def 𝓜'' : NFA (Powertype Q) ⅀ := 𝓜'.to_NFA

    theorem part_b : ∃ (nfa1 : NFA (Powertype Q) ⅀) (nfa2 : NFA Q ⅀), nfa1.Language ⊆ nfa2.Language ∧ ¬∃ (_ : NFASimulation nfa1 nfa2), True := by
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
      . intro sim

        let q0 : Q := ⟨"q0", by simp only [statesList]; grind⟩
        let q1 : Q := ⟨"q1", by simp only [statesList]; grind⟩
        let q2 : Q := ⟨"q2", by simp only [statesList]; grind⟩
        let Q0 : Set Q := fun q => q = q0
        let b : ⅀ := ⟨'b', by simp only [sigma]; grind⟩

        rcases sim with ⟨sim, _⟩
        rcases sim with ⟨sim, start, step, final⟩

        have q01_mem : Q0 ∈ 𝓜''.Q0 := by
          unfold Q0 q0 𝓜'' TotalDFA.to_NFA 𝓜' 𝓜 NFA.to_TotalDFA List.toSet
          simp
        have q02_mem : q0 ∈ 𝓜.Q0 := by unfold q0 𝓜; simp
        have q02_eq : 𝓜.Q0 = [q0] := by unfold q0 𝓜; simp

        have start_mem : sim (Q0, q0) := by
          have aux := start Q0 q01_mem
          rcases aux with ⟨q02, q02_mem', mem_sim⟩
          rw [q02_eq, List.mem_singleton] at q02_mem'
          rw [q02_mem'] at mem_sim
          exact mem_sim

        have delta'_q0_eq : 𝓜''.δ Q0 b = [(fun q => q = q1 ∨ q = q2)] := by
          unfold Q0 q0 q1 q2 b 𝓜'' TotalDFA.to_NFA 𝓜' 𝓜 NFA.to_TotalDFA List.toSet
          simp
          apply Set.ext
          intro x
          constructor
          . intro hr
            rcases hr with ⟨r, r_mem, x_mem⟩
            simp only [Membership.mem] at r_mem
            simp only [r_mem] at x_mem
            simp at x_mem
            exact x_mem
          . intro x_eq
            exists q0
            constructor
            . simp only [q0, Membership.mem]
            . simp [q0]
              exact x_eq

        have delta_q0_eq : 𝓜.δ q0 b = [q1, q2] := by unfold b q0 q1 q2; simp only [𝓜]

        have mem_step : sim ((fun q => q = q1 ∨ q = q2), q2) := by
          have aux := step (a := b) start_mem
          have mem_delta : (fun q => q = q1 ∨ q = q2) ∈ 𝓜''.δ Q0 b := by grind
          specialize aux (fun q => q = q1 ∨ q = q2)
          have aux2 := aux mem_delta
          rcases aux2 with ⟨r, r_mem, mem_sim⟩
          rw [delta_q0_eq] at r_mem

          have nmem_q1 : ¬sim ((fun q => q = q1 ∨ q = q2), q1) := by
            intro contra
            have mem_F : (fun q => q = q1 ∨ q = q2) ∈ 𝓜''.F := by
              simp only [q1, q2, 𝓜'', TotalDFA.to_NFA, 𝓜', NFA.to_TotalDFA, List.mem_filter, Fintype.elems, List.mem_map]
              constructor
              . exists [q1, q2]
                constructor
                . apply powerlist
                  simp
                  have : statesList.attach = Fintype.elems (α := Q) := rfl
                  rw [← this]
                  simp [statesList]
                . unfold q1 q2 List.toSet
                  simp
              . unfold 𝓜 List.toSet
                simp
                intro contra'
                let X : (Powertype Q) := (fun e => e = q2)
                let Y : (Powertype Q) := fun q => q = q1 ∨ q = q2
                have inter : X ∩ Y = (fun q => q = q2) := by
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
                have nmem := contra' q2
                have mem : q2 ∈ X ∩ Y := by
                  simp only [X, Y, inter]
                  simp only [Membership.mem]
                simp only [X, Y] at mem
                contradiction

            have aux3 := final contra mem_F
            simp only [𝓜, List.mem_singleton] at aux3
            grind

          have r_neq : ¬r = q1 := by
            intro contra
            rw [contra] at mem_sim
            contradiction
          have r_eq : r = q2 := by
            simp at r_mem
            grind

          rw [r_eq] at mem_sim
          exact mem_sim

        have delta_undef : ∀ (a : ⅀), ¬∃ r, r ∈ 𝓜.δ q2 a := by
          intro a contra
          rcases contra with ⟨r, r_mem⟩
          simp only [q2, 𝓜] at r_mem
          simp_all

        have delta'_q1_q2 : (fun q => q = q0 ∨ q = q2) ∈ 𝓜''.δ (fun q => q = q1 ∨ q = q2) b := by
          simp only [q0, q1, q2, b, 𝓜'', TotalDFA.to_NFA, 𝓜', NFA.to_TotalDFA, 𝓜]
          simp
          apply Set.ext
          intro q
          constructor
          . intro q_mem
            exists q1
            constructor
            . apply Or.inl; rfl
            . cases q_mem with
              | inl q_mem =>
                simp [q1, q_mem]
              | inr q_mem =>
                simp [q1, q_mem]
          . intro q_mem
            rcases q_mem with ⟨r, r_mem, q_mem⟩
            cases r_mem with
            | inl r_mem =>
              simp only [r_mem, List.mem_cons, List.not_mem_nil, or_false] at q_mem
              simp only [Membership.mem]
              exact q_mem
            | inr r_mem =>
              simp [r_mem] at q_mem

        have mem_step2 := step (a := b) mem_step (fun q => q = q0 ∨ q = q2) delta'_q1_q2
        rcases mem_step2 with ⟨r, r_mem, mem_sim⟩
        specialize delta_undef b
        contradiction

  end d

end Exercise3
