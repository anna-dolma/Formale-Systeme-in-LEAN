import FormaleSystemeInLean.LectureAndExercise.lecture1


def lhs (V : Type v) (Sigma : Type V) := { w : Word (V ⊕ Sigma) // ∃ z, z ∈ w ∧ z.isLeft}
def rule (V : Type v) (Sigma : Type V) := Word (lhs V Sigma) × Word (V ⊕ Sigma)

structure Grammar (V : Type v) (Sigma : Type v) [Fintype V] [Fintype Sigma] where
  S : V
  P : List (rule V Sigma)

variable (V : Type v) (Sigma : Type v) [Fintype V] [Fintype Sigma]

instance : HMul (Word (lhs V Sigma)) (Word (V ⊕ Sigma)) (Word (V ⊕ Sigma)) where
  hMul u v := sorry

def Grammar.derivation  (G : Grammar V Sigma) := { t : (Word (V ⊕ Sigma) × Word (V ⊕ Sigma)) // ∃ (w₁ w₂ y : Word (V ⊕ Sigma)) (x : Word (lhs V Sigma)), t.1 = w₁*(x*w₂) ∧ t.2 = w₁*(y*w₂) ∧ (x, y) ∈ G.P  }
