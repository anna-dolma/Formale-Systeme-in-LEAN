import FormaleSystemeInLean.Set
import FormaleSystemeInLean.List

def Finset' (α : Type u) := List α

instance : Membership α (Finset' α) where
  mem s a := s.Mem a

def Finset.eq (l k : Finset' α) : Prop :=
  ∀ (a : α), a ∈ l ↔ a ∈ k

def Finset.eq.eqv : Equivalence (@Finset.eq α) where
  refl := by
    unfold eq; intro X a; rfl
  symm := by
    unfold eq; intro X Y h x; symm; exact h x
  trans := by
    unfold eq
    intro X Y Z eq_XY eq_YZ x; rw [eq_XY]; exact eq_YZ x

instance Finset.instSetoid (α : Type u) : Setoid (Finset' α) where
  r := Finset.eq
  iseqv := Finset.eq.eqv

def Finset (α : Type u) : Type u := Quotient (@Finset.instSetoid α)

def Finset.mk (l : Finset' α) : Finset α := Quotient.mk _ l

theorem Finset.perm_if_eq [DecidableEq α] (l k : Finset' α) (eq : Finset.eq l k) : l.removeDups.Perm k.removeDups := by
  unfold Finset.eq at eq
  have mem_rd_l := List.mem_removeDups l
  have mem_rd_k := List.mem_removeDups k
  have count_l := List.removeDups_count l
  have count_k := List.removeDups_count k
  have count_eq : ∀ a, l.removeDups.count a = k.removeDups.count a := by
    intro a
    by_cases a_mem : a ∈ l
    . specialize count_l a a_mem
      have a_mem_k := (eq a).mp a_mem
      specialize count_k a a_mem_k
      rw [count_l, count_k]
    . have a_nmem : ¬a ∈ l.removeDups := by
        intro contra
        specialize mem_rd_l a
        have aux := mem_rd_l.mpr contra
        contradiction
      have a_nmem2 : ¬a ∈ k.removeDups := by
        intro contra
        specialize mem_rd_k a
        have aux := (eq a).mpr (mem_rd_k.mpr contra)
        contradiction
      have count_l : l.removeDups.count a = 0 := by
        rw [List.count_eq_zero]; exact a_nmem
      have count_k : k.removeDups.count a = 0 := by
        rw [List.count_eq_zero]; exact a_nmem2
      rw [count_k, count_l]
  simp only [List.perm_iff_count]
  exact count_eq

theorem Finset.length_eq_if_eq [DecidableEq α] (l k : Finset' α) (eq : Finset.eq l k) : l.removeDups.length = k.removeDups.length := by
  have perm := Finset.perm_if_eq l k eq
  apply List.Perm.length_eq
  exact perm

def Finset.card [DecidableEq α] : Finset α -> Nat :=
  Quot.lift
    (fun l' => l'.removeDups.length)
    (by
      intro l k h
      unfold Setoid.r instSetoid eq at h
      simp only at h
      have eq : Finset.eq l k := by unfold eq; exact h
      have aux := length_eq_if_eq l k eq
      grind
    )

def Finset.mem (a : α) : Finset α -> Prop :=
  Quot.lift
    (fun s => a ∈ s)
    (by
      intro x y h
      unfold Setoid.r instSetoid eq at h
      simp only at h
      grind
    )

def Finset.union : Finset α -> Finset α -> Finset α :=
  Quotient.lift₂
    (fun a b => Finset.mk (a.append b))
    (by
      intro u v w x eq_vx eq_uw
      simp only [List.append_eq]
      unfold mk Quotient.mk Setoid.r instSetoid Finset.eq
      simp only
      simp only [HasEquiv.Equiv, Setoid.r, eq] at *
      have aux : ∀ a, a ∈ (u.append v) ↔ a ∈ (w.append x) := by
        intro a
        simp only [List.append_eq, List.mem_append]
        grind
      have test : Finset.eq (u.append v) (w.append x) := by
        unfold eq; exact aux
      have aux2 := Quot.sound test
      exact aux2
    )

def Finset.insert (a : α) : Finset α → Finset α :=
  Quot.lift
    (fun s => Finset.mk (a::s))
    (by
      intro x y h
      unfold Setoid.r instSetoid eq at h
      simp only at *
      unfold mk Quotient.mk Setoid.r instSetoid eq
      simp
      have aux : Finset.eq (a::x) (a::y) := by
        unfold eq
        intro c
        specialize h c
        rw [List.mem_cons]
        by_cases hc : c = a
        . rw [hc]
          simp only [true_or, true_iff]
          rw [List.mem_cons]
          apply Or.inl; rfl
        . simp only [hc, false_or, h]
          rw [List.mem_cons]
          simp only [iff_or_self]
          grind
      have aux2 := Quot.sound aux
      exact aux2)

instance : EmptyCollection (Finset α) where
  emptyCollection := Finset.mk []

instance : Membership α (Finset α) where
  mem s a := s.mem a

instance : Union (Finset α) where
  union X Y := Finset.union X Y

instance : HasSubset (Finset α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

theorem mem_list_iff_mem_mk (l' : List α) : ∀ a, a ∈ l' ↔ a ∈ Finset.mk l' := by
  intro a
  simp only [Finset.mk, Finset.instSetoid, Quotient.mk]
  unfold Finset.eq
  simp only [Membership.mem, Finset.mem]

theorem ext_iff (X Y : Finset α)  : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) := by
  have exists_rep_X := Quot.exists_rep X
  have exists_rep_Y := Quot.exists_rep Y
  rcases exists_rep_X with ⟨l1, X_eq⟩
  rcases exists_rep_Y with ⟨l2, Y_eq⟩
  rw [← X_eq, ← Y_eq]
  constructor
  . intro eq
    have finset_eq := Quotient.exact eq
    simp only [HasEquiv.Equiv, Setoid.r, Finset.eq] at finset_eq
    grind
  . intro mem_iff
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, Finset.eq]
    intro a
    rw [mem_list_iff_mem_mk l1, mem_list_iff_mem_mk l2]
    specialize mem_iff a
    exact mem_iff

instance [DecidableEq α] (x : α) (S : Finset α) : Decidable (x ∈ S) :=
  Quot.recOnSubsingleton S (fun l => List.instDecidableMemOfLawfulBEq x l)

instance [DecidableEq α] (l : Finset' α) (a : α) : Decidable (a ∈ l) := List.instDecidableMemOfLawfulBEq a l

def Finset.inter [DecidableEq α] : Finset α -> Finset α -> Finset α :=
  Quotient.lift₂
    (fun x y => Finset.mk (x.filter (fun a => decide (a ∈ y)))) --(x.removeAll (x.removeAll y)))
    (by
      intro u v w x eq_uw eq_vx
      apply Quot.sound
      simp only [HasEquiv.Equiv, Setoid.r, eq] at *
      intro a
      constructor
      . rw [List.mem_filter]
        intro h
        rw [List.mem_filter]
        rcases h with ⟨a_mem, dec_eq⟩
        constructor
        . apply (eq_uw a).mp; exact a_mem
        . simp only [decide_eq_true_eq] at *
          apply (eq_vx a).mp; exact dec_eq
      . rw [List.mem_filter]
        intro h
        rw [List.mem_filter]
        rcases h with ⟨a_mem, dec_eq⟩
        constructor
        . apply (eq_uw a).mpr; exact a_mem
        . simp only [decide_eq_true_eq] at *
          apply (eq_vx a).mpr; exact dec_eq
      )

instance [DecidableEq α] : Inter (Finset α) where
  inter A B := Finset.inter A B

theorem Finset.eq_rfl (X : Finset α) : X = X := by
  apply (ext_iff X X).mpr
  simp only [implies_true]

def l1 := [1, 2, 3, 4, 5]
def l2 := [3, 4, 5, 6, 7]
#eval l1.removeAll (l1.removeAll l2)
#check Quotient.exact

theorem eq_if_perm [DecidableEq α] (l k : Finset' α) (perm : l.removeDups.Perm k.removeDups) : Finset.eq l k := by
  simp only [Finset.eq]
  intro a
  have aux := List.Perm.mem_iff (a := a) perm
  rw [← List.mem_removeDups, ← List.mem_removeDups] at aux
  exact aux

theorem Finset.perm_iff_eq [DecidableEq α] (l k : Finset' α) : l.removeDups.Perm k.removeDups ↔ Finset.eq l k := by
  constructor
  . intro perm; exact eq_if_perm l k perm
  . intro eq; exact perm_if_eq l k eq

instance [DecidableEq α] (l k : Finset' α) : Decidable (Finset.eq l k) := by
  rw [← Finset.perm_iff_eq]
  by_cases h : (List.removeDups l).Perm (List.removeDups k)
  . apply isTrue h
  . apply isFalse h

instance [DecidableEq α] (l k : Finset' α) : Decidable (l ≈ k) := by
  simp only [HasEquiv.Equiv, Setoid.r]
  rw [← Finset.perm_iff_eq]
  by_cases h : (List.removeDups l).Perm (List.removeDups k)
  . apply isTrue h
  . apply isFalse h

theorem Quotient.eq_iff_equiv {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b ↔ Quotient.mk s a = Quotient.mk s b := by
  constructor
  . intro h; apply Quotient.sound; exact h
  . intro h; apply Quotient.exact; exact h

-- "inspired" by mathlib :|
instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | a, b => Quotient.recOnSubsingleton₂ a b fun _ _ => decidable_of_iff _ Quotient.eq_iff_equiv

theorem Finset.eq_iff_exists_eq_rep [DecidableEq α] (X Y : Finset α) : X = Y ↔ ∃ (l k : Finset' α), Finset.mk l = X ∧ Finset.mk k = Y ∧ Finset.eq l k := by
  have rep_X := Quot.exists_rep X
  have rep_Y := Quot.exists_rep Y
  rcases rep_X with ⟨l, X_eq⟩
  rcases rep_Y with ⟨k, Y_eq⟩
  constructor
  . intro eq
    rw [ext_iff] at eq
    exists l, k
    constructor
    . exact X_eq
    . constructor
      . exact Y_eq
      . rw [← X_eq, ← Y_eq] at eq
        unfold Finset.eq
        intro a
        specialize eq a
        rw [mem_list_iff_mem_mk, mem_list_iff_mem_mk]
        exact eq
  . intro h
    rcases h with ⟨l, k, X_eq, Y_eq, lk_eq⟩
    rw [ext_iff, ← X_eq, ← Y_eq]
    intro a
    rw [← mem_list_iff_mem_mk, ← mem_list_iff_mem_mk]
    simp only [Finset.eq] at lk_eq
    specialize lk_eq a; exact lk_eq

def Finset.BEq [DecidableEq α] : Finset α -> Finset α -> Bool :=
  Quotient.lift₂
    (fun x y => decide (x.removeDups.Perm y.removeDups))
    (by
      intro v w x y eq_vx eq_wy
      simp only [decide_eq_decide]
      have perm_1 := perm_if_eq v x eq_vx
      have perm_2 := perm_if_eq w y eq_wy
      grind
    )

/-instance [DecidableEq α] : BEq (Finset α) where
  beq X Y := Finset.BEq X Y -/

instance [DecidableEq α] : BEq (Finset α) where
  beq X Y := decide (X = Y)

instance [DecidableEq α] : LawfulBEq (Finset α) where
  rfl := by
    intro X
    simp only [BEq.rfl]
  eq_of_beq := by
    intro X Y beq
    simp only [BEq.beq, decide_eq_true_eq] at beq
    exact beq

theorem Finset.empty_eq (A : Finset α) : (∀ (x : α), ¬x ∈ A) → A = ∅ := by
  intro h
  apply (ext_iff A ∅).mpr
  intro a
  simp only [EmptyCollection.emptyCollection]
  constructor
  . intro e_mem
    rw [← mem_list_iff_mem_mk]
    specialize h a
    contradiction
  . intro e_mem
    simp only [Membership.mem] at e_mem
    contradiction

theorem Finset.ne_empty_contains_element (B : Finset α) [DecidableEq α] [ReflBEq (Finset α)] [DecidableEq (Finset α)] : B != ∅ -> ∃ a, a ∈ B := by
  intro neq
  apply Classical.byContradiction
  intro contra
  rw [not_exists] at contra
  have aux := Finset.empty_eq B contra
  rw [aux] at neq
  have aux2 := beq_self_eq_true B
  rw [aux] at aux2
  simp only [bne_self_eq_false, Bool.false_eq_true] at neq

def Finset.toSet (S : Finset α) : Set α := fun x => x ∈ S

theorem Finset.mem_toSet (S : Finset α) : ∀ x, x ∈ S ↔ x ∈ S.toSet := by
  intro x
  constructor
  . intro x_mem; unfold Finset.toSet; simp only [Membership.mem]; exact x_mem
  . intro x_mem; unfold Finset.toSet at x_mem; simp only [Membership.mem] at x_mem; exact x_mem

theorem Quotient.unlift₂.{uA, uB, uC} {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ : Setoid α} {s₂ : Setoid β} (f : α → β → φ)
  (c : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) (a : α) (b : β) :
  Quotient.lift₂ f c (Quotient.mk s₁ a) (Quotient.mk s₂ b) = f a b := rfl

theorem Finset.inter_eq [DecidableEq α] (l k : Finset' α) : mk l ∩ mk k = mk (l.filter (fun x => decide (x ∈ k))) := by
  rfl --- ich heule TT

theorem Finset.mem_inter [DecidableEq α] (X Y : Finset α) (a : α) : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y := by
  have rep_X := Quot.exists_rep X
  have rep_Y := Quot.exists_rep Y
  rcases rep_X with ⟨l, X_eq⟩
  rcases rep_Y with ⟨k, Y_eq⟩
  have := inter_eq l k
  rw [← X_eq, ← Y_eq]
  constructor
  . intro a_mem
    change a ∈ (mk l ∩ mk k) at a_mem
    rw [inter_eq l k, ← mem_list_iff_mem_mk, List.mem_filter] at a_mem
    rcases a_mem with ⟨mem_l, dec_t⟩
    simp at dec_t
    constructor
    . exact mem_l
    . exact dec_t
  . intro a_mem
    change a ∈ (mk l ∩ mk k)
    rw [inter_eq, ← mem_list_iff_mem_mk, List.mem_filter, decide_eq_true_eq]
    change a ∈ mk l ∧ a ∈ mk k at a_mem
    rw [← mem_list_iff_mem_mk, ← mem_list_iff_mem_mk] at a_mem
    exact a_mem
