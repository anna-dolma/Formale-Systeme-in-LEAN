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

theorem Finset.perm_iff_eq [DecidableEq α] (l k : Finset' α) (eq : Finset.eq l k) : l.removeDups.Perm k.removeDups := by
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
  have perm := perm_iff_eq l k eq
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
      simp
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

theorem mem_finset_iff_mem_mk (l' : List α) : ∀ a, a ∈ l' ↔ a ∈ Finset.mk l' := by
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
    rw [mem_finset_iff_mem_mk l1, mem_finset_iff_mem_mk l2]
    specialize mem_iff a
    exact mem_iff

instance [DecidableEq α] (x : α) (S : Finset α) : Decidable (x ∈ S) :=
  Quot.recOnSubsingleton S (fun l => List.instDecidableMemOfLawfulBEq x l)
