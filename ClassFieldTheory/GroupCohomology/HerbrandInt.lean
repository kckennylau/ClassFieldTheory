import Mathlib
import ClassFieldTheory.GroupCohomology._13_HerbrandQuotient

variable {G : Type} [Group G] [Finite G] [DecidableEq G] [IsCyclic G]

open CategoryTheory
  groupCohomology
  LinearMap
  Representation

omit [DecidableEq G] [IsCyclic G] in
@[simp] lemma norm_trivial_int_eq_card : (Representation.trivial ℤ G ℤ).norm = Nat.card G := by
  ext; simpa [Representation.norm, Nat.card_eq]

omit [Finite G] [DecidableEq G]  in
@[simp] lemma oneSubGen_trivial_int_eq_card : (Representation.trivial ℤ G ℤ).oneSubGen = 0 := by
  ext; simp

omit [Finite G] [DecidableEq G] in
lemma herbrandZ0_trivial_int_eq_top : (Representation.trivial ℤ G ℤ).herbrandZ0 = ⊤ := by simp

omit [Finite G] [DecidableEq G] in
lemma herbrandB0_trivial_int_eq_top : (Representation.trivial ℤ G ℤ).herbrandB0 = ⊤ := by simp

theorem card_herbrandH0_trivial_int : Nat.card (trivial ℤ G ℤ).herbrandH0 = Nat.card G := by
  unfold herbrandH0







instance : Subsingleton (trivial ℤ G ℤ).herbrandZ1 := by
  unfold herbrandZ1
  rw [norm_trivial_int_eq_card]
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have : a = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using ha
  have : b = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using hb
  simp [*]

instance : Subsingleton (trivial ℤ G ℤ).herbrandH1 :=
  Quot.Subsingleton

theorem herbrandQuotient_trivial_int : herbrandQuotient (trivial ℤ G ℤ) = Nat.card G := by
  unfold herbrandQuotient
  rw [card_herbrandH0_trivial_int, Nat.card_of_subsingleton (0 : (trivial ℤ G ℤ).herbrandH1)]
  simp only [Nat.cast_one, div_one]
