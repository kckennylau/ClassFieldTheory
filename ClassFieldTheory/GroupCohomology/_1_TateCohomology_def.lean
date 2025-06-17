import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs
open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  -- dimensionShift
  LinearMap

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [Finite G] [DecidableEq G]

noncomputable section

namespace Representation
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

def norm : A →ₗ[R] A :=
  let _ := Fintype.ofFinite G
  ∑ g : G, ρ g

lemma norm_comm (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := sorry

lemma norm_comm' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := sorry

end Representation

namespace groupCohomology

/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶
    (inhomogeneousCochains M).X 0 := by
  /-
  The linear map part will be `M.ρ.norm` after groupHomology is merged.
  -/
  sorry

lemma TateNorm_comp_d (M : Rep R G) : TateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 :=
  sorry

lemma d_comp_TateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ TateNorm M  = 0 :=
  sorry

def TateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ where
  X
  | Int.ofNat n => (inhomogeneousCochains M).X n
  | Int.negSucc n => (inhomogeneousChains M).X n
  d
  | Int.ofNat i, Int.ofNat j            => (inhomogeneousCochains M).d i j
  | Int.ofNat _, Int.negSucc _          => 0
  | -1,0                                => TateNorm M
  | -1, Int.ofNat (j + 1)               => 0
  | -1, Int.negSucc _                   => 0
  | Int.negSucc (i + 1), Int.ofNat j    => 0
  | Int.negSucc (i + 1), Int.negSucc j  => (inhomogeneousChains M).d (i + 1) j
  shape
  | Int.ofNat i, Int.ofNat j => by
      convert (inhomogeneousCochains M).shape i j
      simp only [Int.ofNat_eq_coe, ComplexShape.up_Rel]
      norm_cast
  | Int.ofNat _, Int.negSucc _ => by tauto
  | Int.negSucc 0, 0 => by intro; contradiction
  | -1, Int.ofNat (j + 1) => by tauto
  | -1, Int.negSucc _ => by tauto
  | Int.negSucc (i + 1), Int.ofNat j => by tauto
  | Int.negSucc (i + 1), Int.negSucc j => by
      convert (inhomogeneousChains M).shape (i + 1) j
      rw [ComplexShape.up_Rel, ComplexShape.down_Rel, Int.negSucc_eq, Int.negSucc_eq,
        Nat.cast_add, Nat.cast_one, neg_add, neg_add, neg_add, add_comm, ←add_assoc, add_left_inj,
        add_comm, add_assoc, neg_add_cancel, add_zero, neg_eq_iff_eq_neg, neg_neg, Nat.cast_inj,
        add_left_inj, Eq.comm]
  d_comp_d' i j k hij hjk := by
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j =>
        cases k with
        | ofNat k =>
          simp only [Int.ofNat_eq_coe, ComplexShape.up_Rel] at hij hjk
          norm_cast at hij hjk
          apply (inhomogeneousCochains M).d_comp_d' i j k hij hjk
        | negSucc _ =>
          contradiction
      | negSucc _ =>
        contradiction
    | negSucc i =>
      cases i with
      | zero =>
        simp only [Int.reduceNegSucc, ComplexShape.up_Rel, Int.reduceNeg, neg_add_cancel] at hij hjk
        rw [←hjk,←hij]
        exact TateNorm_comp_d M
      | succ i =>
        cases i with
        | zero =>
          simp only [zero_add, Int.reduceNegSucc, ComplexShape.up_Rel, Int.reduceNeg,
            Int.reduceAdd] at hij hjk
          rw [←hjk,←hij]
          exact d_comp_TateNorm M
        | succ i =>
          cases j with
          | ofNat _ => contradiction
          | negSucc j =>
            cases k with
            | ofNat k =>
              exfalso
              simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
                Int.ofNat_eq_coe, ComplexShape.up_Rel, neg_add_cancel_comm,
                Nat.neg_cast_eq_cast] at hjk
              simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
                hjk.1, CharP.cast_eq_zero, zero_add, ComplexShape.up_Rel, neg_add_cancel_comm,
                add_eq_left] at hij
              rw [←neg_add, neg_eq_zero, add_comm] at hij
              norm_cast at hij
            | negSucc k =>
              simp only [Nat.cast_one, Int.negSucc_eq, Nat.cast_add, neg_add_rev, Int.reduceNeg,
                ComplexShape.up_Rel, neg_add_cancel_comm, add_right_inj] at hij hjk
              rw [←neg_add, neg_eq_iff_eq_neg, neg_neg] at hij hjk
              norm_cast at hij hjk
              subst hjk
              simp at hij
              subst hij
              rw [add_comm 1 i]
              dsimp
              exact (inhomogeneousChains M).d_comp_d' _ _ i rfl rfl

lemma TateComplex_d_neg_one (M : Rep R G) : (TateComplex M).d (-1) 0 = TateNorm M := rfl

lemma TateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (TateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma TateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (TateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map φ := {
    f
    | Int.ofNat i => ((cochainsFunctor R G).map φ).f ↑i
    | Int.negSucc i => (chainsMap (MonoidHom.id G) φ).f i -- don't yet have `chainsFunctor`.
    comm' := sorry
  }
  map_id := sorry
  map_comp := sorry

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry
instance TateComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ n (n + 1) rfl

def TateCohomology.iso_groupCohomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (n + 1)).obj M ≅ groupCohomology M (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology.iso_groupHomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (-n - 2)).obj M ≅ groupHomology M (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology_zero_iso (M : Rep R G) : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
  sorry

def TateCohomology_neg_one_iso (M : Rep R G) : (TateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
    (Submodule.span R (⋃ g : G, range (1 - M.ρ g))).submoduleOf (ker M.ρ.norm)) :=
  sorry

def TateCohomology_zero_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  sorry

def TateCohomology_neg_one_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (TateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)):=
  sorry

end groupCohomology
end
