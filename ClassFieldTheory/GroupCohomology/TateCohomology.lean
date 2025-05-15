import Mathlib
import ClassFieldTheory.GroupCohomology._4_DimensionShift

open
  CategoryTheory
  groupCohomology
  groupHomology
  Rep
  dimensionShift

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [Fintype G]

noncomputable section

namespace groupCohomology



/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶
    (inhomogeneousCochains M).X 0 := by
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
  | -1,0                                =>  TateNorm M
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
      rw [ComplexShape.up_Rel, ComplexShape.down_Rel, Int.negSucc_coe', Int.negSucc_coe',
        sub_add_cancel, ←neg_add', neg_inj, eq_comm]
      norm_cast
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
              simp only [Int.negSucc_coe, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
                Int.ofNat_eq_coe, ComplexShape.up_Rel, neg_add_cancel_comm,
                Nat.neg_cast_eq_cast] at hjk
              simp only [Int.negSucc_coe, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
                hjk.1, zero_add, ComplexShape.up_Rel, neg_add_cancel_comm, add_eq_left] at hij
              rw [←neg_add, neg_eq_zero, add_comm] at hij
              norm_cast at hij
            | negSucc k =>
              simp only [Nat.cast_one, Int.negSucc_coe, Nat.cast_add, neg_add_rev, Int.reduceNeg,
                ComplexShape.up_Rel, neg_add_cancel_comm, add_right_inj] at hij hjk
              rw [←neg_add, neg_eq_iff_eq_neg, neg_neg] at hij hjk
              norm_cast at hij hjk
              rw [←hij, add_comm 1 i]
              dsimp
              convert (inhomogeneousChains M).d_comp_d' (i + 1+1) (i + 1) i rfl rfl
              have : i = k := by linarith
              rw [this]



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

lemma TateCohomology.eq_groupCohomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (n + 1)).obj M = groupCohomology M (n + 1) := by
  rw [TateCohomology, HomologicalComplex.homologyFunctor]
  congr 1
  simp only [Functor.comp_obj]
  rw [HomologicalComplex.homology, groupCohomology, HomologicalComplex.homology]
  congr 1
  rw [TateComplexFunctor]
  dsimp
  rw [TateComplex]
  rw [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    CochainComplex.prev, CochainComplex.next, add_sub_cancel_right]
  sorry


lemma TateCohomology.eq_groupHomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (-n - 2)).obj M = groupHomology M (n + 1) := by
  sorry
  -- rw [TateCohomology, HomologicalComplex.homology]
  -- congr 1
  -- simp only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, CochainComplex.prev,
  --   CochainComplex.next, ChainComplex.prev, ChainComplex.next_nat_succ]
  -- have this₁ : -(n : ℤ) - 2 - 1 = Int.negSucc (n + 2)
  -- · calc
  --   _ = - (n + 2 : ℤ) - 1 := by ring
  --   _ = Int.negSucc (n + 2) := rfl
  -- have this₂ : -(n : ℤ) - 2 = Int.negSucc (n + 1)
  -- · calc
  --   _ = - (n + 1 : ℤ) - 1 := by ring
  --   _ = Int.negSucc (n + 1) := rfl
  -- have this₃ : -(n : ℤ) - 2 + 1 = Int.negSucc n
  -- · calc
  --   _ = - (n + 1 : ℤ) := by ring
  --   _ = Int.negSucc n := rfl
  -- rw [this₃,this₁,this₂]
  -- rfl

/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateCohomology.exact1 :
    CategoryTheory.Limits.PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry
instance TateCohomology.exact2 :
    CategoryTheory.Limits.PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ _ _ rfl



-------------------

/-
Here is another definition of Tate cohomology, this time using dimension-shifting.
-/

def H (n : ℕ) : Rep R G ⥤ ModuleCat R where
  obj M := groupCohomology M n
  map f := map (MonoidHom.id G) f n
  map_id M := sorry
  map_comp := sorry

def Tate : ℤ → Rep R G ⥤ ModuleCat R
  | 0 => down ⋙ H 1
  | Int.ofNat (n + 1) => H (n + 1)
  | Int.negSucc 0 => down ⋙ down ⋙ H 1
  | Int.negSucc (n + 1) => down ⋙ Tate (Int.negSucc n)

lemma Tate_natSucc (n : ℕ) : Tate (n + 1) = H (R := R) (G := G) (n + 1) := by
  norm_cast
  rw [Tate.eq_def]

lemma Tate_zero : Tate 0 = down ⋙ H (R := R) (G := G) 1 := by
  rw [Tate]

lemma Tate_neg_one : Tate (-1 : ℤ)  = down ⋙ down ⋙ H 1 (R := R) (G := G) := by
  change Tate (Int.negSucc 0) = _
  rw [Tate]

lemma Tate_ofNeg (n : ℕ) :
    Tate (R := R) (G := G) (-(n + 2) : ℤ) = down ⋙ Tate (-(n + 1) : ℤ) := by
  change Tate (Int.negSucc (n + 1) ) = down ⋙ Tate (Int.negSucc n)
  rw [Tate]

/-
# TODO

State long exact sequences in Tate cohomology and prove them by dimension-shifting.
-/


end groupCohomology
end
