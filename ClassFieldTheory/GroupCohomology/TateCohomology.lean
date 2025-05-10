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
    (groupCohomology.inhomogeneousCochains M).X 0 := by
  sorry

def TateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ where
  X
  | Int.ofNat n => (inhomogeneousCochains M).X n
  | Int.negSucc n => (inhomogeneousChains M).X n
  d i j := by
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j   => exact (inhomogeneousCochains M).d i j
      | negSucc j => exact 0
    | negSucc i =>
      cases j with
      | ofNat j =>
        cases i with
        | zero =>
          cases j with
          | zero    => exact TateNorm M
          | succ _  => exact 0
        | succ _ => exact 0
      | negSucc j => exact (inhomogeneousChains M).d i j
  shape := sorry
  d_comp_d' := sorry

def TateCohomology (M : Rep R G) (n : ℤ) : ModuleCat R := (TateComplex M).homology n

lemma TateCohomology.eq_groupCohomology (n : ℕ) (M : Rep R G) :
    TateCohomology M (n + 1) = groupCohomology M (n + 1) := by
  rw [TateCohomology, HomologicalComplex.homology]
  congr 1
  simp only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, CochainComplex.prev,
    add_sub_cancel_right, CochainComplex.next, CochainComplex.prev_nat_succ]
  norm_cast

lemma TateCohomology.eq_groupHomology (n : ℕ) (M : Rep R G) :
    TateCohomology M (-n - 2) = groupHomology M (n + 1) := by
  rw [TateCohomology, HomologicalComplex.homology]
  congr 1
  simp only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor, CochainComplex.prev,
    CochainComplex.next, ChainComplex.prev, ChainComplex.next_nat_succ]
  have this₁ : -(n : ℤ) - 2 - 1 = Int.negSucc (n + 2)
  · calc
    _ = - (n + 2 : ℤ) - 1 := by ring
    _ = Int.negSucc (n + 2) := rfl
  have this₂ : -(n : ℤ) - 2 = Int.negSucc (n + 1)
  · calc
    _ = - (n + 1 : ℤ) - 1 := by ring
    _ = Int.negSucc (n + 1) := rfl
  have this₃ : -(n : ℤ) - 2 + 1 = Int.negSucc n
  · calc
    _ = - (n + 1 : ℤ) := by ring
    _ = Int.negSucc n := rfl
  rw [this₃,this₁,this₂]
  rfl

def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map φ :=  {
    f
    | Int.ofNat i => (cochainsMap (MonoidHom.id G) φ).f i
    | Int.negSucc i => (chainsMap (MonoidHom.id G) φ).f i
    comm' := sorry
  }
  map_id M := by
    dsimp only [ComplexShape.up_Rel, cochainsMap_id, HomologicalComplex.id_f]
    ext i : 1
    cases i with
    | ofNat i => rfl
    | negSucc i => sorry
  map_comp := sorry

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
    (n : ℤ) : TateCohomology S.X₃ n ⟶ TateCohomology S.X₁ (n + 1) :=
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

def down_funct : Rep R G ⥤ Rep R G where
  obj M := down M
  map f := sorry
  map_id := sorry
  map_comp := sorry

def Tate (n : ℤ) : Rep R G ⥤ ModuleCat R := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      exact down_funct ⋙ H 1
    | succ n =>
      exact H (n + 1)
  | negSucc n =>
    induction n with
    | zero =>
      exact down_funct ⋙ down_funct ⋙ H 1
    | succ n ih =>
      exact down_funct ⋙ ih

lemma Tate_natSucc (n : ℕ) : Tate (n + 1) = H (R := R) (G := G) (n + 1) := rfl

lemma Tate_zero : Tate 0 = down_funct ⋙ H (R := R) (G := G) 1 := rfl

lemma Tate_neg_one : Tate (-1 : ℤ)  = down_funct ⋙ down_funct ⋙ H 1 (R := R) (G := G) := rfl

lemma Tate_ofNeg (n : ℕ) :
    Tate (R := R) (G := G) (-(n + 2) : ℤ) = down_funct ⋙ Tate (-(n + 1) : ℤ) := rfl



/-
# TODO

State long exact sequences in Tate cohomology and prove them by dimension-shifting.
-/


end groupCohomology
end
