import Mathlib
import CFT.Cohomology.CyclicGroup

variables {G : Type} [Fintype G] [Group G] {R : Type} [CommRing R]

variable (H : Subgroup G)

open CategoryTheory Rep BigOperators



/-
The restriction functor from `Rep R G` to `Rep R H`, where `H` is a subgroup
of a group `G`.
-/
noncomputable def Rep.restriction : (Rep R G) ⥤ (Rep R H) where
  obj X := {
    V := X.V
    ρ := {
      toFun := fun ⟨h,_⟩ ↦ X.ρ h
      map_one' := sorry
      map_mul' := sorry
    }
  }
  map f := {
    hom := f.hom
    comm := fun _ ↦ f.comm _
  }
  map_id := sorry
  map_comp := sorry



variable (C : Rep R G)

#check (restriction H).obj C

variable (hC₁ : Unique (groupCohomology ((restriction H).obj C) 1))
variable (hC₂ : Nat.card (groupCohomology ((restriction H).obj C) 2) = Nat.card H)
variable (H2_gen : groupCohomology ((restriction H).obj C) 2)
variable (H2_gen_spec : ∀ σ : groupCohomology ((restriction H).obj C) 2, ∃ n : ℤ, σ = n • H2_gen)


instance : AddCommGroup {f : G → R // f 1 = 0} where
  add f f' := ⟨f + f', sorry⟩
  add_assoc := sorry
  zero := ⟨0,rfl⟩
  zero_add := sorry
  add_zero := sorry
  nsmul n f := ⟨n • f,sorry⟩
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg f := ⟨f,sorry⟩
  sub f g := ⟨f - g, sorry⟩
  sub_eq_add_neg := sorry
  zsmul n f := ⟨n • f,sorry⟩
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  add_left_neg := sorry
  add_comm := sorry


noncomputable instance : Module R {f : G → R // f 1 = 0} where
  smul x f := ⟨x • f, sorry⟩
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

#check H2_gen

variable {C}
/--the 2-cocycle representing the generator of H^2(G,C).-/
def φ : G → G → C := sorry


noncomputable instance : Representation R G (C × {f : G → R // f 1 = 0}) where
  toFun g := by
    by_cases hg : g = 1
    · exact 1
    · exact {
        toFun := by
          -- need to check all this.
          intro ⟨c,f⟩
          constructor
          · exact C.ρ g c + ∑ h : G, ((f.val h) • φ g h) - (f.val 1) • (φ g 1)
          · exact {
            val := by
              intro h
              by_cases hgh : g=h
              · exact f.val 1 - f.val g
              · exact f.val (g⁻¹ * h)
            property := sorry
          }
        map_add' := sorry
        map_smul' := sorry
      }
  map_one' := sorry
  map_mul' := sorry



noncomputable
def splittingModule : Rep R G where
  V := {
    carrier := C × {f : G → R // f 1 = 0}
    isAddCommGroup := inferInstance
    isModule := inferInstance
  }
  ρ := by
    change G →* _
    exact {
      toFun := by
        change G →* _
        exact {
          toFun := by
            intro g
            exact {
              toFun := by
                intro ⟨c, f⟩
                let φ : G → G → C := sorry -- the 2-cocycle
                let c' := C.ρ g c + ∑ h : G, (f.val g : R) • (φ g h : C)
                sorry
              map_add' := sorry
              map_smul' := sorry
            }
          map_one' := sorry
          map_mul' := sorry
        }
      map_one' := sorry
      map_mul' := sorry
    }




def dimensionShift (r : ℕ) : groupCohomology (Rep.trivial R G R) r ⟶ groupCohomology C (r + 2) := {
  toFun := sorry
  map_add' := sorry
  map_smul' := sorry
}
