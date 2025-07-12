import Mathlib

open CategoryTheory
    Rep

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]


-- noncomputable section Homology -- from #25880

-- def groupHomology.one_trivial_int_iso :
--     groupHomology (trivial ℤ G ℤ) 1 ≅ ModuleCat.of ℤ (Additive (Abelianization G)) := sorry

-- end Homology


-- -- # 25937
-- /-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
-- `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A).` -/
-- noncomputable def groupCohomology.coindIso [DecidableEq G] (S : Subgroup G) (A : Rep R S) (n : ℕ) :
--     groupCohomology (coind S.subtype A) n ≅ groupCohomology A n :=
--   sorry

-- -- # 25996
-- /-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
-- `Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A).` -/
-- noncomputable def groupHomology.indIso [DecidableEq G] (S : Subgroup G) (A : Rep R S) (n : ℕ) :
--     groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
--   sorry
