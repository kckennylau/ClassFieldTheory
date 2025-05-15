-- import Mathlib

-- variable (G : Type) [Group G]

-- open CategoryTheory Limits

-- /-
-- The next two statements say that `inhomogeneousCochainsFunctor` is an exact functor.
-- -/
-- instance groupCohomology.exact1 : PreservesFiniteLimits (groupCohomology.cochainsFunctor ℤ G) :=
--   sorry
-- instance groupCohomology.exact2 : PreservesFiniteColimits (groupCohomology.cochainsFunctor ℤ G) :=
--   sorry

-- variable {G}
-- lemma groupCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep ℤ G)}
--     (hS : S.ShortExact) : (S.map (groupCohomology.cochainsFunctor ℤ G)).ShortExact :=
--   ShortComplex.ShortExact.map_of_exact hS (cochainsFunctor ℤ G)

-- /--
-- The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-- -/
-- noncomputable abbrev groupCohomology.δ {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
--     (n : ℕ) : groupCohomology S.X₃ n ⟶ groupCohomology S.X₁ (n + 1) :=
--   (groupCohomology.cochainsFunctor_Exact hS).δ _ _ rfl
