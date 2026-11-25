/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent

/-!
# Vanishing above m gives the m-pseudo-coherent base case

Source: Stacks Project, More on Algebra, Lemma 15.66.7 (Tag 064W), part (1)
(blueprint: lem-pc-ring-m-pseudo-coherent-vanishing-base).
-/

@[expose] public section

universe w₁ v₁ u₁

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If all cohomology of `C` in degrees at least `m` vanishes, the zero complex of finite
free modules maps to `C`; it is an isomorphism on cohomology above `m` and surjective in
degree `m`. For `i > m`, both cohomology modules are zero, so the induced map is an
isomorphism. In degree `m`, its target is zero, so it is surjective. Thus the zero
complex witnesses `IsMPseudoCoherent m C` (Stacks, Tag 064W, part (1)).
(blueprint: lem-pc-ring-m-pseudo-coherent-vanishing-base) -/
theorem isMPseudoCoherent_of_homology_vanishes {R : Type u₁} [CommRing R]
    [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{v₁} R))
    (hC : ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor (ModuleCat.{v₁} R) i).obj C)) :
    IsMPseudoCoherent m C := by
  open scoped ZeroObject in
  refine ⟨0, 0, 0, inferInstance, inferInstance, ?_, 0, ?_, ?_⟩
  · intro i
    have : Subsingleton ((0 : CochainComplex (ModuleCat.{v₁} R) ℤ).X i) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))
    exact ⟨inferInstance, inferInstance⟩
  · intro i hi
    exact ((homologyFunctor (ModuleCat.{v₁} R) i).map_isZero
      (Q.map_isZero (isZero_zero _))).isIso (hC i (le_of_lt hi)) _
  · exact (hC m le_rfl).epi _

end DerivedCategory
