/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Isomorphism invariance of unrestricted derived completeness

Source: Bhatt--Scholze, Definition 3.5.2; Stacks Project, Tag 08TC.
(blueprint: lem-pur-unrestricted-completeness-iso)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- Unrestricted completeness is invariant under an isomorphism of derived objects.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Project, Tag 08TC
(blueprint: lem-pur-unrestricted-completeness-iso).
Proof: retain the K-flat representative, its resolution and reduction tower.
Compose its identification with the given isomorphism and postcompose the connecting
arrow by its shifted hom. The new canonical augmentation is the old one precomposed
with the inverse isomorphism. Projectionwise product extensionality identifies the
first triangle square; the other two squares are identity and inverse cancellation.
Thus the new Roos triangle is isomorphic to the original distinguished triangle. -/
theorem isDerivedCompleteUnrestricted_of_iso
  {K M : DerivedCategory (integralTowerModules l E X)} (e : K ≅ M)
  (hK : IsDerivedCompleteUnrestricted l E X K) :
  IsDerivedCompleteUnrestricted l E X M := by
  obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hK
  let := hprod
  refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

end WeilConjectures
