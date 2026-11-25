/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingPushforward
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalConstructibleCohomology

/-! # Constructibility of the localizing exceptional inverse image

Source: blueprint `theorem-exceptional-inverse-image` (4), `det-existence-restriction.proof.md`.
(blueprint: lem-sfb-adic-localizing-exceptional-constructible)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- `ellAdic_localizing_rightAdjoint_obj_boundedConstructible` for the coefficients `E` and
`Q̄_ℓ`, through the rational restriction theorem only (blueprint:
theorem-f-shriek-ell-adic-coefficients). (blueprint:
lem-sfb-adic-localizing-exceptional-constructible)
-/
theorem ellAdic_localizing_rightAdjoint_obj_boundedConstructible_rational
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (hr : ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))))
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    boundedConstructible (condensedRingObj Λ Z.left)
      ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj) := by
  rw [mem_boundedConstructible_iff]
  exact ⟨ellAdic_localizing_rightAdjoint_obj_isBounded_rational (hcd := hcd) Λ ℓ g hΛ hr G adj K,
    ellAdic_localizing_rightAdjoint_obj_homology_constructible_rational (hcd := hcd) Λ ℓ g hΛ hr
      G adj K⟩

end AlgebraicGeometry.ProEtale.CondensedRing
