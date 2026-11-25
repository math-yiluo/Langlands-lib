/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingPushforward
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingCohomologicalRepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-! # Brown representability for proper adic pushforward on localizing hulls

Source: blueprint `theorem-exceptional-inverse-image` (1)-(3), specialized to a proper morphism.
(blueprint: lem-sfb-adic-localizing-brown-representability)
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

/-- Represent the contravariant Hom functor of the exact coproduct-preserving
proper localizing pushforward. -/
theorem ellAdic_localizing_lowerStar_hom_isRepresentable
    (K : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory) :
    ((ellAdicLocalizingLowerStar Λ ℓ g hΛ).op ⋙ yoneda.obj K).IsRepresentable := by
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  let H := F.op ⋙ preadditiveYoneda.obj K
  let := Pretriangulated.Opposite.instHasShiftOppositeInt
    (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory
  let := Pretriangulated.Opposite.instHasShiftOppositeInt
    (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory
  let := Pretriangulated.Opposite.instOpposite
    (C := (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
  let := Pretriangulated.Opposite.instOpposite
    (C := (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory)
  let := Pretriangulated.Opposite.commShiftFunctorOpInt F
  let := Pretriangulated.Opposite.functor_isTriangulated_op F
  have : H.IsHomological := by
    change (F.op ⋙ preadditiveYoneda.obj K).IsHomological
    infer_instance
  have hH : ∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) H := by
    intro I
    let : PreservesColimitsOfShape (Discrete I) F :=
      ellAdicLocalizingLowerStar_preservesCoproducts Λ ℓ g hΛ I
    let : PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F
    let : PreservesLimitsOfShape (Discrete I) F.op :=
      preservesLimitsOfShape_op (Discrete I) F
    have : PreservesLimitsOfShape (Discrete I)
        (preadditiveYoneda.obj K ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete I) (yoneda.obj K))
    have : PreservesLimitsOfShape (Discrete I) (preadditiveYoneda.obj K) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)
    change PreservesLimitsOfShape (Discrete I) (F.op ⋙ preadditiveYoneda.obj K)
    infer_instance
  exact ellAdic_localizing_cohomological_isRepresentable Λ ℓ Z hΛ H hH

/-- The representable Hom functors assemble to a right adjoint. -/
theorem ellAdic_isLeftAdjoint_localizingLowerStar :
    (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext K
  apply propext
  change ((ellAdicLocalizingLowerStar Λ ℓ g hΛ).op ⋙ yoneda.obj K).IsRepresentable ↔ True
  exact ⟨fun _ ↦ trivial,
    fun _ ↦ ellAdic_localizing_lowerStar_hom_isRepresentable Λ ℓ g hΛ K⟩

end AlgebraicGeometry.ProEtale.CondensedRing
