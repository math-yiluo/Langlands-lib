/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleLocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic

/-! # Proper pushforward on the localizing hull of constructible adic complexes

Source: blueprint `sk-cor-existence-ii-restriction.proof.md`, part (1), and
`theorem-exceptional-inverse-image`, part (2).
(blueprint: lem-sfb-adic-proper-localizing-pushforward)
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

include ℓ k hΛ

/-- Proper derived pushforward carries the source localizing hull to the target one.
The proof uses exactness, proper finiteness on the generators, and coproduct preservation
on the hull, through the universal property of the localizing closure. -/
theorem ellAdic_localizing_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj Λ Z.left)))
    (hK : boundedConstructibleLocalizingClosure Λ Z.left K) :
    boundedConstructibleLocalizingClosure Λ Y.left ((R((g.left)_*⟦Λ⟧)).obj K) := by
  refine boundedConstructibleLocalizingClosure_map_of_preservesOnClosure Λ Z.left Y.left
    (R((g.left)_*⟦Λ⟧))
    (fun I ↦ ellAdic_localizingLowerStar_preservesCoproducts Λ ℓ g hΛ I) ?_ K hK
  intro K hK
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  cases hΛ with
  | continuous E =>
    exact boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj
      ℓ E Y.hom g.left K hK
  | integral E =>
    exact boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj
      ℓ E Y.hom g.left K hK
  | algebraicClosure =>
    exact boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj
      ℓ Y.hom g.left K hK

/-- The actual ambient proper pushforward restricted to the two localizing hulls.
The object and morphism maps are those of the ambient derived pushforward. -/
noncomputable def ellAdicLocalizingLowerStar :
    (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory :=
  (boundedConstructibleLocalizingClosure Λ Y.left).lift
    ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧))
    (fun K ↦ ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ K.obj K.property)

/-- The localizing proper pushforward commutes with integer shifts. -/
noncomputable instance commShift_ellAdicLocalizingLowerStar :
    (ellAdicLocalizingLowerStar Λ ℓ g hΛ).CommShift ℤ := by
  unfold ellAdicLocalizingLowerStar
  infer_instance

/-- The localizing proper pushforward is exact. -/
instance isTriangulated_ellAdicLocalizingLowerStar :
    (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsTriangulated := by
  have : (R((g.left)_*⟦Λ⟧)).IsTriangulated := inferInstance
  have : ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙
      R((g.left)_*⟦Λ⟧)).IsTriangulated := inferInstance
  unfold ellAdicLocalizingLowerStar
  infer_instance

/-- Its coproducts can be tested after the fully faithful target inclusion. -/
theorem ellAdicLocalizingLowerStar_preservesCoproducts (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (ellAdicLocalizingLowerStar Λ ℓ g hΛ) := by
  let : PreservesColimitsOfShape (Discrete I)
      ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧)) :=
    ellAdic_localizingLowerStar_preservesCoproducts Λ ℓ g hΛ I
  have : PreservesColimitsOfShape (Discrete I)
      (ellAdicLocalizingLowerStar Λ ℓ g hΛ ⋙
        (boundedConstructibleLocalizingClosure Λ Y.left).ι) := by
    change PreservesColimitsOfShape (Discrete I)
      ((boundedConstructibleLocalizingClosure Λ Z.left).ι ⋙ R((g.left)_*⟦Λ⟧))
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (ellAdicLocalizingLowerStar Λ ℓ g hΛ)
    (boundedConstructibleLocalizingClosure Λ Y.left).ι

end AlgebraicGeometry.ProEtale.CondensedRing
