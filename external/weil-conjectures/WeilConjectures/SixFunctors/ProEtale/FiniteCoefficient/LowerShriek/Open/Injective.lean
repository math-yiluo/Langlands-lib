/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Restriction to a localization preserves injectives

For a weakly étale `f : V ⟶ U`, the restriction `j_f^*` of pro-étale sheaves along the
localization functor `V_proét ⥤ U_proét` has an exact left adjoint, the left Kan extension
along the localization functor followed by sheafification: on presheaves it sends `M` to
`W ↦ ⨁_{s ∈ Hom_U(W, V)} M(W, s)`, which is exact since direct sums are exact in a Grothendieck
abelian category. Hence `j_f^*`, and the pullback `f^*`, preserve injective objects. The same
holds for étale `f` on the small étale sites. This is the pro-étale and étale localization part
of blueprint `lemma-acyclicity-pulled-back-injectives`.

## Main results

- `AlgebraicGeometry.ProEtale.injective_upperStar_obj_of_weaklyEtale`: `f^*` preserves
  injective pro-étale sheaves for `f` weakly étale.
- `AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale'`: `f^*` preserves injective
  étale sheaves for `f` étale.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)

/-- The restriction along the localization functor of a weakly étale `f` preserves injective
objects: it is right adjoint to the left Kan extension along the localization functor followed
by sheafification, which is left exact. -/
instance preservesInjectiveObjects_localizationRestriction :
    (ProEtale.localizationRestriction A f h).PreservesInjectiveObjects := by
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A
    (P := @WeaklyEtale) h
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ h) A (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ h) A (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)) :=
    comp_preservesFiniteLimits (sheafToPresheaf _ A)
      (((MorphismProperty.Over.map ⊤ h).op.lan) ⋙ presheafToSheaf _ A)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

/-- The pullback `f^*` along a weakly étale `f` sends injective pro-étale sheaves to injective
pro-étale sheaves. -/
theorem injective_upperStar_obj_of_weaklyEtale [WeaklyEtale f]
    (I : Sheaf (Scheme.ProEt.topology U) A) [Injective I] :
    Injective ((ProEtale.upperStar A f).obj I) :=
  Injective.of_iso ((ProEtale.upperStarIsoLocalizationRestriction A f inferInstance).app I).symm
    (Functor.PreservesInjectiveObjects.injective_obj (F := _) inferInstance)

end ProEtale

namespace Etale

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : Etale f)

/-- The restriction along the localization functor of an étale `f` preserves injective
objects. -/
instance preservesInjectiveObjects_localizationRestriction :
    (Etale.localizationRestriction A f h).PreservesInjectiveObjects := by
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A
    (P := @Etale) h
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale))
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ h) A V.smallEtaleTopology U.smallEtaleTopology
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ h) A V.smallEtaleTopology U.smallEtaleTopology) :=
    comp_preservesFiniteLimits (sheafToPresheaf _ A)
      (((MorphismProperty.Over.map ⊤ h).op.lan) ⋙ presheafToSheaf _ A)
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

/-- The pullback `f^*` along an étale `f` sends injective étale sheaves to injective étale
sheaves. -/
theorem injective_upperStar_obj_of_etale' [Etale f]
    (I : Sheaf U.smallEtaleTopology A) [Injective I] :
    Injective ((Etale.upperStar A f).obj I) :=
  Injective.of_iso ((Etale.upperStarIsoLocalizationRestriction A f inferInstance).app I).symm
    (Functor.PreservesInjectiveObjects.injective_obj (F := _) inferInstance)

end Etale

end AlgebraicGeometry
