/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteModuleCategoriesSupplement
public import WeilConjectures.CategoryTheory.ConstantInternalModuleSheafEncoding.ConstantInternalModuleSheafEquivalenceSupplement
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData

/-! # A common sectionwise finite-coefficient encoding

The same functor on internal modules in abelian groups is used on every site.
The coefficient-ring identification is pulled back from one fixed profinite point.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_finiteDiscreteCoefficientEncodingDataSupplement
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme CategoryTheory.ConstantInternalModuleSheafEncoding

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

/-- This coefficient encoding preserves the underlying abelian sheaf. -/
noncomputable def finiteDiscreteCoefficientEquivalenceForgetIso (T : Scheme.{u}) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙ Mod.forget _ ≅
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  let H := sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG
  let U := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  unfold finiteDiscreteCoefficientEquivalence
  change H.inv ⋙ Mod.forget _ ≅ U
  exact Functor.isoWhiskerLeft H.inv
      (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight H.asEquivalence.counitIso U ≪≫ Functor.leftUnitor U

end AlgebraicGeometry.ProEtale.CondensedRing
