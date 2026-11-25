/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation

/-! # Finite comparison realization of constant sheaves and pullback

The finite comparison realization of a constant sheaf with value an ordinary module `P` is
the inverse image from the point of a condensed module `pointConstantModule B eR P`, built
from the constant condensed sheaf on `P`. This functor sends `B^n` to the free module of
rank `n`. The finite comparison realization also commutes with inverse image.

Source: blueprint scalar-six-ctf (1), finite coefficient comparison and finite projective
local models.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

public noncomputable section

namespace AlgebraicGeometry.ProEtale

attribute [local instance] fixedModuleLimits

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Ordinary modules as condensed modules over the continuous-map ring: the constant
condensed sheaf, read as an internal module over the sheafified constant ring, then
transported along the given ring isomorphism `eR`. -/
def pointConstantModule :
    ModuleCat.{u + 1} (ULift.{u + 1} B) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} B) :=
  constantSheaf (coherentTopology Profinite.{u}) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⋙
    (ConstantInternalModuleSheafEncoding.sheafEncoding (coherentTopology Profinite.{u})
      (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) rfl).inv ⋙
    Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) eR.inv

/-- The condensed point model of `B^n` is the free module of rank `n`. -/
def pointConstantModuleFiniteFreeIso (n : ℕ) :
    (pointConstantModule B eR).obj
        (ModuleCat.of (ULift.{u + 1} B) (Fin n → ULift.{u + 1} B)) ≅
      Mod.finiteFree (Profinite.continuousMapRingObj.{u} B) n := by
  let R := ULift.{u + 1} B
  let J := coherentTopology Profinite.{u}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl
  let S := constantSheaf J (ModuleCat.{u + 1} R)
  let rr : (internalToModule R).obj (Mod.regular (AddCommGrpCat.of R)) ≅ ModuleCat.of R R :=
    ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext x; rfl)
  let e : H.obj (Mod.finiteFree _ n) ≅ S.obj (ModuleCat.of R (Fin n → R)) :=
    ConstantInternalModuleSheafEncoding.encFiniteFreeIso J R (internalToModule R) rfl n ≪≫
      S.mapIso (biproduct.mapIso (fun _ ↦ rr) ≪≫ ModuleCat.biproductIsoPi _)
  let F := Mod.comap (D := Sheaf J Ab.{u + 1}) eR.inv
  let : F.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso eR.inv).isEquivalence_functor
  let : F.Additive := Functor.additive_of_preserves_binary_products _
  let free : F.obj (Mod.finiteFree _ n) ≅ Mod.finiteFree _ n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv eR.inv))
  exact F.mapIso (H.inv.mapIso e.symm ≪≫ (H.asEquivalence.unitIso.app _).symm) ≪≫ free

/-- The internal constant model of `P`, pulled back from the point, is the
finite-discrete encoding of the constant sheaf on `P`. -/
private def pointConstantChain (X : Scheme.{u}) (P : ModuleCat.{u + 1} (ULift.{u + 1} B)) :
    ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj.{u} B)).obj
      ((Mod.comap (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) eR.inv).obj
        ((internalConstantFunctor (coherentTopology Profinite.{u}) (ULift.{u + 1} B)).obj
          (moduleToInternalObj (ULift.{u + 1} B) P))) ≅
      (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).functor.obj
          ((constantSheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P) := by
  let R := ULift.{u + 1} B
  let N := moduleToInternalObj R P
  let HX := ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X) R
    (internalToModule R) rfl
  let CX := (internalConstantFunctor (Scheme.ProEt.topology X) R).obj N
  let eX : HX.obj CX ≅ (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)).obj P :=
    (internalConstantEncoding (Scheme.ProEt.topology X) R).app N ≪≫
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)).mapIso
        (CategoryTheory.realizationIso R P)
  let j : CX ≅ HX.inv.obj ((constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)).obj P) :=
    HX.asEquivalence.unitIso.app CX ≪≫ HX.inv.mapIso eX
  unfold CondensedRing.finiteDiscreteCoefficientEquivalence
  change _ ≅ (Mod.comap (asIso (finiteDiscreteSchemeRingIso B X eR).hom).inv).obj _
  exact pointConstantComparison B X eR N ≪≫
    (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv).mapIso j ≪≫
    (Mod.comapCongr (by
      apply (cancel_mono (finiteDiscreteSchemeRingIso B X eR).hom).mp
      simp)).app _

/-- The finite comparison realization of the constant sheaf on `P` is pulled back from the
point model of `P`. -/
def finiteComparisonRealizationConstantIso (X : Scheme.{u})
    (P : ModuleCat.{u + 1} (ULift.{u + 1} B)) :
    (finiteComparisonRealization B X eR).obj
        ((constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P) ≅
      ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj.{u} B)).obj
        ((pointConstantModule B eR).obj P) := by
  let R := ULift.{u + 1} B
  let J := coherentTopology Profinite.{u}
  let N := moduleToInternalObj R P
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl
  let C := (internalConstantFunctor J R).obj N
  let eJ : H.obj C ≅ (constantSheaf J (ModuleCat.{u + 1} R)).obj P :=
    (internalConstantEncoding J R).app N ≪≫
      (constantSheaf J (ModuleCat.{u + 1} R)).mapIso (CategoryTheory.realizationIso R P)
  let cJ : C ≅ H.inv.obj ((constantSheaf J (ModuleCat.{u + 1} R)).obj P) :=
    H.asEquivalence.unitIso.app C ≪≫ H.inv.mapIso eJ
  exact (realizedEncodingIso B X eR).app _ ≪≫ (pointConstantChain B eR X P).symm ≪≫
    ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj.{u} B)).mapIso
      ((Mod.comap (D := Sheaf J Ab.{u + 1}) eR.inv).mapIso cJ)

/-- The finite comparison realization commutes with inverse image. -/
def finiteComparisonRealizationUpperStarIso {S T : Scheme.{u}} (f : T ⟶ S) :
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f ⋙
        finiteComparisonRealization B T eR ≅
      finiteComparisonRealization B S eR ⋙
        CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} B) f :=
  Functor.isoWhiskerLeft _ (realizedEncodingIso B T eR) ≪≫
    CondensedRing.finiteDiscreteCoefficientProEtalePullbackIso B eR
      (internalToModule (ULift.{u + 1} B)) rfl f ≪≫
    Functor.isoWhiskerRight (realizedEncodingIso B S eR).symm _

end AlgebraicGeometry.ProEtale

end
