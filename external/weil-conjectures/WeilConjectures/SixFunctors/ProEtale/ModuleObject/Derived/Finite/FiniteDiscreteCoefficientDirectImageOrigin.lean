/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientDirectImageConjugation
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage

/-! # Direct image preserves the finite coefficient etale image -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- A qcqs derived direct image of a realized complex still has etale origin.
Source: Bhatt--Scholze, Lemmas 5.4.1 and 5.4.3; Stacks Project, Tag 099R
(blueprint: lem-weil-pbc-finite-discrete-direct-image-origin).

Proof in words. Undo the exact coefficient equivalence on the source and target.
Sectionwise restriction commutes with its common G, and the point-derived constant
ring identifications commute with scalar restriction along the canonical coefficient
maps. Hence the ordinary internal direct image is conjugate through these equivalences
to the ordinary module-valued direct image. Exact equivalences preserve injectives;
apply this identity to injective resolutions to obtain its derived version. For a
bounded below etale complex K the finite coefficient direct-image comparison identifies
R h_proet,* (nu_S^* K) with nu_T^* (R+ h_et,* K). The latter complex is bounded below.
Transport back by the target coefficient equivalence and include D+ in D. Thus the
specific witness for the essential image is R+ h_et,* K, and the comparison just
described supplies its isomorphism to the displayed target. Empty schemes and the
zero ring require no extra hypothesis. -/
theorem finiteDiscreteCoefficient_directImage_origin [DiscreteTopology B] [Finite B]
    {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
    (K : FiniteDiscreteEtalePlus B S) :
    (finiteDiscreteRealization B T (finiteDiscreteCoefficientEquivalence B eR G hG T)).essImage
      ((coefficientDerivedLowerStar (Profinite.continuousMapRingObj B) h).obj
        ((finiteDiscreteRealization B S
          (finiteDiscreteCoefficientEquivalence B eR G hG S)).obj K)) := by
  obtain ⟨e⟩ :=
    AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  refine ⟨(R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)).obj K, ?_⟩
  let Eₛ := finiteDiscreteCoefficientEquivalence B eR G hG S
  let Eₜ := finiteDiscreteCoefficientEquivalence B eR G hG T
  let q := (D(Eₜ.functor)).mapIso (DerivedCategory.Plus.ι.mapIso (e.app K))
  let iₜ := (ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)]).mapDerivedCategoryPlusCompatibility.app
    ((R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)).obj K)
  let iₛ := (ν^*(S)[ModuleCat.{u + 1} (ULift.{u + 1} B)]).mapDerivedCategoryPlusCompatibility.app K
  obtain ⟨hc⟩ := finiteDiscreteCoefficient_directImage_conjugation B eR G hG h
    ((D+(ν^*(S)[ModuleCat.{u + 1} (ULift.{u + 1} B)])).obj K)
  refine ⟨?_⟩
  let qt := (D(Eₜ.functor)).mapIso iₜ
  let qs := (D(Eₛ.functor)).mapIso iₛ
  let hs := (coefficientDerivedLowerStar (Profinite.continuousMapRingObj B) h).mapIso qs
  simpa only [finiteDiscreteRealization, Eₛ, Eₜ, Functor.comp_obj] using
    qt.symm ≪≫ q ≪≫ hc ≪≫ hs

end AlgebraicGeometry.ProEtale.CondensedRing
