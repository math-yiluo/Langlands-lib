/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseOverField
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.TraceFormula.WeilIdentityStructureOfId
public import WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible
public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
public import WeilConjectures.ZetaFunction.WeilObjectOfLisse

/-!
# The compactly supported cohomology of a pulled-back lisse sheaf in the two models

Let `H` be a lisse `ℓ`-adic sheaf on a separated `k₀`-scheme `X₀` of finite type, `a : X₀ ⟶ Spec k₀`
its structure morphism and `p^* H` the Weil sheaf on `X₀` pulled back from `H`
(`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`). Write `Mʲ = Hʲ(Ra_! H)` for the homology
sheaves of the compactly supported direct image of `H` in the trace formula chapter
(`ProEtale.CondensedRing.boundedConstructibleLowerShriek`), module objects on `Spec k₀`. Then:

- in the zeta-function chapter, the `j`-th cohomology sheaf of `Ra_! (p^* H)` is the Weil sheaf on
  `Spec k₀` pulled back from `Mʲ`
  (`AlgebraicGeometry.WeilComplex.homologySheafDerivedLowerShriekGeometricFiberPullbackIso`), by
  the comparison of the two models of `Rf_!`
  (`AlgebraicGeometry.WeilComplex.derivedLowerShriekCompToCondensedIso`) and the weakly étale base
  change of `Rf_!` to the geometric fibres
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekGeometricFiberWeilIso`);
- in the trace formula chapter, the `j`-th homology sheaf of the compactly supported cohomology of
  the Weil object `(H, 1)` is the Weil sheaf `Mʲ` with the identity structure
  (`AlgebraicGeometry.WeilComplex.homologyFunctorWeilCompactSupportCohomologyWeilObjectOfLisseIso`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open ProEtale ProEtale.CondensedRing

/-- The condensed Weil lower shriek only depends on the compactification chosen by
`HasCompactification` through the underlying morphism. -/
noncomputable def ProEtale.CondensedRing.weilRightDerivedLowerShriekCongr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
    {t : Y₀ ⟶ Spec (.of k)} {f g : X₀ ⟶ Y₀} (hfg : f = g) [HasCompactification f]
    [HasCompactification g] (hf : f ≫ t = s) (hg : g ≫ t = s) :
    weilRightDerivedLowerShriek Λ (HasCompactification.compactification f) hf ≅
      weilRightDerivedLowerShriek Λ (HasCompactification.compactification g) hg := by
  subst hfg
  exact Iso.refl _

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

namespace WeilComplex

variable (X) in
omit [Finite k₀] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- The structure morphism `X₀ ⟶ Spec k₀` factors through the identity of `Spec k₀`: the underlying
morphism of `toPoint X₀` followed by the structure morphism of `Spec k₀`. -/
lemma toPoint_overSpec_left_comp :
    (toPoint (overSpec (k₀ := k₀) X)).left ≫ (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) =
      X ↘ Spec (CommRingCat.of k₀) := by
  rw [toPoint_left]
  exact comp_over (X ↘ Spec (CommRingCat.of k₀)) _

/-- The `j`-th homology sheaf `Mʲ = Hʲ(Ra_! H)` of the compactly supported direct image, in the
trace formula chapter, of a lisse sheaf `H` placed in degree `0`: a module object on `Spec k₀`. -/
noncomputable abbrev lowerShriekHomologyOfLisse {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H)
    (j : ℤ) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of k₀))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀))) :=
  (DerivedCategory.homologyFunctor _ j).obj
    ((boundedConstructibleLowerShriek l (toPoint (overSpec (k₀ := k₀) X))).obj
      (boundedConstructibleOfLisse hH)).obj

/-- The comparison of the two models of `Rf_!` at `p^* H`. -/
noncomputable def derivedLowerShriekGeometricFiberPullbackToCondensedIso₁ {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l (Spec (CommRingCat.of k₀))).functor.obj
        ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH))).obj ≅
      (ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
          (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
            (hf := hasCompactification_of_over (k₀ := k₀) _))).obj
        ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtaleWeilSheaf.geometricFiberPullback k₀ l X).obj H))) :=
  (derivedLowerShriekCompToCondensedIso k₀ l (X ↘ Spec (CommRingCat.of k₀))).app
      (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH))

/-- The pulled-back Weil sheaf `p^* H` placed in degree `0`, in the condensed model, is the
pullback to the geometric fibre of `E H` placed in degree `0`. -/
noncomputable def derivedEquivCondensedSingleGeometricFiberPullbackIso (H : AdicSheaf l X) :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtaleWeilSheaf.geometricFiberPullback k₀ l X).obj H)) ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
  (ProEtaleWeilSheaf.singleFunctorCompDerivedEquivCondensedIso k₀ l X 0).app
      ((ProEtaleWeilSheaf.geometricFiberPullback k₀ l X).obj H) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso k₀ l X).app H) ≪≫
    ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategorySingleFunctor 0).symm.app
        ((adicSheafEquivCondensedMod l X).functor.obj H)

/-- The condensed Weil `Rā_!` for the compactification of the zeta-function chapter is the one
for the compactification of the trace formula chapter. -/
noncomputable def condensedRightDerivedLowerShriekCompactificationIso :
    ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
        (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
          (hf := hasCompactification_of_over (k₀ := k₀) _)) ≅
      weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
        (compactificationOverField (toPoint (overSpec (k₀ := k₀) X)))
        (toPoint_overSpec_left_comp (k₀ := k₀) X) :=
  haveI := hasCompactification_of_over (k₀ := k₀) (X ↘ Spec (CommRingCat.of k₀))
  haveI := HasCompactification.of_over (toPoint (overSpec (k₀ := k₀) X))
  weilRightDerivedLowerShriekCongr (Profinite.padicAlgClRingObj l)
    (toPoint_left (overSpec (k₀ := k₀) X)).symm (comp_over (X ↘ Spec (CommRingCat.of k₀)) _)
    (toPoint_overSpec_left_comp (k₀ := k₀) X)

/-- The pullback to the geometric fibre of `Ra_! H`, computed by the condensed Weil `Rā_!`. -/
noncomputable def weilRightDerivedLowerShriekSingleOfLisseIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
        (compactificationOverField (toPoint (overSpec (k₀ := k₀) X)))
        (toPoint_overSpec_left_comp (k₀ := k₀) X)).obj
        ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
          (boundedConstructibleOfLisse hH).obj) ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        ((boundedConstructibleLowerShriek l (toPoint (overSpec (k₀ := k₀) X))).obj
          (boundedConstructibleOfLisse hH)).obj :=
  (geometricFiberWeilRightDerivedLowerShriekIso'
      (compactificationOverField (toPoint (overSpec (k₀ := k₀) X)))
      (toPoint_overSpec_left_comp (k₀ := k₀) X)).app (boundedConstructibleOfLisse hH).obj ≪≫
    (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.mapIso
      ((boundedConstructibleLowerShriekCompatibility l
        (toPoint (overSpec (k₀ := k₀) X))).app (boundedConstructibleOfLisse hH)).symm

/-- The comparison, through `toCondensed`, of the compactly supported direct image
`Ra_! (p^* H)` of the zeta-function chapter with the pullback to the geometric fibre of
`Ra_! H` in the trace formula chapter, in the derived category of condensed Weil objects on
`Spec k₀`. -/
noncomputable def derivedLowerShriekGeometricFiberPullbackToCondensedIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l (Spec (CommRingCat.of k₀))).functor.obj
        ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH))).obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        ((boundedConstructibleLowerShriek l (toPoint (overSpec (k₀ := k₀) X))).obj
          (boundedConstructibleOfLisse hH)).obj :=
  derivedLowerShriekGeometricFiberPullbackToCondensedIso₁ hH ≪≫
    (ProEtaleWeilSheaf.condensedRightDerivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))
      _).mapIso (derivedEquivCondensedSingleGeometricFiberPullbackIso H) ≪≫
    condensedRightDerivedLowerShriekCompactificationIso.app _ ≪≫
    weilRightDerivedLowerShriekSingleOfLisseIso hH

/-- The pullback to the geometric fibre of `Mʲ = Hʲ(Ra_! H)`, as a condensed Weil object on
`Spec k₀`, is the `j`-th cohomology sheaf of `Ra_! (p^* H)` through `toCondensed`. -/
noncomputable def toCondensedHomologySheafDerivedLowerShriekPullbackIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) :
    (ProEtaleWeilSheaf.toCondensed k₀ l (Spec (CommRingCat.of k₀))).obj
        ((homologySheaf j).obj ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH)))).obj ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).obj
        (lowerShriekHomologyOfLisse hH j) :=
  (ProEtaleWeilSheaf.homologyFunctorCompToCondensedIso k₀ l (Spec (CommRingCat.of k₀)) j).app
      _ ≪≫
    (DerivedCategory.homologyFunctor _ j).mapIso
      (derivedLowerShriekGeometricFiberPullbackToCondensedIso hH) ≪≫
    ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapDerivedCategoryHomologyFunctorIso
        j).symm.app _

/-- The `ℓ`-adic sheaf on `Spec k₀` corresponding to `Mʲ = Hʲ(Ra_! H)`. -/
noncomputable abbrev lowerShriekHomologyAdicOfLisse {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) : AdicSheaf l (Spec (CommRingCat.of k₀)) :=
  (adicSheafEquivCondensedMod l (Spec (CommRingCat.of k₀))).inverse.obj
    (lowerShriekHomologyOfLisse hH j)

/-- The homology sheaves `Mʲ = Hʲ(Ra_! H)` of the compactly supported direct image of a lisse
sheaf are lisse on `Spec k₀`: their pullbacks to `Spec k̄` are finite free. -/
theorem isAdicLisseSheaf_lowerShriekHomologyAdicOfLisse {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) :
    IsAdicLisseSheaf (lowerShriekHomologyAdicOfLisse (k₀ := k₀) hH j) :=
  isAdicLisseSheaf_inverse_obj_of_isConstructibleModuleObject
    (((boundedConstructibleLowerShriek l (toPoint (overSpec (k₀ := k₀) X))).obj
      (boundedConstructibleOfLisse hH)).property.2 j)

/-- The pullback to the geometric fibre of `Mʲ = Hʲ(Ra_! H)`, through `toCondensed`, is the
Weil sheaf of the zeta-function chapter pulled back from the corresponding `ℓ`-adic sheaf. -/
noncomputable def toCondensedGeometricFiberPullbackLowerShriekHomologyIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) :
    (ProEtaleWeilSheaf.toCondensed k₀ l (Spec (CommRingCat.of k₀))).obj
        ((ProEtaleWeilSheaf.geometricFiberPullback k₀ l (Spec (CommRingCat.of k₀))).obj
          (lowerShriekHomologyAdicOfLisse (k₀ := k₀) hH j)) ≅
      (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).obj
        (lowerShriekHomologyOfLisse hH j) :=
  (ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso k₀ l
      (Spec (CommRingCat.of k₀))).app (lowerShriekHomologyAdicOfLisse (k₀ := k₀) hH j) ≪≫
    (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).mapIso
      ((adicSheafEquivCondensedMod l (Spec (CommRingCat.of k₀))).counitIso.app
        (lowerShriekHomologyOfLisse (k₀ := k₀) hH j))

/-- The `j`-th cohomology sheaf of `Ra_! (p^* H)`, as a pro-étale Weil sheaf, is pulled back from
`Mʲ = Hʲ(Ra_! H)`. -/
noncomputable def homologySheafDerivedLowerShriekGeometricFiberPullbackObjIso
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (j : ℤ) :
    ((homologySheaf j).obj ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH)))).obj ≅
      (ProEtaleWeilSheaf.geometricFiberPullback k₀ l (Spec (CommRingCat.of k₀))).obj
        (lowerShriekHomologyAdicOfLisse (k₀ := k₀) hH j) :=
  (ProEtaleWeilSheaf.toCondensed k₀ l (Spec (CommRingCat.of k₀))).preimageIso
    (toCondensedHomologySheafDerivedLowerShriekPullbackIso hH j ≪≫
      (toCondensedGeometricFiberPullbackLowerShriekHomologyIso hH j).symm)

/-- **The cohomology sheaves of `Ra_! (p^* H)`**: the `j`-th cohomology sheaf of the compactly
supported direct image of `p^* H` in the zeta-function chapter is the Weil sheaf on `Spec k₀`
pulled back from `Mʲ = Hʲ(Ra_! H)`. -/
noncomputable def homologySheafDerivedLowerShriekGeometricFiberPullbackIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) :
    (homologySheaf j).obj ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH))) ≅
      WeilSheaf.geometricFiberPullback (k₀ := k₀)
        (isAdicLisseSheaf_lowerShriekHomologyAdicOfLisse hH j) :=
  ObjectProperty.isoMk _ (homologySheafDerivedLowerShriekGeometricFiberPullbackObjIso hH j)

/-- Multiplication by `1` on a lisse sheaf placed in degree `0` is the identity. -/
lemma boundedConstructibleOfLisseSMulIso_one_hom {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (boundedConstructibleOfLisseSMulIso hH 1).hom = 𝟙 _ := by
  have h : AdicSheaf.smul (ULift.up (1 : PadicAlgCl l)) H = 𝟙 H := AdicSheaf.smul_one H
  refine ObjectProperty.hom_ext _ ?_
  simp [boundedConstructibleOfLisseSMulIso, WeilCoefficients.smulIso, h]
  rfl

/-- The structure isomorphism of the Weil object `(H, b)`. -/
lemma weilObjectOfLisse_str {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) :
    (weilObjectOfLisse (k₀ := k₀) hH b).str =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj.{u} l) l
          (overSpec (k₀ := k₀) X)).app (boundedConstructibleOfLisse hH) ≪≫
        boundedConstructibleOfLisseSMulIso hH b :=
  Endofunctor.IsoAlgebra.mk_str _ _

/-- The Weil object `(H, 1)` is `H` placed in degree `0` with the identity Weil structure. -/
noncomputable def weilObjectOfLisseOneIso {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    weilObjectOfLisse (k₀ := k₀) hH 1 ≅
      WeilBoundedConstructible.ofId l (boundedConstructibleOfLisse hH) :=
  Endofunctor.IsoAlgebra.isoMk (Iso.refl _) (by
    refine (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans ?_
    rw [Category.id_comp]
    refine Eq.trans ?_ (Category.comp_id _).symm
    rw [← Endofunctor.IsoAlgebra.str_hom, ← Endofunctor.IsoAlgebra.str_hom,
      weilObjectOfLisse_str, WeilBoundedConstructible.ofId_str, Iso.trans_hom,
      boundedConstructibleOfLisseSMulIso_one_hom]
    exact (Category.comp_id _).symm)

/-- The isomorphism of Weil sheaves on `Spec k₀` between the `j`-th homology sheaf of the
compactly supported cohomology of the Weil object `(H, 1)` and the Weil sheaf
`Mʲ = Hʲ(Ra_! H)` with the identity structure. -/
noncomputable def homologyWeilCompactSupportCohomologyWeilObjectOfLisseIso {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (j : ℤ) :
    (WeilBoundedConstructible.homologyFunctor l (Iso.refl (point k₀)) j).obj
        ((weilCompactSupportCohomology l (Iso.refl (overSpec (k₀ := k₀) X))).obj
          (weilObjectOfLisse (k₀ := k₀) hH 1)) ≅
      WeilSheaf.ofId l (X := point k₀) (lowerShriekHomologyOfLisse hH j) :=
  (WeilBoundedConstructible.homologyFunctor l (Iso.refl (point k₀)) j).mapIso
      ((weilCompactSupportCohomology l (Iso.refl (overSpec (k₀ := k₀) X))).mapIso
          (weilObjectOfLisseOneIso hH) ≪≫
        weilCompactSupportCohomologyOfIdIso l (boundedConstructibleOfLisse hH)) ≪≫
    WeilBoundedConstructible.homologyFunctorOfIdIso l j _

/-- The local trace of the Weil object `(H, 1)` is the trace of the Frobenius on the stalk of the
Weil sheaf `H` with the identity structure. -/
lemma weilStalkTraceAlternatingSum_weilObjectOfLisse_one {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k₀)) ⟶ X)
    (hx : x ≫ ((Iso.refl (overSpec (k₀ := k₀) X)).pow (n + 1)).hom.left =
      ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum l (n + 1) x hx (weilObjectOfLisse (k₀ := k₀) hH 1) =
      weilSheafStalkTrace l (n + 1) x hx (WeilSheaf.ofId l (X := overSpec (k₀ := k₀) X)
        ((adicSheafEquivCondensedMod l X).functor.obj H)) := by
  refine (weilStalkTraceAlternatingSum_congr (e := Iso.refl (overSpec (k₀ := k₀) X)) l n x hx
    (weilObjectOfLisseOneIso hH)).trans ?_
  refine (weilStalkTraceAlternatingSum_ofId_of_isZero (X := overSpec (k₀ := k₀) X) l (n + 1) x hx
    (boundedConstructibleOfLisse hH)
    fun i hi ↦ DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
      (Iso.refl ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H))) hi).trans ?_
  have e : (DerivedCategory.homologyFunctor _ 0).obj (boundedConstructibleOfLisse hH).obj ≅
      (adicSheafEquivCondensedMod l X).functor.obj H :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _
  have h₂ := weilSheafStalkTrace_congr (X := overSpec (k₀ := k₀) X) (e := Iso.refl _) l (n + 1) x hx
    (WeilSheaf.ofIdMapIso (X := overSpec (k₀ := k₀) X) l e)
  exact h₂

end WeilComplex

end AlgebraicGeometry
