/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import all WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Supporting.StrictDvrReductionTriangles
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedEpimorphicTopDerivedLimit
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SixFunctors.Sf.SfWeaklyContractibleProjective
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.SixFunctors.Supporting.ProjectiveCohomologySplitModel
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SixFunctors.Completed.CompletedFreeCellOrdinaryLimit
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement

/-! # Lifting a prescribed top residue basis

Source: Stacks Project, proetale.tex, Tag 09C3, final induction paragraph
(blueprint: lem-sf-complete-lifted-top-cell-triangle).

The free cell is the existing single complex in degree b, namely P[-b]. The residue
identification is normalized by the actual coefficient quotient on its generators.
The scheme universe t and coefficient universe u are independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompleteLiftedTopCell

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{t})

/-- The standard rank-r residue module, including the empty product, which is zero.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
abbrev residueFree (r : ℕ) : scalarReductionTarget l E T 0 :=
  ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)

/-- The residue free cell in degree b, i.e. k^r[-b].
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
abbrev residueCell (r : ℕ) (b : ℤ) :=
  (DerivedCategory.singleFunctor (scalarReductionTarget l E T 0) b).obj
    (residueFree l E T r)

/-- The coefficient quotient on each standard generator of the finite free module.
Restriction preserves products; its canonical product comparison identifies the target.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def freeQuotient (r : ℕ) :
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ⟶
        (scalarReductionRestriction l E T 0).obj (residueFree l E T r) :=
  let := scalarReductionRestrictionLimits l E T 0
  Limits.Pi.map (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0) ≫
    inv (piComparison (scalarReductionRestriction l E T 0)
      (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)))

/-- The canonical free-cell quotient in the completed-coefficient derived category.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def freeCellQuotient (r : ℕ) (b : ℤ) :
    DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b) ⟶
      (scalarReductionDerivedRestriction l E T 0).obj (residueCell l E T r b) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.singleFunctor (scalarReductionSource l E T) b).map
      (freeQuotient l E T r) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategorySingleFunctor b).inv.app
      (residueFree l E T r)

/-- The actual top cohomology reduction, with the exact restriction comparison.
Source: Stacks Tags 06YY and 09C3
(blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def topReduction (M : DerivedCategory (scalarReductionSource l E T)) (b : ℤ) :
    (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).obj M ⟶
      (scalarReductionRestriction l E T 0).obj
        ((DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).obj
          ((scalarReductionDerivedExtension l E T 0).obj M)) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).map
      (CompletedCoefficientFree.reductionMap l E T 0 M) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategoryHomologyFunctorIso b).inv.app
      ((scalarReductionDerivedExtension l E T 0).obj M)

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

-- Prefer the same standard localizations used by the scalar-reduction functors.
attribute [local instance 3000] scalarReductionSourceDerived scalarReductionTargetDerived

attribute [local irreducible] unrestrictedIntegralReductionExistence
  integralReductionExistence integralReductionDerivedExistence
  unrestrictedTowerUnit unrestrictedTowerTransition unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison unrestrictedTowerComparison
  strictDvrReductionComparison

attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private theorem complete_local_iff (K : IntegralOnSlice.D l E T none) :
    IsDerivedCompleteUnrestricted l E T K ↔
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K := by
  classical
  obtain ⟨P₀, q, hP₀, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) (DerivedCategory.Q.objPreimage K)
  let : QuasiIso q := hq
  let P : (IntegralOnSlice.Good l E T none).FullSubcategory :=
    ⟨P₀, hP₀, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (IntegralOnSlice.ring l E T none) _).symm
        (hflat i)⟩
  let e : DerivedCategory.Q.obj P.obj ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  exact (roosIntrinsicCompletenessEquivalence p l (by omega) E T d hd K P e).out 1 2

private theorem complete_cone (Δ : Triangle (DerivedCategory (scalarReductionSource l E T)))
    (hΔ : Δ ∈ distTriang _) (h₁ : IsDerivedCompleteUnrestricted l E T Δ.obj₁)
    (h₂ : IsDerivedCompleteUnrestricted l E T Δ.obj₂) :
    IsDerivedCompleteUnrestricted l E T Δ.obj₃ := by
  apply (complete_local_iff l E T Δ.obj₃).mpr
  have h₁' := (complete_local_iff l E T Δ.obj₁).mp h₁
  have h₂' := (complete_local_iff l E T Δ.obj₂).mp h₂
  intro U s hs
  let : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let R := IntegralOnSlice.rings l E T none
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over U))
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R U
  let : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  let : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  let A := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)
  let H := (Functor.curry.obj (IntegralOnSlice.hom l E T (some U))).obj (op A)
  obtain ⟨hshift, htri⟩ :=
    (CategoryTheory.RingedHomUniverses.ringedInternalHom_exact
      (IntegralOnSlice.topology T (some U)) (IntegralOnSlice.ring l E T (some U))).2 A
  let : H.CommShift ℤ := hshift
  let : H.IsTriangulated := htri
  let G := F.mapDerivedCategory ⋙ H
  have e (K : IntegralOnSlice.D l E T none) :
      IntegralPrincipalCone.localTest l E T K U s ≅ G.obj K :=
    (IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso R U K))
  exact ((Pretriangulated.Triangle.isZero₃_of_isZero₁₂ _
    (G.map_distinguished Δ hΔ) ((e Δ.obj₁).isZero_iff.mp (h₁' U s hs))
      ((e Δ.obj₂).isZero_iff.mp (h₂' U s hs)))).of_iso (e Δ.obj₃)

private theorem normalized_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (P : C) (S : D) (b : ℤ) (K : DerivedCategory D)
    (β : (DerivedCategory.singleFunctor C b).obj P ⟶ R.mapDerivedCategory.obj K)
    (e : K ≅ (DerivedCategory.singleFunctor D b).obj S) (q : P ⟶ R.obj S)
    (he : β ≫ R.mapDerivedCategory.map e.hom =
      (DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).inv.app P ≫
        (DerivedCategory.homologyFunctor C b).map β ≫
        (R.mapDerivedCategoryHomologyFunctorIso b).inv.app K =
      q ≫ R.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso D b).inv.app S ≫
        (DerivedCategory.homologyFunctor D b).map e.inv) := by
  let HB := DerivedCategory.homologyFunctor C b
  let Hk := DerivedCategory.homologyFunctor D b
  let εB := DerivedCategory.singleFunctorCompHomologyFunctorIso C b
  let εk := DerivedCategory.singleFunctorCompHomologyFunctorIso D b
  have hsingle := R.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor b S
  have hcompat : HB.map ((R.mapDerivedCategorySingleFunctor b).inv.app S) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) ≫ R.map (εk.hom.app S) =
        (εB.hom.app (R.obj S)) := by
    apply (cancel_epi (HB.map ((R.mapDerivedCategorySingleFunctor b).hom.app S))).1
    rw [← HB.map_comp_assoc, Iso.hom_inv_id_app, HB.map_id, Category.id_comp]
    apply (cancel_epi ((R.mapDerivedCategoryHomologyFunctorIso b).hom.app
      ((DerivedCategory.singleFunctor _ b).obj S))).1
    rw [Iso.hom_inv_id_app_assoc]
    exact hsingle.symm
  have hq : εB.inv.app P ≫
      HB.map ((DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) ≫ R.map (εk.hom.app S) =
      q := by
    rw [HB.map_comp]
    simp only [Category.assoc]
    rw [hcompat]
    have hh := εB.hom.naturality (q)
    change HB.map ((DerivedCategory.singleFunctor _ b).map _) ≫ εB.hom.app _ =
      εB.hom.app P ≫ q at hh
    exact (congrArg (fun f ↦ εB.inv.app P ≫ f) hh).trans
      (Iso.inv_hom_id_app_assoc εB P _)
  have hn := (R.mapDerivedCategoryHomologyFunctorIso b).inv.naturality e.hom
  change HB.map (R.mapDerivedCategory.map e.hom) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) =
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app _ ≫ R.map (Hk.map e.hom) at hn
  apply (cancel_mono (R.map (Hk.map e.hom ≫ εk.hom.app S))).1
  change (εB.inv.app P ≫ (HB.map β ≫ (R.mapDerivedCategoryHomologyFunctorIso b).inv.app K)) ≫
      R.map (Hk.map e.hom ≫ εk.hom.app S) =
    (q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv)) ≫
      R.map (Hk.map e.hom ≫ εk.hom.app S)
  simp only [Category.assoc]
  rw [← R.map_comp]
  have hi : (εk.inv.app S ≫ Hk.map e.inv) ≫ (Hk.map e.hom ≫ εk.hom.app S) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (Hk.map e.inv),
      ← Hk.map_comp, e.inv_hom_id, Hk.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rw [hi]
  erw [R.map_id, Category.comp_id]
  rw [R.map_comp]
  rw [← reassoc_of% hn]
  rw [← HB.map_comp_assoc, he]
  exact hq

private theorem single_unit_extension
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    (η : 𝟭 C ⟶ F ⋙ R) (X : C) (Y : D) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (b : ℤ) :
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app
        ((CochainComplex.singleFunctor C b).obj X) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).hom.app X) ≫
          (CochainComplex.singleFunctor D b).map e.hom) ≫
      (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).hom.app Y =
        (CochainComplex.singleFunctor C b).map p := by
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at *
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc]
  simp only [Iso.inv_hom_id_assoc, R.map_comp, Category.assoc]
  have hn := η.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom
  change (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom ≫ η.app X =
    η.app _ ≫ R.map (F.map (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom) at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% he]
  simp only [← R.map_comp_assoc, Iso.inv_hom_id, R.map_id, Category.id_comp]

private theorem derived_single_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : 𝟭 C ⟶ F ⋙ R) (X : C) (Y : D) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (b : ℤ)
    (K : DerivedCategory D)
    (c : K ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor C b).obj X)))
    (β : (DerivedCategory.singleFunctor C b).obj X ⟶ R.mapDerivedCategory.obj K)
    (hc : β ≫ R.mapDerivedCategory.map c.hom ≫ R.mapDerivedCategoryFactors.hom.app _ =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (.up ℤ)).app
        ((CochainComplex.singleFunctor C b).obj X))) :
    let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).app X ≪≫
      (CochainComplex.singleFunctor D b).mapIso e
    β ≫ R.mapDerivedCategory.map (c.hom ≫ DerivedCategory.Q.map eC.hom) =
      (DerivedCategory.singleFunctor C b).map p ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app Y := by
  intro eC
  apply (cancel_mono ((R.mapDerivedCategorySingleFunctor b).hom.app Y)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hs : (R.mapDerivedCategorySingleFunctor b).hom.app Y =
      R.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor D b).obj Y) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).hom.app Y) := by
    simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Iso.refl_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
      Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
    erw [Category.id_comp]
  rw [hs, Functor.map_comp]
  simp only [Category.assoc]
  have hn := R.mapDerivedCategoryFactors.hom.naturality eC.hom
  change R.mapDerivedCategory.map (DerivedCategory.Q.map eC.hom) ≫
    R.mapDerivedCategoryFactors.hom.app _ = R.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map eC.hom) at hn
  rw [reassoc_of% hn]
  erw [reassoc_of% hc, Category.comp_id]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map (single_unit_extension F R η X Y e p he b)

private theorem projective_normalized_lift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : D ⥤ C) [R.Faithful] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (η : 𝟭 _ ⟶ F ⋙ R.mapDerivedCategory) (P : C) [Projective P]
    (S : D) (b : ℤ) (q : P ⟶ R.obj S) [Epi q]
    (e : F.obj ((DerivedCategory.singleFunctor C b).obj P) ≅
      (DerivedCategory.singleFunctor D b).obj S)
    (he : η.app _ ≫ R.mapDerivedCategory.map e.hom =
      (DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S)
    (M : DerivedCategory C)
    (θ : S ≅ (DerivedCategory.homologyFunctor D b).obj (F.obj M))
    (hEpi : Epi ((DerivedCategory.homologyFunctor C b).map (η.app M) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app (F.obj M))) :
    ∃ f : (DerivedCategory.singleFunctor C b).obj P ⟶ M,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D b).inv.app S ≫
        (DerivedCategory.homologyFunctor D b).map (e.inv ≫ F.map f) = θ.hom := by
  let HB := DerivedCategory.homologyFunctor C b
  let Hk := DerivedCategory.homologyFunctor D b
  let εB := DerivedCategory.singleFunctorCompHomologyFunctorIso C b
  let εk := DerivedCategory.singleFunctorCompHomologyFunctorIso D b
  let top (N : DerivedCategory C) := HB.map (η.app N) ≫
    (R.mapDerivedCategoryHomologyFunctorIso b).inv.app (F.obj N)
  have hn {N N' : DerivedCategory C} (f : N ⟶ N') :
      HB.map f ≫ top N' = top N ≫ R.map (Hk.map (F.map f)) := by
    have hη := η.naturality f
    have hH := (R.mapDerivedCategoryHomologyFunctorIso b).inv.naturality (F.map f)
    change f ≫ η.app N' = η.app N ≫ R.mapDerivedCategory.map (F.map f) at hη
    dsimp only [top]
    rw [← Category.assoc, ← HB.map_comp, hη, HB.map_comp, Category.assoc]
    simpa only [HB, Hk, Functor.comp_map, Functor.id_obj, Category.assoc] using
      congrArg (fun g ↦ HB.map (η.app N) ≫ g) hH
  let : Epi (top M) := hEpi
  let x := Projective.factorThru (q ≫ R.map θ.hom) (top M)
  have hx : x ≫ top M = q ≫ R.map θ.hom := Projective.factorThru_comp _ _
  obtain ⟨f, hf⟩ := (WeilConjectures.sfProjectiveHomologyBijective P M b).2
    (εB.hom.app P ≫ x)
  change HB.map f = εB.hom.app P ≫ x at hf
  have hf' : εB.inv.app P ≫ HB.map f = x := by rw [hf, Iso.inv_hom_id_app_assoc]
  have hnorm := normalized_homology R P S b _ (η.app _) e q he
  change εB.inv.app P ≫ top _ = q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv) at hnorm
  refine ⟨f, ?_⟩
  apply R.map_injective
  apply (cancel_epi q).1
  calc
    _ = (q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv)) ≫ R.map (Hk.map (F.map f)) := by
      change q ≫ R.map (εk.inv.app S ≫ Hk.map (e.inv ≫ F.map f)) = _
      simp only [Hk.map_comp, R.map_comp, Category.assoc]
    _ = (εB.inv.app P ≫ top _) ≫ R.map (Hk.map (F.map f)) :=
      congrArg (fun g ↦ g ≫ R.map (Hk.map (F.map f))) hnorm.symm
    _ = (εB.inv.app P ≫ HB.map f) ≫ top M := by
      rw [Category.assoc, ← hn, ← Category.assoc]
    _ = _ := by rw [hf', hx]

private theorem restriction_faithful
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{v}} (φ : R ⟶ S) :
    (SheafOfModules.restrictScalars.{v} φ).Faithful where
  map_injective := by
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun k ↦ (k.val.app U) x) h

end WeilConjectures.CompleteLiftedTopCell
