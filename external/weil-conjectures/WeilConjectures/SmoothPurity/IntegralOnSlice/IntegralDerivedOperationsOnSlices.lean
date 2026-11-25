/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices

import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-!
# Completed integral operations on the global site and its slices

Source: Bhatt--Scholze, Definition 3.4.10 and Definition 3.5.2; Stacks Project,
Tags 06YY and 08TC (blueprint: def-pur-integral-derived-operations).

The option is only an index for the two sites in the consumer: none is the global
site; some U is its actual over-site. Coefficients and quotient projections on the
latter are sectionwise restrictions. Site object and morphism sizes stay t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe a b c d e f r

private theorem sliceModuleTransport
    {C H : Type a} [Category.{b} C] [Category.{b} H]
    (J : GrothendieckTopology C) (K : GrothendieckTopology H)
    (e : C ≌ H) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{r}) (S : Sheaf K RingCat.{r})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{r} K J).obj R) :
    ∃ q : SheafOfModules.{r} R ≌ SheafOfModules.{r} S,
      q.functor ⋙ SheafOfModules.forget _ =
        SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := e.inverse) c.hom.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  refine ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂, rfl⟩

private theorem resolvingWhiskering
    {K : Type a} [Category.{b} K] {H : Type c} [Category.{d} H]
    {D : Type e} [Category.{f} D]
    (p : K ⥤ H) [p.Full] [p.EssSurj] (hsurj : Function.Surjective p.obj)
    (W : MorphismProperty H) [W.HasRightCalculusOfFractions]
    (q : H ⥤ D) [q.IsLocalization W]
    (P : ObjectProperty K) (S : ObjectProperty H)
    (hp : ∀ X, P X ↔ S (p.obj X))
    (hres : ∀ X : H, ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    Nonempty (((CategoryTheory.Functor.whiskeringLeft
      P.FullSubcategory D D).obj (P.ι ⋙ p ⋙ q)).FullyFaithful) := by
  let f := S.lift (P.ι ⋙ p) (fun X ↦ (hp X.obj).1 X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨g, hg⟩ := p.map_surjective g.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := hsurj X.obj
    refine ⟨⟨Y, (hp Y).2 (hy.symm ▸ X.property)⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
  have : (S.ι ⋙ q).IsLocalization (W.inverseImage S.ι) :=
    restriction_localization W q S hres
  let ff := Localization.fullyFaithfulWhiskeringLeft (S.ι ⋙ q) (W.inverseImage S.ι) D
  let fg := fullyFaithfulWhiskeringOfFullEssSurj f D
  exact ⟨ff.comp fg⟩

private theorem complexWhiskering
    (A : Type a) [Category.{b} A] [Abelian A] [HasDerivedCategory.{e} A]
    (P : ObjectProperty (CochainComplex A ℤ))
    (S : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (hp : ∀ K, P K ↔ S ((HomotopyCategory.quotient A (.up ℤ)).obj K))
    (hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ K),
        HomotopyCategory.quasiIso A (.up ℤ) s) :
    Nonempty (((CategoryTheory.Functor.whiskeringLeft P.FullSubcategory
      (DerivedCategory A) (DerivedCategory A)).obj (P.ι ⋙ DerivedCategory.Q)).FullyFaithful) := by
  have hff := resolvingWhiskering (HomotopyCategory.quotient A (.up ℤ))
    HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh P S hp hres
  let e := Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)
  let ff := Classical.choice hff
  exact ⟨ff.ofIso
    ((CategoryTheory.Functor.whiskeringLeft _ _ (DerivedCategory A)).mapIso e)⟩

private theorem siteWhiskering
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [HasDerivedCategory.{e} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    let A := SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) := fun K ↦
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K ∧
        ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.X i)
    Nonempty (((CategoryTheory.Functor.whiskeringLeft P.FullSubcategory
      (DerivedCategory A) (DerivedCategory A)).obj (P.ι ⋙ DerivedCategory.Q)).FullyFaithful) := by
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun K ↦
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K.as ∧
      ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (K.as.X i)
  exact complexWhiskering A _ S (fun _ ↦ Iff.rfl) (by
    intro K
    obtain ⟨P, g, hP, hflat, hg, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (J := J) (R := R) K.as
    have hs : ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i) := fun i ↦
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hflat i)
    refine ⟨⟨(HomotopyCategory.quotient _ _).obj P, hP, hs⟩,
      (HomotopyCategory.quotient _ _).map g, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg)

private theorem normalizedUnit_existsUnique
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    (p : C ⥤ D)
    (ff : ((CategoryTheory.Functor.whiskeringLeft C D D).obj p).FullyFaithful)
    (F : D ⥤ D) (G : C ⥤ D) (e : p ⋙ F ≅ G) (β : p ⟶ G) :
    ∃! η : 𝟭 D ⟶ F, ∀ P : C, η.app (p.obj P) ≫ e.hom.app P = β.app P := by
  let α : p ⋙ 𝟭 D ⟶ p ⋙ F := β ≫ e.inv
  let η₀ : 𝟭 D ⟶ F := ff.preimage (X := 𝟭 D) (Y := F) α
  have hη₀ : Functor.whiskerLeft p η₀ = α := ff.map_preimage α
  refine ⟨η₀, ?_, ?_⟩
  · intro P
    have h := congrArg (fun k ↦ k.app P) hη₀
    change η₀.app (p.obj P) = β.app P ≫ e.inv.app P at h
    rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro η hη
    apply ff.map_injective
    ext P
    apply (cancel_mono (e.hom.app P)).1
    rw [show (((CategoryTheory.Functor.whiskeringLeft C D D).obj p).map η₀).app P =
      α.app P from congrArg (fun k ↦ k.app P) hη₀]
    change η.app (p.obj P) ≫ _ = α.app P ≫ _
    rw [hη]
    simp only [α, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem arrowConeMap (M : Type*) [Category* M] [Abelian M]
    {K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) :
    HomologicalComplex.homotopyCofiber.mapArrowHom φ₁ φ₂
        (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map φ₁ φ₂ a b h := by
  apply HomologicalComplex.hom_ext
  intro i
  apply HomologicalComplex.homotopyCofiber.ext_from_X φ₁ (i + 1) i rfl
  · change (CochainComplex.mappingCone.inl φ₁).v (i + 1) i (by omega) ≫ _ =
      (CochainComplex.mappingCone.inl φ₁).v (i + 1) i (by omega) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h).f i
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f]
    simp [CochainComplex.mappingCone.inl,
      HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom φ₂
        (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (i + 1) i rfl]
  · change (CochainComplex.mappingCone.inr φ₁).f i ≫ _ =
      (CochainComplex.mappingCone.inr φ₁).f i ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h).f i
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f]
    change HomologicalComplex.homotopyCofiber.inrX φ₁ i ≫ _ = _
    simp [HomologicalComplex.homotopyCofiber.mapArrowHom]
    rfl

private theorem completedCoconeLift_f (M : Type*) [Category* M] [Abelian M]
    {C K L : CochainComplex M ℤ} (φ : K ⟶ L) (u : C ⟶ K)
    (hu : u ≫ φ = 0) (p : ℤ) :
    (CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])).f p =
      u.f p ≫ (CochainComplex.mappingCocone.inl φ).v p p (add_zero p) := by
  let l := CochainComplex.mappingCocone.lift φ u 0 (by simp [hu])
  have h := CochainComplex.mappingCocone.id_X φ p (p + -1) rfl
  calc
    l.f p = l.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [← h, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        CochainComplex.mappingCocone.lift_f_fst_f,
        CochainComplex.mappingCocone.lift_f_snd_v]
      simp

private theorem completedCoconeLift_natural (M : Type*) [Category* M] [Abelian M]
    {C D K₁ K₂ L₁ L₂ : CochainComplex M ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (α : C ⟶ D) (u : C ⟶ K₁) (v : D ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0) (hn : α ≫ v = u ≫ a) :
    α ≫ CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  have hi : (CochainComplex.mappingCocone.inl φ₁).v p p (add_zero p) ≫
      ((CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f p =
      a.f p ≫ (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p) := by
    simp [CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
      CochainComplex.mappingCone.map]
  simp only [HomologicalComplex.comp_f]
  rw [completedCoconeLift_f M φ₂ v hv p, completedCoconeLift_f M φ₁ u hu p,
    Category.assoc, hi, ← Category.assoc]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun z ↦ z.f p ≫
      (CochainComplex.mappingCocone.inl φ₂).v p p (add_zero p)) hn

namespace WeilConjectures
namespace IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- Global or localized site objects. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def Site (U : Option X.ProEt) : Type (t + 1) :=
  match U with
  | none => X.ProEt
  | some V => Over V

/-- The original category structure, with Hom universe t. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
instance siteCategory (U : Option X.ProEt) : Category.{t} (Site X U) :=
  match U with
  | none => inferInstanceAs (Category X.ProEt)
  | some V => inferInstanceAs (Category (Over V))

/-- The actual topology or its over-topology. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def topology (U : Option X.ProEt) : GrothendieckTopology (Site X U) :=
  match U with
  | none => AlgebraicGeometry.Scheme.ProEt.topology X
  | some V => (AlgebraicGeometry.Scheme.ProEt.topology X).over V

/-- Sectionwise coefficient restriction. Source: Stacks 04D5
(blueprint: def-pur-integral-derived-operations). -/
def restrict (U : Option X.ProEt) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (topology X U) CommRingCat.{max u (t + 1)} :=
  match U with
  | none => 𝟭 _
  | some V => (Over.forget V).sheafPushforwardContinuous _ _ _

variable (U : Option X.ProEt)

/-- The existing completed ring on this site. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def ring := (restrict.{t, u} X U).obj (completedIntegralCommRingSheafUnrestricted l E X)

/-- Finite coefficients at exponent n+1. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def finite (n : ℕ) := (restrict.{t, u} X U).obj (integralCoefficientCommRingSheaf l E X n)

/-- The actual restricted quotient projection. Source: Bhatt--Scholze, Section 6.5
(blueprint: def-pur-integral-derived-operations). -/
def projection (n : ℕ) : ring l E X U ⟶ finite l E X U n :=
  (restrict.{t, u} X U).map (completedIntegralCommRingProjectionUnrestricted l E X n)

/-- Abelian sheafification in a size containing the actual site. Source: Stacks 03DA
(blueprint: def-pur-integral-derived-operations). -/
instance abSheafify : HasSheafify (topology X U) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion. Source: Stacks 03DA
(blueprint: def-pur-integral-derived-operations). -/
instance abLocallyBijective :
    (topology X U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall (topology X U)

/-- Forget only commutativity, retaining the exact completed ring data. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
abbrev rings := SheafOfModules.derivedChangeRingIndependentCoefficients (topology X U)
  (ring l E X U)

/-- The existing module category. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
abbrev Mod := ringedSiteModules.{max u (t + 1)} (rings l E X U)

/-- Standard derived localization for these modules. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
instance hasDerived : HasDerivedCategory (Mod l E X U) := HasDerivedCategory.standard _

/-- The derived category of all completed-coefficient modules on this site. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
abbrev D := DerivedCategory (Mod l E X U)

/-- The precise cochain representatives. Source: Stacks 05RU
(blueprint: def-pur-integral-derived-operations). -/
abbrev Cx := CochainComplex (Mod l E X U) ℤ

set_option linter.defProp false in
/-- The universal scalar-extension witness along the specified projection. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
def reductionWitness (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients (topology X U) (finite l E X U n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients (projection l E X U n)

/-- Ordinary change of rings with the witness's fixed objects and maps. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
def reduction (n : ℕ) :
    Mod l E X U ⥤ SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (topology X U) (finite l E X U n)) :=
  (reductionWitness l E X U n).choose

/-- Additivity supplied by the normalized scalar-extension construction. Source: Stacks 06YY
(blueprint: def-pur-integral-derived-operations). -/
instance reductionAdditive (n : ℕ) : (reduction l E X U n).Additive :=
  (reductionWitness l E X U n).choose_spec.choose_spec.choose_spec.choose

attribute [local irreducible] reductionWitness

/-- Termwise reduction with the completed action restored by the actual projection.
Source: Stacks 06YY (blueprint: def-pur-integral-derived-operations). -/
def level (n : ℕ) : Cx l E X U ⥤ Cx l E X U :=
  (reduction l E X U n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n))).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- The normalized scalar-extension functor has the prescribed objects.
Source: Stacks 06YY (blueprint: def-pur-integral-derived-operations).
Proof: project the object-normalization clause of the scalar-extension witness. -/
theorem reduction_obj (n : ℕ) (M : Mod l E X U) :
    (reduction l E X U n).obj M =
      SheafOfModules.changeOfRings
        (projection l E X U n) M :=
  (reductionWitness l E X U n).choose_spec.choose M

/-- The sheafified generator s tensor x of finite reduction. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def generator (n : ℕ) (M : Mod l E X U) (V : (Site X U)ᵒᵖ)
    (s : (finite l E X U n).obj.obj V) (x : M.val.obj V) :
    ((reduction l E X U n).obj M).val.obj V :=
  (eqToHom (reduction_obj l E X U n M).symm).val.app V
    ((toSheafify (topology X U)
      (SheafOfModules.changeOfRingsPresheaf (projection l E X U n) M).presheaf).app V
        (s ⊗ₜ[(ring l E X U).obj.obj V, ((projection l E X U n).hom.app V).hom] x))

private theorem unrestrictedReduction_map (n : ℕ)
    {M N : Mod l E X U} (a : M ⟶ N) :
    (reduction l E X U n).map a =
      eqToHom (reduction_obj l E X U n M) ≫
        SheafOfModules.changeOfRingsHom
          (projection l E X U n) M a ≫
        eqToHom (reduction_obj l E X U n N).symm :=
  (reductionWitness l E X U n).choose_spec.choose_spec.choose a

private theorem sliceGenerator_eq (n : ℕ) (M : Mod l E X U)
    (V : (Site X U)ᵒᵖ) (s : (finite l E X U n).obj.obj V) (x : M.val.obj V) :
    generator l E X U n M V s x =
      (eqToHom (reduction_obj l E X U n M).symm).val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (projection l E X U n) M V s x) := rfl

private def unitPresheaf (n : ℕ) (M : Mod l E X U) :
    M.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n)).hom).obj
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
        (projection l E X U n) M) where
  app V := (ModuleCat.extendRestrictScalarsAdj
    ((projection l E X U n).hom.app V).hom).unit.app (M.val.obj V)
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    ext x
    change (1 : (finite l E X U n).obj.obj W) ⊗ₜ[(ring l E X U).obj.obj W,
      ((projection l E X U n).hom.app W).hom] (show M.val.obj W from M.val.map f x) =
      SheafOfModules.changeOfRingsMap.{t, t + 1, max u (t + 1)} (projection l E X U n) M f
        ((1 : (finite l E X U n).obj.obj V) ⊗ₜ[(ring l E X U).obj.obj V,
          ((projection l E X U n).hom.app V).hom] x)
    have he := ((SheafOfModules.exists_changeOfRingsMap.{t, t + 1, max u (t + 1)}
      (projection l E X U n) M f).choose_spec 1 x).symm
    simp only [map_one] at he
    convert he using 1 <;> rfl

private def unitModule (n : ℕ) (M : Mod l E X U) :
    M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n))).obj ((reduction l E X U n).obj M) where
  val := unitPresheaf l E X U n M ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n)).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
        (R := (sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (finite l E X U n)) (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} (projection l E X U n) M)) ≫
    ((SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (projection l E X U n))).map
      (eqToHom (reduction_obj l E X U n M).symm)).val

private theorem unitModule_apply (n : ℕ) (M : Mod l E X U)
    (V : (Site X U)ᵒᵖ) (x : M.val.obj V) :
    (unitModule l E X U n M).val.app V x = generator l E X U n M V 1 x := by
  rfl

section TransitionConstruction

private theorem generator_map (n : ℕ) {M N : Mod l E X U} (a : M ⟶ N)
    (V : (Site X U)ᵒᵖ) (s : (finite l E X U n).obj.obj V) (x : M.val.obj V) :
    ((reduction l E X U n).map a).val.app V (generator l E X U n M V s x) =
      generator l E X U n N V s (a.val.app V x) := by
  rw [sliceGenerator_eq, sliceGenerator_eq]
  have h : eqToHom (reduction_obj l E X U n M).symm ≫
      (reduction l E X U n).map a =
      SheafOfModules.changeOfRingsHom (projection l E X U n) M a ≫
        eqToHom (reduction_obj l E X U n N).symm := by
    rw [unrestrictedReduction_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  calc
    _ = (eqToHom (reduction_obj l E X U n N).symm).val.app V
        ((SheafOfModules.changeOfRingsHom (projection l E X U n) M a).val.app V
          (SheafOfModules.UnrestrictedTowerProof.tensorSection
            (projection l E X U n) M V s x)) :=
      congrArg (fun k ↦ k.val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (projection l E X U n) M V s x)) h
    _ = _ := congrArg ((eqToHom (reduction_obj l E X U n N).symm).val.app V)
      (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
        (projection l E X U n) M a V s x)

private def moduleUnit (n : ℕ) :
    𝟭 (Mod l E X U) ⟶ reduction l E X U n ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (projection l E X U n)) where
  app M := unitModule l E X U n M
  naturality {M N} a := by
    ext V x
    change (unitModule l E X U n N).val.app V (a.val.app V x) =
      ((reduction l E X U n).map a).val.app V
        ((unitModule l E X U n M).val.app V x)
    rw [unitModule_apply, unitModule_apply, generator_map]

private def levelUnit (n : ℕ) : 𝟭 (Cx l E X U) ⟶ level l E X U n :=
  NatTrans.mapHomologicalComplex (moduleUnit l E X U n) (.up ℤ)

private theorem levelUnit_apply (n : ℕ) (P : Cx l E X U) (i : ℤ)
    (V : (Site X U)ᵒᵖ) (x : (P.X i).val.obj V) :
    (((levelUnit l E X U n).app P).f i).val.app V x =
      generator l E X U n (P.X i) V 1 x :=
  unitModule_apply l E X U n (P.X i) V x

/-- The coefficient reduction, forgetting commutativity only. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def rho (n : ℕ) :
    (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (finite l E X U (n + 1)) ⟶
      (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (finite l E X U n) :=
  match U with
  | none => integralCoefficientSheafTransition l E X n
  | some V => ((Over.forget V).sheafPushforwardContinuous _ _ _).map
      (integralCoefficientSheafTransition l E X n)

private def coefficientStep (n : ℕ) : finite l E X U (n + 1) ⟶ finite l E X U n :=
  (restrict.{t, u} X U).map (WeilConjectures.unrestrictedCoefficientStep l E X n)

private theorem coefficientStep_apply (n : ℕ) (V : (Site X U)ᵒᵖ)
    (s : (finite l E X U (n + 1)).obj.obj V) :
    (coefficientStep l E X U n).hom.app V s = (rho l E X U n).hom.app V s := by
  cases U <;> rfl

private theorem coefficientStep_comp (n : ℕ) :
    projection l E X U (n + 1) ≫ coefficientStep l E X U n = projection l E X U n := by
  exact ((restrict.{t, u} X U).map_comp _ _).symm.trans
    (congrArg (restrict.{t, u} X U).map (WeilConjectures.unrestrictedCoefficientStep_comp l E X n))

private noncomputable def unrestrictedModuleStep (n : ℕ)
    (M : Mod l E X U) :
    (SheafOfModules.UnrestrictedTowerProof.res
      (projection l E X U (n + 1))).obj
        ((reduction l E X U (n + 1)).obj M) ⟶
      (SheafOfModules.UnrestrictedTowerProof.res
        (projection l E X U n)).obj
          ((reduction l E X U n).obj M) :=
  SheafOfModules.UnrestrictedTowerProof.identifiedMap
    (projection l E X U (n + 1))
    (projection l E X U n)
    (coefficientStep l E X U n) (coefficientStep_comp l E X U n) M
    (reduction l E X U (n + 1))
    (reduction l E X U n)
    (reduction_obj l E X U (n + 1))
    (reduction_obj l E X U n)

private theorem unrestrictedModuleStep_naturality (n : ℕ)
    {M N : Mod l E X U} (a : M ⟶ N) :
    (SheafOfModules.UnrestrictedTowerProof.res
      (projection l E X U (n + 1))).map
        ((reduction l E X U (n + 1)).map a) ≫
      unrestrictedModuleStep l E X U n N =
    unrestrictedModuleStep l E X U n M ≫
      (SheafOfModules.UnrestrictedTowerProof.res
        (projection l E X U n)).map
          ((reduction l E X U n).map a) :=
  SheafOfModules.UnrestrictedTowerProof.identifiedMap_naturality
    (projection l E X U (n + 1))
    (projection l E X U n)
    (coefficientStep l E X U n) (coefficientStep_comp l E X U n) M
    (reduction l E X U (n + 1))
    (reduction l E X U n)
    (reduction_obj l E X U (n + 1))
    (reduction_obj l E X U n)
    (unrestrictedReduction_map l E X U (n + 1))
    (unrestrictedReduction_map l E X U n) a

private theorem unrestrictedModuleStep_tmul (n : ℕ) (M : Mod l E X U)
    (V : (Site X U)ᵒᵖ)
    (s : (finite l E X U (n + 1)).obj.obj V) (x : M.val.obj V) :
    (unrestrictedModuleStep l E X U n M).val.app V
      (generator l E X U (n + 1) M V s x) =
    generator l E X U n M V
      ((rho l E X U n).hom.app V s) x := by
  have h := SheafOfModules.UnrestrictedTowerProof.identifiedMap_tmul
    (projection l E X U (n + 1))
    (projection l E X U n)
    (coefficientStep l E X U n) (coefficientStep_comp l E X U n) M
    (reduction l E X U (n + 1))
    (reduction l E X U n)
    (reduction_obj l E X U (n + 1))
    (reduction_obj l E X U n) V s x
  rw [sliceGenerator_eq, sliceGenerator_eq]
  simp only [coefficientStep_apply] at h
  convert h using 1 <;> rfl

private theorem unrestrictedReduction_hom_ext (n : ℕ) (M N : Mod l E X U)
    (a b : (SheafOfModules.UnrestrictedTowerProof.res
      (projection l E X U n)).obj
        ((reduction l E X U n).obj M) ⟶ N)
    (h : ∀ V s x, a.val.app V (generator l E X U n M V s x) =
      b.val.app V (generator l E X U n M V s x)) : a = b :=
  SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (projection l E X U n) M
    (reduction l E X U n)
    (reduction_obj l E X U n) N a b
      (fun V s x ↦ by
        convert h V s x using 1 <;> rfl)

attribute [local irreducible] unrestrictedModuleStep

/-- Consecutive reduction maps are uniquely specified on generators. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations).
Proof: send s tensor x to rho(s) tensor x. The projection compatibility makes this
balanced and completed-linear. Restrictions and differentials commute with this
formula. Sheafification and tensor generation give existence and uniqueness. -/
theorem transition_existsUnique (n : ℕ) :
    ∃! τ : level l E X U (n + 1) ⟶ level l E X U n,
      ∀ (P : Cx l E X U) (i : ℤ) (V : (Site X U)ᵒᵖ)
        (s : (finite l E X U (n + 1)).obj.obj V) (x : (P.X i).val.obj V),
        ((τ.app P).f i).val.app V (generator l E X U (n + 1) (P.X i) V s x) =
          generator l E X U n (P.X i) V ((rho l E X U n).hom.app V s) x := by
  let τ : level l E X U (n + 1) ⟶
      level l E X U n :=
    { app := fun P ↦
        { f := fun i ↦ unrestrictedModuleStep l E X U n (P.X i)
          comm' := fun i j _ ↦
            (unrestrictedModuleStep_naturality l E X U n (P.d i j)).symm }
      naturality := fun P Q a ↦ by
        apply HomologicalComplex.hom_ext
        intro i
        exact unrestrictedModuleStep_naturality l E X U n (a.f i) }
  have hτ : ∀ (P : CochainComplex (Mod l E X U) ℤ) (i : ℤ)
      (V : (Site X U)ᵒᵖ)
      (s : (finite l E X U (n + 1)).obj.obj V)
      (x : (P.X i).val.obj V),
      ((τ.app P).f i).val.app V
        (generator l E X U (n + 1) (P.X i) V s x) =
      generator l E X U n (P.X i) V
        ((rho l E X U n).hom.app V s) x :=
    fun P i V s x ↦ unrestrictedModuleStep_tmul l E X U n (P.X i) V s x
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply unrestrictedReduction_hom_ext l E X U (n + 1) (P.X i)
  intro V s x
  exact (hτ' P i V s x).trans (hτ P i V s x).symm

end TransitionConstruction

/-- The actual transition fixed by the preceding tensor formula. Source: Stacks 03EK
(blueprint: def-pur-integral-derived-operations). -/
def transition (n : ℕ) : level l E X U (n + 1) ⟶ level l E X U n :=
  (transition_existsUnique l E X U n).exists.choose

/-- The actual strict reduction tower. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def tower : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U) :=
  (Functor.ofOpSequence (X := fun n ↦ level l E X U n) (transition l E X U)).flip

attribute [local irreducible] levelUnit

/-- The unique augmentation has x mapped to 1 tensor x at every positive exponent.
Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: def-pur-integral-derived-operations).
Proof: the scalar-extension adjunction unit is completed-linear and natural. Apply
it degreewise; its compatibility with rho follows because rho preserves one. Pure
tensor generation and sheafification determine the maps uniquely. -/
theorem augmentation_existsUnique :
    ∃! γ : (Functor.const ℕᵒᵖ : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U)) ⟶ tower l E X U,
      ∀ (P : Cx l E X U) (n : ℕ) (i : ℤ) (V : (Site X U)ᵒᵖ) (x : (P.X i).val.obj V),
        (((γ.app P).app (op n)).f i).val.app V x =
          generator l E X U n (P.X i) V 1 x := by
  let γ : (Functor.const ℕᵒᵖ : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U)) ⟶
      tower l E X U :=
    { app := fun P ↦ NatTrans.ofOpSequence
        (fun n ↦ (levelUnit l E X U n).app P)
        (fun n ↦ by
          change 𝟙 P ≫ _ = _ ≫ _
          rw [Category.id_comp]
          change (levelUnit l E X U n).app P =
            (levelUnit l E X U (n + 1)).app P ≫
              ((Functor.ofOpSequence (transition l E X U)).map
                (homOfLE (Nat.le_succ n)).op).app P
          rw [Functor.ofOpSequence_map_homOfLE_succ]
          ext i V x
          change (((levelUnit l E X U n).app P).f i).val.app V x =
            (((transition l E X U n).app P).f i).val.app V
              ((((levelUnit l E X U (n + 1)).app P).f i).val.app V x)
          have hn := (transition_existsUnique l E X U n).exists.choose_spec P i V 1 x
          simp only [map_one] at hn
          exact (levelUnit_apply l E X U n P i V x).trans
            (hn.symm.trans (congrArg
              ((((transition l E X U n).app P).f i).val.app V)
              (levelUnit_apply l E X U (n + 1) P i V x)).symm))
      naturality := fun {P Q} f ↦ by
        apply NatTrans.ext
        funext n
        exact (levelUnit l E X U n.unop).naturality f }
  refine ⟨γ, ?_, ?_⟩
  · intro P n i V x
    exact levelUnit_apply l E X U n P i V x
  · intro γ' hγ'
    ext P n i V x
    exact (hγ' P n.unop i V x).trans
      (levelUnit_apply l E X U n.unop P i V x).symm

/-- The canonical reduction augmentation. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def augmentation :
    (Functor.const ℕᵒᵖ : Cx l E X U ⥤ (ℕᵒᵖ ⥤ Cx l E X U)) ⟶ tower l E X U :=
  (augmentation_existsUnique l E X U).exists.choose

attribute [local irreducible] tower augmentation

/-- K-flat representatives with flat terms. Source: Stacks 06YN
(blueprint: def-pur-integral-derived-operations). -/
def Good : ObjectProperty (Cx l E X U) := fun P ↦
  CochainComplex.IsKFlatIndependentCoefficients (J := topology X U) (R := ring l E X U) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := ring l E X U) (P.X i)

/-- Localization of the resolving class into the existing derived category. Source: Stacks 06YN
(blueprint: def-pur-integral-derived-operations). -/
def qGood := (Good l E X U).ι ⋙ DerivedCategory.Q

/-- The actual Roos complex of the strict quotient tower. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def roos := tower l E X U ⋙ integralOperationsRoosFunctor

/-- Quotient completion on all good representatives. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def roosGood := (Good l E X U).ι ⋙ roos l E X U ⋙ DerivedCategory.Q

private theorem sliceProductsExact :
    HasExactLimitsOfShape (Discrete ℕ) (Mod l E X U) := by
  cases U with
  | none =>
      exact AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} X
        (rings l E X none) ℕ
  | some V =>
      let J := (AlgebraicGeometry.Scheme.ProEt.topology X).over V
      let K := AlgebraicGeometry.Scheme.ProEt.topology V.left
      let e := AlgebraicGeometry.Scheme.ProEt.sliceEquiv X V
      let : e.inverse.IsDenseSubsite K J := AlgebraicGeometry.Scheme.ProEt.sliceDense X V
      let R := rings l E X (some V)
      let S := (e.inverse.sheafPushforwardContinuous RingCat.{max u (t + 1)} K J).obj R
      obtain ⟨q, _⟩ := sliceModuleTransport J K e R S (Iso.refl _)
      let := AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} V.left S ℕ
      exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) q.symm

private theorem goodLocalization :
    (qGood l E X U).IsLocalization
      ((HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)).inverseImage
        (Good l E X U).ι) := by
  let : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  exact goodComplexes_isLocalization (ring l E X U) (Good l E X U) (fun _ ↦ Iff.rfl)

private theorem levelQuasiIso (n : ℕ) {P Q : Cx l E X U} (α : P ⟶ Q)
    (hP : Good l E X U P) (hQ : Good l E X U Q) (hα : QuasiIso α) :
    QuasiIso ((level l E X U n).map α) := by
  let : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients (topology X U) (finite l E X U n)))
  let φ := (sheafCompose _
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E X U n)
  let T := SheafOfModules.restrictScalars φ
  have hT := coefficientRestriction_exact φ
  let : PreservesFiniteLimits T := hT.1
  let : PreservesFiniteColimits T := hT.2
  have h := (reductionWitness l E X U n).choose_spec.choose_spec.choose_spec.choose_spec.1
    α hP.1 hQ.1 hα
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ T (hφ := h)

private theorem roosGoodInverts :
    ((HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)).inverseImage
      (Good l E X U).ι).IsInvertedBy (roosGood l E X U) := by
  let := sliceProductsExact l E X U
  intro P Q α hα
  change IsIso (DerivedCategory.Q.map
    (integralOperationsRoosMap ((tower l E X U).map α.hom)))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  apply roosMap_quasiIso
  intro n
  delta WeilConjectures.IntegralOnSlice.tower
  change QuasiIso ((level l E X U n).map α.hom)
  exact levelQuasiIso l E X U n α.hom P.property Q.property hα

/-- Completion is the unique descent equipped with its representative comparison.
Source: Stacks 06YN, 08TC (blueprint: def-pur-integral-derived-operations).
Proof: restriction has exact underlying sheaves, also on a slice; the pro-etale
countable-product theorem restricts to its over-site. Reduction carries K-flat
quasi-isomorphisms to quasi-isomorphisms. Roos preserves these by exact products.
Every derived object has a good representative. The resolving-class localization
therefore descends roosGood, and is fully faithful on natural transformations,
which determines this functor together with its comparison uniquely. -/
theorem completion_exists :
    ∃ F : D l E X U ⥤ D l E X U,
      Nonempty (qGood l E X U ⋙ F ≅ roosGood l E X U) ∧
      ∀ (F' : D l E X U ⥤ D l E X U) (e : qGood l E X U ⋙ F ≅ roosGood l E X U)
        (e' : qGood l E X U ⋙ F' ≅ roosGood l E X U),
        ∃! a : F ≅ F', Functor.whiskerLeft (qGood l E X U) a.hom ≫ e'.hom = e.hom := by
  let W := (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)).inverseImage
    (Good l E X U).ι
  let := goodLocalization l E X U
  let hR := roosGoodInverts l E X U
  let F := Localization.lift (roosGood l E X U) hR (qGood l E X U)
  let e₀ := Localization.fac (roosGood l E X U) hR (qGood l E X U)
  let ff := Localization.fullyFaithfulWhiskeringLeft (qGood l E X U) W (D l E X U)
  refine ⟨F, ⟨e₀⟩, ?_⟩
  intro F' e e'
  let a : F ≅ F' := ff.isoEquiv.symm (e ≪≫ e'.symm)
  have ha : Functor.isoWhiskerLeft (qGood l E X U) a = e ≪≫ e'.symm :=
    ff.isoEquiv.apply_symm_apply _
  refine ⟨a, ?_, ?_⟩
  · have hi : Functor.isoWhiskerLeft (qGood l E X U) a ≪≫ e' = e := by
      rw [ha]
      simp
    exact congrArg Iso.hom hi
  · intro b hb
    apply ff.isoEquiv.injective
    change Functor.isoWhiskerLeft (qGood l E X U) b =
      Functor.isoWhiskerLeft (qGood l E X U) a
    rw [ha]
    apply Iso.ext
    apply (cancel_mono e'.hom).1
    simpa using hb

/-- Completion chosen with its determining representative normalization. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def completion : D l E X U ⥤ D l E X U :=
  (completion_exists l E X U).choose

/-- The normalized comparison on every good representative. Source: Stacks 08TC
(blueprint: def-pur-integral-derived-operations). -/
def completionComparison : qGood l E X U ⋙ completion l E X U ≅ roosGood l E X U :=
  (completion_exists l E X U).choose_spec.1.some

attribute [local irreducible] completion completionComparison

/-- The augmentation into the termwise product. Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-pur-integral-derived-operations). -/
def productAugmentation (P : Cx l E X U) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ ((augmentation l E X U).app P).app (op n))

/-- The zero homotopy witnesses the strict augmentation's composite with 1-s.
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations).
Proof: postcompose with every product projection. Consecutive quotient augmentations
agree after transition by naturality of augmentation. Hence c(1-s)=0. The differential
of the zero cochain and the cochain of the zero chain map are both zero. -/
theorem roosUnit_condition (P : Cx l E X U) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain P
        (∏ᶜ fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (productAugmentation l E X U P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
            (integralOperationsTowerStep ((tower l E X U).obj P))) = 0 := by
  have h : productAugmentation l E X U P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
        (integralOperationsTowerStep ((tower l E X U).obj P)) = 0 := by
    apply Pi.hom_ext
    intro n
    have hn := ((augmentation l E X U).app P).naturality
      (homOfLE (Nat.le_succ n)).op
    simpa [productAugmentation, towerTransitionEndomorphism, towerProductShift,
      integralOperationsTowerStep, Category.assoc] using sub_eq_zero.mpr hn
  rw [h]
  simp

/-- The prescribed quotient unit is the explicit chain map (c,0) into Cone(1-s)[-1].
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations). -/
def roosUnit (P : Cx l E X U) :
    P ⟶ integralOperationsRoos ((tower l E X U).obj P) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
      (integralOperationsTowerStep ((tower l E X U).obj P)))
    (productAugmentation l E X U P) 0 (roosUnit_condition l E X U P)

private theorem goodWhiskering :
    Nonempty (((CategoryTheory.Functor.whiskeringLeft
      (Good l E X U).FullSubcategory (D l E X U) (D l E X U)).obj
      (qGood.{t, u} l E X U)).FullyFaithful) := by
  let : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  set_option backward.isDefEq.respectTransparency true in
    exact siteWhiskering (topology X U) (ring l E X U)

private theorem roosUnit_eq (P : Cx l E X U) :
    roosUnit l E X U P = CochainComplex.mappingCocone.lift
      (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
        (integralOperationsTowerStep ((tower l E X U).obj P)))
      (productAugmentation l E X U P) 0 (roosUnit_condition l E X U P) := rfl

attribute [local irreducible] roosUnit

private theorem sliceRoosUnit_natural {P Q : Cx.{t, u} l E X U} (a : P ⟶ Q) :
    a ≫ roosUnit.{t, u} l E X U Q = roosUnit.{t, u} l E X U P ≫ (roos.{t, u} l E X U).map a := by
  have hz (T : Cx.{t, u} l E X U) : productAugmentation.{t, u} l E X U T ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((tower.{t, u} l E X U).obj T).obj (op n))
        (integralOperationsTowerStep ((tower.{t, u} l E X U).obj T)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using roosUnit_condition.{t, u} l E X U T
  have hn : a ≫ productAugmentation.{t, u} l E X U Q =
      productAugmentation.{t, u} l E X U P ≫
        Limits.Pi.map (fun n ↦ ((tower.{t, u} l E X U).map a).app (op n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, productAugmentation, Limits.Pi.lift_comp_π,
      Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
    simpa only [Functor.const_map_app, CategoryTheory.NatTrans.comp_app] using
      congrArg (fun k ↦ k.app (op n)) ((augmentation.{t, u} l E X U).naturality a)
  rw [roosUnit_eq, roosUnit_eq]
  change a ≫ _ = _ ≫ (shiftFunctor _ (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ _)
  rw [arrowConeMap]
  exact completedCoconeLift_natural (Mod l E X U) _ _ _ _
    (integralOperationsRoos_square ((tower.{t, u} l E X U).map a)) a _ _ (hz P) (hz Q) hn

/-- The quotient unit descends uniquely with its (c,0) normalization on good representatives.
Source: Stacks 06YN, 08TC (blueprint: def-pur-integral-derived-operations).
Proof: the chain-level unit commutes with maps, by its product components and its zero
second cochain. Its equality survives quasi-isomorphisms between good representatives.
Fully faithful restriction of transformations along the resolving-class localization
supplies exactly one natural transformation with the displayed formula. -/
theorem completionUnit_existsUnique :
    ∃! η : 𝟭 (D l E X U) ⟶ completion l E X U,
      ∀ P : (Good l E X U).FullSubcategory,
        η.app ((qGood l E X U).obj P) ≫ (completionComparison l E X U).hom.app P =
          DerivedCategory.Q.map (roosUnit l E X U P.obj) := by
  let ff := Classical.choice (goodWhiskering l E X U)
  let β : qGood.{t, u} l E X U ⟶ roosGood.{t, u} l E X U :=
    { app := fun P ↦ DerivedCategory.Q.map (roosUnit.{t, u} l E X U P.obj)
      naturality := by
        intro P Q a
        change DerivedCategory.Q.map a.hom ≫ _ = _ ≫
          DerivedCategory.Q.map ((roos.{t, u} l E X U).map a.hom)
        simpa only [← Functor.map_comp] using
          congrArg DerivedCategory.Q.map (sliceRoosUnit_natural l E X U a.hom) }
  exact normalizedUnit_existsUnique (qGood l E X U) ff
    (completion l E X U) (roosGood l E X U) (completionComparison l E X U) β

/-- The unique completion unit determined on all K-flat flat-term representatives.
Source: Stacks 08TC (blueprint: def-pur-integral-derived-operations). -/
def completionUnit : 𝟭 (D l E X U) ⟶ completion l E X U :=
  Classical.choose (α := 𝟭 (D l E X U) ⟶ completion l E X U)
    (p := fun η ↦ ∀ P : (Good l E X U).FullSubcategory,
      η.app ((qGood l E X U).obj P) ≫ (completionComparison l E X U).hom.app P =
        DerivedCategory.Q.map (roosUnit l E X U P.obj))
    (ExistsUnique.exists (completionUnit_existsUnique l E X U))

/-- The ambient internal Hom, with independent site and coefficient sizes. Source: Stacks 08J7
(blueprint: def-pur-integral-derived-operations). -/
def hom : (D l E X U)ᵒᵖ × D l E X U ⥤ D l E X U :=
  derivedInternalHomOfUniverses.{t + 1, t, u} (topology X U) (ring l E X U)

/-- The normalized ordinary derived tensor-Hom model. Source: Stacks 08JD
(blueprint: def-pur-integral-derived-operations). -/
def duality : RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (topology X U) (ring l E X U) :=
  Classical.choice (ringedSiteDualityMaps_exists (topology X U) (ring l E X U))

/-- Completed tensor as quotient completion of ordinary derived tensor. The balanced
finite-level identity identifies this with the recorded two-reduction construction.
Source: Bhatt--Scholze, Definition 3.4.10 (blueprint: def-pur-integral-derived-operations). -/
def completedTensor : (D l E X U) × (D l E X U) ⥤ D l E X U :=
  (duality l E X U).closed.tensor ⋙ completion l E X U

attribute [local irreducible] duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard constantSheaf
  completedIntegralCoefficientSheafUnrestricted

private theorem globalTower_eq :
    tower l E X none =
      (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E X n)
        (unrestrictedIntegralTransition l E X)).flip := by
  have h (n : ℕ) : transition l E X none n = unrestrictedIntegralTransition l E X n := by
    apply (transition_existsUnique l E X none n).unique
      (transition_existsUnique l E X none n).exists.choose_spec
    intro P i V s x
    exact (unrestrictedIntegralTransition_existsUnique l E X n).exists.choose_spec P i V s x
  have hh : transition l E X none = unrestrictedIntegralTransition l E X := funext h
  delta tower
  rw [hh]

private theorem totalTensorGood
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    Good l E X none
      ((coefficientTotalTensor.{u, t + 1, t} (topology X none)
        (ring l E X none)).obj (P.obj, Q.obj)) := by
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (ring l E X none) P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  exact ⟨h.1, h.2.1⟩

private def totalTensorOnGood :
    (integralOperationsGoodComplex l E X).FullSubcategory ×
      (integralOperationsGoodComplex l E X).FullSubcategory ⥤
        (Good l E X none).FullSubcategory :=
  ObjectProperty.lift _
    (((integralOperationsGoodComplex l E X).ι.prod
      (integralOperationsGoodComplex l E X).ι) ⋙
        coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none))
    (fun P ↦ totalTensorGood l E X P.1 P.2)

private theorem tensorCompletionOnGood :
    Nonempty (((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ completedTensor l E X none ≅
        totalTensorOnGood l E X ⋙ roosGood l E X none) := by
  let H : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none) :
            ObjectProperty (Cx l E X none)) :=
    ObjectProperty.lift _ (integralOperationsGoodComplex l E X).ι
      (fun P ↦ P.property.1)
  let c := Functor.isoWhiskerLeft (H.prod H) (duality l E X none).models.comparison
  have c' : ((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ (duality l E X none).closed.tensor ≅
        totalTensorOnGood l E X ⋙ qGood l E X none := c.symm
  let e := Functor.isoWhiskerRight c' (completion l E X none)
  let d := Functor.isoWhiskerLeft (totalTensorOnGood l E X)
    (completionComparison l E X none)
  exact ⟨e ≪≫ d⟩

/-- The global specialization computes precisely the recorded finite-tensor Roos model,
so this extension does not introduce a different global tensor product.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 06YY
(blueprint: def-pur-integral-derived-operations).
Proof: for flat-term K-flat P,Q, their ordinary tensor is K-flat with flat terms.
Apply completionComparison to that tensor and the ordinary tensor comparison of
RingedSiteDualityModel.models. At each finite level reassociate balanced tensors:
(p tensor a) tensor (q tensor b) maps to (p tensor q) tensor ab, and its inverse
sends (p tensor q) tensor a to (p tensor 1) tensor (q tensor a). Both maps preserve
the total differential and every quotient transition. Their strict tower isomorphism
gives a Roos isomorphism, natural in P,Q. Compose with the representative comparisons.
The target is exactly integralOperationsTensorOnGood, not an arbitrary derived model. -/
theorem completedTensor_global_comparison :
    Nonempty (((integralOperationsGoodLocalization l E X).prod
      (integralOperationsGoodLocalization l E X)) ⋙ completedTensor l E X none ≅
        integralOperationsTensorOnGood l E X) := by
  obtain ⟨a⟩ := tensorCompletionOnGood l E X
  obtain ⟨b⟩ := integralTensorReductionTowerComparison l E X
  let H := (integralOperationsGoodComplex l E X).ι.prod
    (integralOperationsGoodComplex l E X).ι
  let T := coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)
  let R := integralOperationsRoosFunctor (A := Mod l E X none)
  let Q := DerivedCategory.Q (C := Mod l E X none)
  let W := tower l E X none
  let V := integralOperationsTensorTowerFunctor l E X
  have e : totalTensorOnGood l E X ⋙ (Good l E X none).ι ≅ H ⋙ T :=
    (Good l E X none).liftCompιIso (H ⋙ T) (fun P ↦ totalTensorGood l E X P.1 P.2)
  have b' : T ⋙ W ≅ V := by
    dsimp only [T, W, V]
    rw [globalTower_eq]
    exact b
  refine ⟨a ≪≫ ?_⟩
  exact (Functor.associator (totalTensorOnGood l E X)
      (Good l E X none).ι (roos l E X none ⋙ Q)).symm ≪≫
    Functor.isoWhiskerRight e (roos l E X none ⋙ Q) ≪≫
    Functor.isoWhiskerLeft (H ⋙ T) (Functor.associator W R Q) ≪≫
    (Functor.associator (H ⋙ T) W (R ⋙ Q)).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator H T W) (R ⋙ Q) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H b') (R ⋙ Q) ≪≫
    Functor.associator H V (R ⋙ Q) ≪≫
    Functor.isoWhiskerLeft H (Functor.associator V R Q).symm

end IntegralOnSlice
end WeilConjectures
