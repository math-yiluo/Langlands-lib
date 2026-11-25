/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicTensorComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.ConstructibleSheaf.Monoidal

/-! # Finiteness under exact tensor by a finite coefficient line

Source: definition-tate-twists--10, proof steps 4--5.
(blueprint: lem-weil-finite-line-tensor-conditions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem constant_unit_over (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) :
    Nonempty (SheafOfModules.unit
        (((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)).over U) ≅
      proEtaleConstantModuleSheafOver S A U
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) := by
  classical
  let J := (ProEt.topology S).over U
  let R := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing S A)).over U
  let a : (Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶ R.obj :=
    Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let := (proEtaleConstantRingUnit_over_locallyBijective S A U).1
  let := (proEtaleConstantRingUnit_over_locallyBijective S A U).2
  let P := proEtaleConstantModulePresheaf (Over U) A
    (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))
  let η : P ⟶ (PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val :=
    { app V := ModuleCat.ofHom (X := P.obj V)
        (Y := ((PresheafOfModules.restrictScalars a).obj (SheafOfModules.unit R).val).obj V)
        { toFun := fun x ↦ a.app V x
          map_add' := fun x y ↦ map_add (a.app V).hom x y
          map_smul' := fun x y ↦ map_mul (a.app V).hom x y }
      naturality f := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (a.naturality f) x) }
  let f : (PresheafOfModules.sheafification.{u + 1} a).obj P ⟶ SheafOfModules.unit R :=
    (PresheafOfModules.sheafificationHomEquiv.{u + 1} a).symm η
  have hfac : toSheafify J P.presheaf ≫
      (PresheafOfModules.toPresheaf R.obj).map f.val =
        Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
    have h := (PresheafOfModules.sheafificationHomEquiv.{u + 1} a (P := P)
      (F := SheafOfModules.unit R)).apply_symm_apply η
    exact (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def a f).symm.trans
      (congrArg (fun g ↦ (PresheafOfModules.toPresheaf _).map g) h)
  have hi : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J a x y h⟩
  have hs : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight a (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
    ⟨fun x ↦ Presheaf.imageSieve_mem J a x⟩
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J _ hfac, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact ⟨(asIso f).symm⟩

private theorem line_constant_models (S : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ ProEt.precoverage S (ProEt.mk (𝟙 S)) ∧
        ∀ i, Nonempty (L.over (U i) ≅ proEtaleConstantModuleSheafOver S A (U i)
          (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) := by
  classical
  obtain ⟨I, U, hc, he⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp inferInstance
  obtain ⟨Q, hQ, hle⟩ := ProEt.mem_topology_iff.mp (hc (ProEt.mk (𝟙 S)))
  let V : Q.uncurry → S.ProEt := fun i ↦ i.1.1
  let f : ∀ i : Q.uncurry, V i ⟶ ProEt.mk (𝟙 S) := fun i ↦ i.1.2
  have hQeq : Presieve.ofArrows V f = Q := by
    funext W g
    apply propext
    constructor
    · rintro ⟨i⟩
      exact i.2
    · intro hg
      exact @Presieve.ofArrows.mk _ _ _ _ V f ⟨⟨W, g⟩, hg⟩
  refine ⟨Q.uncurry, V, f, hQeq.symm ▸ hQ, ?_⟩
  intro i
  obtain ⟨j, ⟨g⟩⟩ := hle _ _ i.2
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  let e := (he j).some ≪≫ SheafOfModules.freeUniqueIso _
  let e' : L.over (V i) ≅ SheafOfModules.unit (R.over (V i)) :=
    ((SheafOfModules.overFunctorMap R g).app L).symm ≪≫
      (SheafOfModules.overMap R g).mapIso e ≪≫ SheafOfModules.overMapUnitIso (R := R) g
  exact ⟨e' ≪≫ (constant_unit_over S A (V i)).some⟩

private theorem line_locally_constant (S : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1] : IsLocallyConstantProEtaleModuleSheaf S A L := by
  obtain ⟨I, U, f, hf, h⟩ := line_constant_models S A L
  exact ⟨I, U, f, hf, fun i ↦ ⟨_, h i⟩⟩

private theorem line_finite_models (S : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1] :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((proEtaleModuleRestriction S A).obj L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := line_constant_models S A L
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a (ModuleCat.of B B)
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B) :=
    E.mapIso (he i).some ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a (ModuleCat.of B B))).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app (ModuleCat.of B B)
  exact ⟨ModuleCat.of B B, inferInstance, ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

private noncomputable def realization_restriction_iso
    (S : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    F ≅ (proEtaleModuleRestriction S A).obj ((sfIntrinsicModuleEquivalence S A).functor.obj F) := by
  let P := (ProEtale.finiteCoefficientModulePresheaf S.ProEt (ULift.{u + 1} A)).obj F.obj
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap S A)
  let η : F ⟶ (proEtaleModuleRestriction S A).obj
      ((sfIntrinsicModuleEquivalence S A).functor.obj F) :=
    ⟨{ app U := (adj.unit.app P).app U
       naturality _ _ f := by
         ext x
         exact ConcreteCategory.congr_hom ((adj.unit.app P).naturality f) x }⟩
  have : IsIso η := by
    have : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology S) P.presheaf)
      exact isIso_toSheafify (ProEt.topology S)
        ((sheafCompose (ProEt.topology S)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A))
            AddCommGrpCat.{u + 1})).obj F).property
    have hη (U : S.ProEtᵒᵖ) : IsIso (η.hom.app U) := by
      have : IsIso ((PresheafOfModules.toPresheaf _).map (adj.unit.app P)) := inferInstance
      have : IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U) :=
        inferInstance
      rw [← isIso_iff_of_reflects_iso _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1})]
      change IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U)
      infer_instance
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    change IsIso η.hom
    rw [NatTrans.isIso_iff_isIso_app]
    exact hη
  exact asIso η

private theorem fixed_constructible_tensor (S : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (M N : Sheaf (ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (hM : ProEtale.IsConstructible (ULift.{u + 1} A) M)
    (hN : ProEtale.IsConstructible (ULift.{u + 1} A) N) :
    ProEtale.IsConstructible (ULift.{u + 1} A) (M ⊗ N) := by
  obtain ⟨M', hM', ⟨eM⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ hM
  obtain ⟨N', hN', ⟨eN⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ hN
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
  exact ProEtale.isConstructible_of_iso
    ((Functor.Monoidal.μIso V M' N').symm ≪≫ tensorIso eM eN)
    (by
      let := hM'.tensorObj hN'
      exact ProEtale.isConstructible_comparisonUpperStar_obj (M' ⊗ N'))

private theorem finite_line_constructible (S : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1]
    (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (hM : IsConstructibleProEtaleModuleSheaf S A M) :
    IsConstructibleProEtaleModuleSheaf S A
      ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).obj M) := by
  let R := proEtaleConstantRing S A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let E := sfIntrinsicModuleEquivalence S A
  let C := proEtaleModuleRestriction S A
  let FM := E.inverse.obj M
  let FL := E.inverse.obj L
  let eM : FM ≅ C.obj M := realization_restriction_iso S A FM ≪≫
    C.mapIso (E.counitIso.app M)
  let eL : FL ≅ C.obj L := realization_restriction_iso S A FL ≪≫
    C.mapIso (E.counitIso.app L)
  have hFM : ProEtale.IsConstructible (ULift.{u + 1} A) FM :=
    ProEtale.isConstructible_of_iso eM.symm
      ((proEtaleModuleRestriction_constructible_iff S A M).mp hM)
  have hFL : ProEtale.IsConstructible (ULift.{u + 1} A) FL := by
    refine ProEtale.isConstructible_of_iso eL.symm ⟨Stratification.trivial S, fun _ ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId _ S).app _).symm (line_finite_models S A L)
  have ht := fixed_constructible_tensor S A FM FL hFM hFL
  obtain ⟨q⟩ := AlgebraicGeometry.proEtale_intrinsic_tensorRight_comparison S A FL
  let e : (SheafOfModules.siteSheafTensorRight (A := R) L).obj M ≅
      E.functor.obj (FM ⊗ FL) :=
    (SheafOfModules.siteSheafTensorRightIso R L).app M ≪≫
      tensorIso (E.counitIso.app M).symm (E.counitIso.app L).symm ≪≫
      ((SheafOfModules.siteSheafTensorRightIso R (E.functor.obj FL)).app
        (E.functor.obj FM)).symm ≪≫ q.app FM
  apply (proEtaleModuleRestriction_constructible_iff S A _).mpr
  exact ProEtale.isConstructible_of_iso (C.mapIso e).symm
    (ProEtale.isConstructible_of_iso (realization_restriction_iso S A (FM ⊗ FL)) ht)

set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_line_tor (S : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := proEtaleConstantRing S A) L).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)]
    [PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)]
    (K : proEtaleDerivedCategory S A) (a b : ℤ)
    (hK : HasProEtaleTorAmplitude S A K a b) :
    HasProEtaleTorAmplitude S A
      ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).mapDerivedCategory.obj K) a b := by
  classical
  have hab := hK.1
  let R := proEtaleConstantRing S A
  let C := proEtaleRingModules S R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  have := SheafOfModules.isGrothendieckAbelian_kfg R
  have := SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let (X₁ X₂ : GradedObject ℤ C) : X₁.HasTensor X₂ := inferInstance
  let := HasDerivedCategory.standard C
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) :=
    DerivedCategory.instMonoidalCategory C
  have hk (P : CochainComplex C ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj N)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  have heq (K : DerivedCategory C) (L P : CochainComplex C ℤ) (e : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) (M : C) :
      Nonempty (MonoidalCategory.tensorObj K ((DerivedCategory.singleFunctor C 0).obj M) ≅
        derivedTensor S A L ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
    exact ⟨(MonoidalCategory.tensorIso (e.symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm)
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P _ (hk P hP)⟩
  have hamp (K : DerivedCategory C) : HasProEtaleTorAmplitude S A K a b ↔
      DerivedCategory.torAmplitudeIn C a b K := by
    constructor
    · intro h M
      have : (DerivedCategory.Q (C := C)).EssSurj :=
        Localization.essSurj _ (HomologicalComplex.quasiIso _ (.up ℤ))
      let L := (DerivedCategory.Q (C := C)).objPreimage K
      let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
      obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
      obtain ⟨eq⟩ := heq K L P e f hf hP M
      rw [DerivedCategory.homologyConcentratedIn_iff]
      refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inl hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq)
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inr hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq)
    · intro h
      refine ⟨hab, ?_⟩
      rintro L P ⟨e⟩ f hf hP M i hi
      obtain ⟨eq⟩ := heq K L P e f hf hP M
      have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
          (MonoidalCategory.tensorObj K ((DerivedCategory.singleFunctor C 0).obj M))) := by
        obtain ⟨hge, hle⟩ := (DerivedCategory.homologyConcentratedIn_iff _ _ _).1 (h M)
        rcases hi with hi | hi
        · exact (DerivedCategory.isGE_iff _ a).1 hge i hi
        · exact (DerivedCategory.isLE_iff _ b).1 hle i hi
      exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq.symm)
  let F := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L
  have hL : PreservesFiniteLimits (MonoidalCategory.tensorRight L) :=
    preservesFiniteLimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R L)
  let := hL
  let : F.PreservesFlat :=
    { flat_obj := fun {M} hM ↦ by
        let : PreservesFiniteLimits (tensorRight M) := hM.2.1
        let : PreservesFiniteLimits (tensorRight M ⋙ tensorRight L) :=
          comp_preservesFiniteLimits _ _
        have : PreservesFiniteLimits (MonoidalCategory.tensorRight (M ⊗ L)) :=
          preservesFiniteLimits_of_natIso (MonoidalCategory.tensorRightTensor M L).symm
        have hML : ObjectProperty.flat (M ⊗ L) :=
          (ObjectProperty.flat_iff_preservesFiniteLimits _).2
            (preservesFiniteLimits_of_natIso
              (BraidedCategory.tensorLeftIsoTensorRight _).symm)
        exact ObjectProperty.flat.prop_of_iso
          ((SheafOfModules.siteSheafTensorRightIso R L).app M).symm hML }
  exact (hamp _).2 (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj F ((hamp K).1 hK))

/-- Exact tensor by a rank-one sheaf preserves constructible sheaves and every Tor interval.
Source: blueprint definition-tate-twists--10, proof steps 4--5
(blueprint: lem-weil-finite-line-tensor-conditions).

Proof: a rank-one trivialization over the constant coefficient ring is a constant
rank-one module model; hence the line is locally constant. Pull a trivializing cover
back to each member of a constructible stratification and refine its locally constant
models. The tensor then has model M tensor A, canonically isomorphic to M. Thus it
has the same finite stalks and the same finite partition, including on the empty scheme.
For Tor amplitude choose flat-term K-flat models P for K and Q for a test module M.
Tensor by the line is exact, so it preserves acyclic complexes and the vanishing of
cohomology in each degree. Associativity and symmetry identify
(P tensor L) tensor Q with (P tensor Q) tensor L. Tensor by L preserves the direct
sums in total tensor, being a left adjoint. The complex P tensor L is still K-flat
and has flat terms: its tensor with an acyclic complex is an exact line twist of
an acyclic tensor. Consequently this rebracketing computes both derived tensors.
Apply the assumed Tor interval of K to M, then exact line tensor; the same ordered
interval works for all module sheaves M, with no constructibility assumption on M. -/
theorem finiteLineTensor_conditions (S : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    [L.IsFiniteLocallyFreeOfRank 1]
    [(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := proEtaleConstantRing S A) L).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)]
    [PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L)] :
    IsLocallyConstantProEtaleModuleSheaf S A L ∧
      (∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
        IsConstructibleProEtaleModuleSheaf S A M →
        IsConstructibleProEtaleModuleSheaf S A
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).obj M)) ∧
      ∀ (K : proEtaleDerivedCategory S A) (a b : ℤ),
        HasProEtaleTorAmplitude S A K a b →
        HasProEtaleTorAmplitude S A
          ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
        (A := proEtaleConstantRing S A) L).mapDerivedCategory.obj K) a b := by
  refine ⟨line_locally_constant S A L, finite_line_constructible S A L, ?_⟩
  exact fun K a b hK ↦ finite_line_tor S A L K a b hK

end WeilConjectures
