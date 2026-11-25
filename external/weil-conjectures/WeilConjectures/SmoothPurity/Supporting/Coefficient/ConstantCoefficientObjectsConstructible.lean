/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import all WeilConjectures.SmoothPurity.ConstantScalarUnitQuasiIsomorphism.ConstantScalarUnitQuasiIsomorphism
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-!
# Constant coefficient objects are bounded constructible

Source: Weil blueprint, ordinary and compactly supported cohomology, order 1510;
Bhatt--Scholze, Sections 3.5, 6.5 and Definition 6.8.1, Lemma 6.8.2
(blueprint: lem-weil-constant-coefficient-objects-constructible).
The finite and completed coefficient objects are the regular module sheaves in degree zero.
All positive levels are indexed by n : ℕ, denoting exponent n+1. Rationalization is raw,
and algebraically closed coefficients use the recorded small finite-field models.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local instance] HasDerivedCategory.standard

local instance instEssentiallySmallProEt_constantCoefficientObjectsConstructible
    (Y : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _

private theorem exists_coefficientTestDatum (l : ℕ) :
    ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  refine ⟨D, ?_⟩
  change l ≠ p
  omega

-- Sheafification comparison elaborates several large dependent module categories.
private noncomputable def constantRegularIso
    (Y : AlgebraicGeometry.Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleConstantModuleSheaf Y A (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)) ≅
      SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)) := by
  classical
  let J := ProEt.topology Y
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let a : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶ R.obj :=
    Functor.whiskerRight (toSheafify J
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  letI := (proEtaleConstantRingUnit_locallyBijective Y A).1
  letI := (proEtaleConstantRingUnit_locallyBijective Y A).2
  let P := proEtaleConstantModulePresheaf Y.ProEt A
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
    (PresheafOfModules.sheafificationHomEquiv.{u + 1} a (P := P)
      (F := SheafOfModules.unit R)).symm η
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
  haveI : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J _ hfac, Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac⟩
  haveI : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact asIso f

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The finite constant ring sheaf, as its regular module in degree zero.
Source: blueprint order 1510; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def finiteConstantCoefficientObject (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- The completed coefficient ring, as its regular module in degree zero.
Source: Bhatt--Scholze, Definition 6.8.1, Lemma 6.8.2(1)
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def integralConstantCoefficientObject :
    DerivedCategory (scalarReductionSource l E Y) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- The completed-ring projection as a linear map into the restricted quotient module.
The image of 1 is the compatible section 1, so its sectionwise formula is precisely π_n.
Source: Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constantCoefficientProjection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (scalarReductionRestriction l E Y n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj U))
      (fun {_ _} f ↦ map_one ((integralCoefficientSheaf l E Y n).obj.map f).hom))

/-- The canonical derived reduction map: transpose the actual coefficient projection
through the normalized derived tensor/restriction adjunction. Exact restriction commutes
with placing a sheaf in degree zero via Mathlib's specified single-functor comparison.
Source: Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible). -/
noncomputable def constantCoefficientReductionMap (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        (integralConstantCoefficientObject l E Y) ⟶ finiteConstantCoefficientObject l E Y n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (constantCoefficientProjection l E Y n) ≫
      ((scalarReductionRestriction l E Y n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)))

/-- Part 1: the finite constant object is bounded constructible, and its underlying
sheaf is locally constant on Y itself, with finite stalks isomorphic to A_{E,n+1}.
Source: blueprint order 1510; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the integer ring is a DVR with finite residue field, so all its positive-power
quotients are finite (lem-weil-valued-dvr-finite-quotients). Use the single stratum Y,
with identity immersion; Y is locally closed and constructible in itself. The identity
cover trivializes the constant regular module. The constant germ calculation
(lem-weil-proetale-constant-sheaf-stalk) identifies each geometric stalk with the
coefficient ring, hence makes it finite. A single complex has this constructible sheaf
as H^0 and zero cohomology in every other degree. This is exactly the finite-torsion
constructibility condition. The empty scheme has no geometric points and is allowed. -/
theorem finiteConstantCoefficient_constructible (n : ℕ) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y
        (finiteConstantCoefficientObject l E Y n) ∧
      IsLocallyConstantProEtaleModuleSheaf Y (Padic.coefficientExtensionRing l E (n + 1))
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : AlgebraicGeometry.Spec (.of Ω) ⟶ Y),
        (∃ e : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+
            proEtaleGeometricModuleStalk y
              (integralCoefficientCommRingSheaf l E Y n)
              (SheafOfModules.unit (integralCoefficientSheaf l E Y n)),
          ∀ a b : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
            e (a * b) = proEtaleConstantRingGerm y
              (Padic.coefficientExtensionRing l E (n + 1)) a • e b) ∧
        Finite (proEtaleGeometricModuleStalk y
          (integralCoefficientCommRingSheaf l E Y n)
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n))) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := integralCoefficientSheaf l E Y n
  have hr : (SheafOfModules.unit R).IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
      _).mp inferInstance
  obtain ⟨hl, hc, hf⟩ := finiteLocallyFreeLine_models Y A (SheafOfModules.unit R) hr
  obtain ⟨hfin, hconst, _, _⟩ := constructible_single_support Y A
    (SheafOfModules.unit R) hc (finiteConstantCoefficientObject l E Y n) (Iso.refl _)
  refine ⟨⟨hfin, hconst⟩, hl, ?_⟩
  intro Ω _ _ y
  let M := ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)
  let eM := (geometricRingModuleStalkFunctor y
    (integralCoefficientCommRingSheaf l E Y n)).mapIso (constantRegularIso Y A)
  have hg := proEtaleConstantModuleGerm_bijective y A M
  let e : ULift.{u + 1} A ≃+
      proEtaleGeometricModuleStalk y (integralCoefficientCommRingSheaf l E Y n)
        (SheafOfModules.unit R) :=
    (AddEquiv.ofBijective (proEtaleConstantModuleGerm y A M) hg.1).trans
      eM.toLinearEquiv.toAddEquiv
  refine ⟨⟨e, ?_⟩, hf Ω y⟩
  intro a b
  change eM.hom (proEtaleConstantModuleGerm y A M (a • b)) = _
  rw [hg.2.1]
  exact eM.hom.hom.map_smul _ _

-- The normalized adjunction comparison traverses several localization isomorphisms.
/-- Part 2, with the same integral membership in both recorded presentations.
Source: blueprint order 1510; Bhatt--Scholze, Definition 3.5.2, Section 6.5,
Definition 6.8.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-constant-coefficient-objects-constructible).
Proof: the regular module in degree zero is K-flat, since tensoring with it is the
identity on complexes. Compute each reduction by this representative: multiplication
R_n tensor_R R → R_n is the unit isomorphism and is the transpose of π_n. Thus the
specified reduction map is invertible. Its target is the finite constant object of
Part 1; all reductions have cohomology supported in [0,0]. Their transition maps are
the quotient reductions and are surjective: locally lift a constant quotient section
from the integer ring. Restriction of scalars leaves the underlying sheaf unchanged.
Their ordinary inverse limit is the completed coefficient sheaf by its construction.
Apply lem-weil-proetale-surjective-tower-derived-limit to obtain its Roos triangle
with the actual projections. These are exactly the canonical reduction units, so
both recorded completeness predicates hold. Together with Part 1 and the common
interval [0,0], this proves membership in both recorded integral full subcategories.
This does not assert uniqueness of an arbitrary lift to a triangulated homotopy limit. -/
theorem integralConstantCoefficient_constructible
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    boundedConstructibleDerivedCompleteIntegral D l hl E Y
        (integralConstantCoefficientObject l E Y) ∧
      sfIntegralConstructible l E Y (integralConstantCoefficientObject l E Y) ∧
      IsDerivedCompleteUnrestricted l E Y (integralConstantCoefficientObject l E Y) ∧
      ∀ n : ℕ, IsIso (constantCoefficientReductionMap l E Y n) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E Y n).obj
            (integralConstantCoefficientObject l E Y)) ⊆ Set.Icc 0 0 := by
  classical
  obtain ⟨D₀, hl₀⟩ := exists_coefficientTestDatum l
  obtain ⟨hg, _, _, hv, _, _⟩ :=
    ConstantScalarStrictUnit.regular_scalar_strict_unit.{0, u, u} l E Y E (AlgHom.id _ _) D₀ hl₀
  let P : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ :=
    ConstantScalarStrictUnit.regularComplex.{u, u} l E Y
  have hcomplete := ConstantScalarUnitQuasiIsomorphism.regular_complete.{u, u} l E Y D₀ hl₀ hg hv
  have hsf : IsSfDerivedComplete l E Y (integralConstantCoefficientObject l E Y) :=
    (sfDerivedComplete_iff_legacy l E Y D₀ hl₀ _).mpr hcomplete
  have hred (n : ℕ) : IsIso (constantCoefficientReductionMap l E Y n) := by
    obtain ⟨v, _, hu, _⟩ := hv n
    let c : (scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P) :=
      @asIso _ _ _ _ ((scalarReductionCounit l E Y n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
        (unrestrictedTowerCounit_isIso l E Y n P hg.1)
    let t : (scalarReductionDerivedExtension l E Y n).obj
        (integralConstantCoefficientObject l E Y) ⟶ finiteConstantCoefficientObject l E Y n :=
      c.hom ≫ DerivedCategory.Q.map v.hom
    have ht : IsIso t := by dsimp [t]; infer_instance
    have hc : sfReductionRepresentativeComparison l E Y n P =
        (scalarReductionDerivedRestriction l E Y n).map c.hom ≫
          (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.hom.app
            (unrestrictedTowerFiniteComplex l E Y n P) := by
      change (scalarReductionDerivedRestriction l E Y n).map c.hom ≫
        (scalarReductionRestriction l E Y n).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (unrestrictedTowerFiniteComplex l E Y n P)) = _
      erw [Functor.mapDerivedCategoryFactorsh_hom_app]
      simp! [c,
        DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
        Category.assoc]
      change (scalarReductionDerivedRestriction l E Y n).map c.hom ≫
        (scalarReductionRestriction l E Y n).mapDerivedCategory.map (𝟙 _) ≫
        (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.hom.app
          (unrestrictedTowerFiniteComplex l E Y n P) ≫ 𝟙 _ = _
      erw [CategoryTheory.Functor.map_id]
      erw [Category.id_comp, Category.comp_id]
      rfl
    have heq : constantCoefficientReductionMap l E Y n = t := by
      let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
      unfold constantCoefficientReductionMap
      apply (adj.homEquiv (integralConstantCoefficientObject l E Y)
        (finiteConstantCoefficientObject l E Y n)).injective
      rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
      apply (cancel_mono ((scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.hom.app
          (ConstantScalarStrictUnit.finiteRegularComplex l E Y n))).1
      have hn := (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors_hom_naturality
        v.hom
      have hunit := representative_unit l E Y n P hg.1
      have hproj :
          (DerivedCategory.singleFunctor (scalarReductionSource l E Y) 0).map
              (constantCoefficientProjection l E Y n) ≫
            ((scalarReductionRestriction l E Y n).mapDerivedCategorySingleFunctor 0).inv.app
              (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
            (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.hom.app
              (ConstantScalarStrictUnit.finiteRegularComplex l E Y n) =
          DerivedCategory.Q.map (ConstantScalarStrictUnit.projectionComplex l E Y n) := by
        erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
        change DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (scalarReductionSource l E Y) 0).map
            (constantCoefficientProjection l E Y n)) ≫ _ = _
        rw [← DerivedCategory.Q.map_comp]
        rfl
      simp only [Category.assoc]
      calc
        _ = DerivedCategory.Q.map (ConstantScalarStrictUnit.projectionComplex l E Y n) := hproj
        _ = DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n) ≫
            DerivedCategory.Q.map
              (((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map
                v.hom) := by rw [← DerivedCategory.Q.map_comp, hu]
        _ = _ := by
          rw [← hunit, hc]
          simp only [t, Functor.map_comp, Category.assoc]
          exact congrArg (fun f ↦ adj.unit.app _ ≫
            (scalarReductionDerivedRestriction l E Y n).map c.hom ≫ f) hn.symm
    rw [heq]
    exact ht
  have hbounds (n : ℕ) :
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((scalarReductionDerivedExtension l E Y n).obj
          (integralConstantCoefficientObject l E Y)) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E Y n).obj
          (integralConstantCoefficientObject l E Y)) ⊆ Set.Icc 0 0 := by
    let := hred n
    let e := asIso (constantCoefficientReductionMap l E Y n)
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have hi : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) Y) :=
      (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated Y
        (Padic.coefficientExtensionRing l E (n + 1))).1
    let R := integralCoefficientSheaf l E Y n
    have hr : (SheafOfModules.unit R).IsFiniteLocallyFreeOfRank 1 :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
        _).mp inferInstance
    have hc := (finiteConstantCoefficient_constructible l E Y n).1
    obtain ⟨_, _, hs, _⟩ := constructible_single_support Y
      (Padic.coefficientExtensionRing l E (n + 1))
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n))
      ((finiteLocallyFreeLine_models Y _ (SheafOfModules.unit R) hr).2.1)
      (finiteConstantCoefficientObject l E Y n) (Iso.refl _)
    refine ⟨ObjectProperty.prop_of_iso _ e.symm hc, ?_⟩
    intro i hi
    have hz : i ∈ proEtaleCohomologicalSupport (finiteConstantCoefficientObject l E Y n) := by
      intro hzero
      exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mpr hzero)
    have he : i = 0 := hs hz
    simp [he]
  refine ⟨?_, ⟨hsf, 0, 0, le_refl _, hbounds⟩, ⟨D₀, hl₀, hcomplete⟩,
    fun n ↦ ⟨hred n, (hbounds n).2⟩⟩
  exact ⟨(sfDerivedComplete_iff_legacy l E Y D hl _).mp hsf,
    0, 0, le_refl _, fun n ↦ ⟨(hbounds n).1, fun i hi ↦ (hbounds n).2 hi⟩⟩

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

namespace AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

end AlgebraicallyClosedCoefficients
end WeilConjectures
