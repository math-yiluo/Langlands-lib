/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleRestrictScalars
import WeilConjectures.Algebra.Category.Ring.IsPushoutOfSurjective
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.SixFunctors.RamifiedPullback.RamifiedCoefficientQuotientComparison
import all WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerIdentification
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Finite reductions after rational scalar restriction

Exact restriction identifies each finite reduction with restriction of a finite
coefficient reduction of the original object. The same finite stratifications,
interval, and local models are retained after restriction of scalars. This is
separated from completeness because it is a finite-level constructibility
assertion.
(blueprint: lem-sf-rational-scalar-restriction-reduction-constructible)
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

section RamifiedSquare

/-- The ramification index `e` of the integral coefficient extension, with
`ι(ϖ_E) O_F = ϖ_F^e O_F`. Source: Serre, Local Fields, Chapter I, Proposition 9. -/
theorem exists_coefficientRamification :
    ∃ e : ℕ, 1 ≤ e ∧
      Ideal.span ({(integralScalarIntegerInclusion l E F ι
        (Padic.coefficientExtensionUniformizer l E))} :
          Set (Padic.coefficientExtensionIntegers l F)) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e} := by
  obtain ⟨e, he, h, _⟩ := RamifiedPullback.ramification_exists l E F ι
  exact ⟨e, he, h⟩

/-- The ramified exponent identity `index e n + 1 = e (n + 1)` for `1 ≤ e`. -/
theorem ramifiedIndex_add_one {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    RamifiedPullback.index e n + 1 = e * (n + 1) := by
  have h := Nat.mul_le_mul_right (n + 1) he
  simp only [RamifiedPullback.index]
  omega

/-- A source uniformizer power maps into the ramified target ideal.
Source: Bhatt--Scholze, Lemma 6.8.2(1). -/
theorem ramifiedCoefficientQuotient_kernel {e : ℕ} (he : 1 ≤ e)
    (hideal : Ideal.span ({(integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E))} :
        Set (Padic.coefficientExtensionIntegers l F)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e}) (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E (n + 1)) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (RamifiedPullback.index e n + 1))
      (integralScalarIntegerInclusion l E F ι x) = 0 := by
  have hi : Ideal.map (integralScalarIntegerInclusion l E F ι)
      (Padic.coefficientExtensionIdeal l E (n + 1)) =
        Padic.coefficientExtensionIdeal l F (RamifiedPullback.index e n + 1) := by
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow]
    rw [Ideal.map_span, Set.image_singleton, hideal, ← Ideal.span_singleton_pow,
      ← pow_mul, ramifiedIndex_add_one he n]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hi]
  exact Ideal.mem_map_of_mem _ hx

/-- The ramified quotient map `O_E/ϖ_E^(n+1) → O_F/ϖ_F^(e(n+1))` induced by `ι`.
Source: Bhatt--Scholze, Lemma 6.8.2(1). -/
noncomputable def ramifiedCoefficientQuotient {e : ℕ} (he : 1 ≤ e)
    (hideal : Ideal.span ({(integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E))} :
        Set (Padic.coefficientExtensionIntegers l F)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e}) (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l F (RamifiedPullback.index e n + 1) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E (n + 1))
    ((Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l F (RamifiedPullback.index e n + 1))).comp
      (integralScalarIntegerInclusion l E F ι))
    (ramifiedCoefficientQuotient_kernel l E F ι he hideal n)

/-- The completed coefficient inclusion reduces to the ramified quotient map.
Source: Bhatt--Scholze, Lemma 6.8.2(1). -/
theorem completedCoefficientMap_ramifiedProjection {e : ℕ} (he : 1 ≤ e)
    (hideal : Ideal.span ({(integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E))} :
        Set (Padic.coefficientExtensionIntegers l F)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e}) (n : ℕ) :
    completedCoefficientMap l E F ι W ≫
        completedIntegralCommRingProjectionUnrestricted l F W (RamifiedPullback.index e n) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫
        RamifiedPullback.ramifiedMap l E F W e n
          (ramifiedCoefficientQuotient l E F ι he hideal n) :=
  RamifiedPullback.ramified_projection l E F ι e he
    (ramifiedCoefficientQuotient l E F ι he hideal) (fun _ _ ↦ rfl) W n

/-- The completed coefficient projections are surjective on sections.
Source: Stacks Project, Tag 093M. -/
theorem completedIntegralProjection_surjective (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U) :=
  AlgebraicGeometry.ProEtale.projection_surjective l E W _
    (AlgebraicGeometry.ProEtale.uniformizer_normalized l E W n) U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed ramified coefficient square is a pushout on every section ring:
`R_F(U) ⊗_{R_E(U)} A_E(U) = A_F(U)`. Source: Stacks Project, Tag 093M;
Bhatt--Scholze, Lemma 6.8.2(1). -/
theorem completedRamifiedSquare_isPushout {e : ℕ} (he : 1 ≤ e)
    (hideal : Ideal.span ({(integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E))} :
        Set (Padic.coefficientExtensionIntegers l F)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e}) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    IsPushout ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U)
      ((completedCoefficientMap l E F ι W).hom.app U)
      ((RamifiedPullback.ramifiedMap l E F W e n
        (ramifiedCoefficientQuotient l E F ι he hideal n)).hom.app U)
      ((completedIntegralCommRingProjectionUnrestricted l F W
        (RamifiedPullback.index e n)).hom.app U) := by
  let c := completedCoefficientMap l E F ι W
  have hker : RingHom.ker
        ((completedIntegralCommRingProjectionUnrestricted l F W
          (RamifiedPullback.index e n)).hom.app U).hom =
      Ideal.map (c.hom.app U).hom
        (RingHom.ker
          ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom) := by
    rw [AlgebraicGeometry.ProEtale.uniformizer_kernel,
      AlgebraicGeometry.ProEtale.uniformizer_kernel]
    change Ideal.span {(scalarValue l F W U
        (Padic.coefficientExtensionUniformizer l F) ^ (RamifiedPullback.index e n + 1))} =
      Ideal.map (c.hom.app U).hom (Ideal.span {(scalarValue l E W U
        (Padic.coefficientExtensionUniformizer l E) ^ (n + 1))})
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    have hc := scalarValue_map l E W F ι U (Padic.coefficientExtensionUniformizer l E)
    change (c.hom.app U).hom _ = _ at hc
    erw [hc]
    have hh := congrArg (fun I ↦ Ideal.map (scalarValue l F W U) (I ^ (n + 1))) hideal
    simp only [Ideal.map_span, Set.image_singleton, map_pow,
      Ideal.span_singleton_pow, ← pow_mul, ramifiedIndex_add_one he n] at hh ⊢
    convert! hh.symm using 1
  exact (CommRingCat.isPushout_of_map_ker_eq_ker _ _ _ _
    (congrArg (fun φ ↦ φ.hom.app U)
      (completedCoefficientMap_ramifiedProjection l E F ι W he hideal n))
    (completedIntegralProjection_surjective l E W n U)
    (completedIntegralProjection_surjective l F W _ U) hker.symm).flip

end RamifiedSquare

section ReductionBaseChange

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The small pro-étale site is essentially small in the coefficient universe. -/
private theorem proEtSite_essentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] proEtSite_essentiallySmall
attribute [-instance] integralCoefficientAbSheafify integralCoefficientAbLocallyBijective

/-- Abelian sheafification on the small pro-étale site, in the coefficient universe. -/
private noncomputable instance (priority := high) proEtSite_hasSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

/-- Local bijectivity description on the small pro-étale site. -/
private noncomputable instance (priority := high) proEtSite_locallyBijective
    (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

variable {e : ℕ} (he : 1 ≤ e)
  (hideal : Ideal.span ({(integralScalarIntegerInclusion l E F ι
    (Padic.coefficientExtensionUniformizer l E))} :
      Set (Padic.coefficientExtensionIntegers l F)) =
    Ideal.span {Padic.coefficientExtensionUniformizer l F ^ e}) (n : ℕ)

/-- The ordinary reduction functor is change of rings along the finite projection on objects.
Source: Stacks Project, Tag 03EK. -/
theorem scalarReductionExtension_obj_eq (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W n).obj M =
      SheafOfModules.changeOfRings (completedIntegralCommRingProjectionUnrestricted l E W n) M :=
  (scalarReductionExistence l E W n).choose_spec.choose M

/-- The ordinary reduction functor is change of rings along the finite projection on maps.
Source: Stacks Project, Tag 03EK. -/
theorem scalarReductionExtension_map_eq {M N : scalarReductionSource l E W} (φ : M ⟶ N) :
    (scalarReductionExtension l E W n).map φ =
      eqToHom (scalarReductionExtension_obj_eq l E W n M) ≫
        SheafOfModules.changeOfRingsHom (completedIntegralCommRingProjectionUnrestricted l E W n)
          M φ ≫ eqToHom (scalarReductionExtension_obj_eq l E W n N).symm :=
  (scalarReductionExistence l E W n).choose_spec.choose_spec.choose φ

/-- Restriction of scalars along the ramified finite coefficient map
`A_{E,n} → A_{F,e(n+1)-1}`. Source: Stacks Project, Tag 03CZ. -/
noncomputable abbrev ramifiedReductionRestriction :
    scalarReductionTarget l F W (RamifiedPullback.index e n) ⥤ scalarReductionTarget l E W n :=
  SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (RamifiedPullback.ramifiedMap l E F W e n
        (ramifiedCoefficientQuotient l E F ι he hideal n)))

/-- The component of the reduction base-change isomorphism at one module.
Source: Stacks Project, Tag 03EK; Bhatt--Scholze, Lemma 6.8.2(1). -/
noncomputable def scalarReductionRestrictionBaseChangeApp (M : scalarReductionSource l F W) :
    (scalarReductionExtension l E W n).obj ((rationalScalarModuleRestriction l E F ι W).obj M) ≅
      (ramifiedReductionRestriction l E F ι W he hideal n).obj
        ((scalarReductionExtension l F W (RamifiedPullback.index e n)).obj M) :=
  eqToIso (scalarReductionExtension_obj_eq l E W n _) ≪≫
    SheafOfModules.changeOfRingsBaseChangeIso _ _ _ _
      (completedRamifiedSquare_isPushout l E F ι W he hideal n) M ≪≫
    (ramifiedReductionRestriction l E F ι W he hideal n).mapIso
      (eqToIso (scalarReductionExtension_obj_eq l F W (RamifiedPullback.index e n) M)).symm

/-- The reduction base-change component, unfolded into its three factors. -/
theorem scalarReductionRestrictionBaseChangeApp_hom (M : scalarReductionSource l F W) :
    (scalarReductionRestrictionBaseChangeApp l E F ι W he hideal n M).hom =
      eqToHom (scalarReductionExtension_obj_eq l E W n _) ≫
        (SheafOfModules.changeOfRingsBaseChangeIso _ _ _ _
          (completedRamifiedSquare_isPushout l E F ι W he hideal n) M).hom ≫
        (ramifiedReductionRestriction l E F ι W he hideal n).map
          (eqToHom (scalarReductionExtension_obj_eq l F W (RamifiedPullback.index e n) M).symm) :=
  rfl

/-- Naturality of the reduction base-change components. -/
theorem scalarReductionRestrictionBaseChangeApp_naturality
    {M N : scalarReductionSource l F W} (φ : M ⟶ N) :
    (scalarReductionExtension l E W n).map ((rationalScalarModuleRestriction l E F ι W).map φ) ≫
        (scalarReductionRestrictionBaseChangeApp l E F ι W he hideal n N).hom =
      (scalarReductionRestrictionBaseChangeApp l E F ι W he hideal n M).hom ≫
        (ramifiedReductionRestriction l E F ι W he hideal n).map
          ((scalarReductionExtension l F W (RamifiedPullback.index e n)).map φ) := by
  rw [scalarReductionExtension_map_eq, scalarReductionExtension_map_eq,
    scalarReductionRestrictionBaseChangeApp_hom, scalarReductionRestrictionBaseChangeApp_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.map_comp, eqToHom_map]
  have : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    proEtSite_locallyBijective W
  have : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := proEtSite_hasSheafify W
  have key := (SheafOfModules.changeOfRingsBaseChangeIso_hom_naturality.{u + 1, u, u + 1}
    (completedIntegralCommRingProjectionUnrestricted l E W n) (completedCoefficientMap l E F ι W)
    (RamifiedPullback.ramifiedMap l E F W e n (ramifiedCoefficientQuotient l E F ι he hideal n))
    (completedIntegralCommRingProjectionUnrestricted l F W (RamifiedPullback.index e n))
    (completedRamifiedSquare_isPushout l E F ι W he hideal n) φ)
  erw [reassoc_of% key]

/-- The completed coefficient ring sheaf `R_E` is flat as a module over itself.
Source: Stacks Project, Tag 06YQ. -/
theorem completedIntegralUnit_isFlatOnSite :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let A := SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let U : A := SheafOfModules.unit _
  have hlim : PreservesFiniteLimits (MonoidalCategory.tensorRight U) :=
    preservesFiniteLimits_of_natIso (MonoidalCategory.rightUnitorNatIso A).symm
  have hcol : PreservesFiniteColimits (MonoidalCategory.tensorRight U) :=
    preservesFiniteColimits_of_natIso (MonoidalCategory.rightUnitorNatIso A).symm
  exact ⟨preservesFiniteLimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R U).symm,
    preservesFiniteColimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R U).symm⟩

/-- A finite nonempty product of copies of `R_E` is flat over `R_E`. -/
theorem completedIntegralUnitPi_isFlatOnSite (d : ℕ) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (∏ᶜ fun _ : Fin (d + 1) ↦
        SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let U := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
  induction d with
  | zero =>
    exact SheafOfModules.flatOnSite_of_iso R (Limits.productUniqueIso (fun _ : Fin 1 ↦ U)).symm
      (completedIntegralUnit_isFlatOnSite l E W)
  | succ d ih =>
    let f : Fin (d + 2) → _ := fun _ ↦ U
    let e : (∏ᶜ f) ≅ U ⨯ ∏ᶜ (fun _ : Fin (d + 1) ↦ U) :=
      (limit.isLimit (Discrete.functor f)).conePointUniqueUpToIso
        (extendFanIsLimit f (limit.isLimit _) (prodIsProd _ _))
    exact SheafOfModules.flatOnSite_of_iso R (e ≪≫ (biprod.isoProd _ _).symm).symm
      (SheafOfModules.flatOnSite_biprod R _ _ (completedIntegralUnit_isFlatOnSite l E W) ih)

/-- The completed coefficient sheaf `R_F` is flat as an `R_E`-module, being finite free.
Source: Bhatt--Scholze, Lemma 6.8.2(1). -/
theorem completedCoefficientRestrictionUnit_isFlatOnSite :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      ((SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedCoefficientMap l E F ι W))).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l F W))) := by
  obtain ⟨b⟩ := (finiteFreeCompletedScalarComparison l E F ι W).1
  have hpos : completedScalarRelativeDegree l E F ι ≠ 0 := by
    let := ι.toAlgebra
    have : IsScalarTower ℚ_[l] E F :=
      IsScalarTower.of_algebraMap_eq (fun x ↦ (ι.commutes x).symm)
    have : FiniteDimensional E F := FiniteDimensional.right ℚ_[l] E F
    exact Module.finrank_pos.ne'
  generalize completedScalarRelativeDegree l E F ι = d at b hpos
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  exact SheafOfModules.flatOnSite_of_iso _ b.symm (completedIntegralUnitPi_isFlatOnSite l E W d)

/-- Restriction along the ramified finite map preserves finite limits. -/
instance ramifiedReductionRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (ramifiedReductionRestriction l E F ι W he hideal n) :=
  pbcRestrict_limits _

/-- Restriction along the ramified finite map preserves finite colimits. -/
instance ramifiedReductionRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (ramifiedReductionRestriction l E F ι W he hideal n) :=
  pbcRestrict_colimits _

/-- Restriction along the ramified finite map is additive. -/
instance ramifiedReductionRestriction_additive :
    (ramifiedReductionRestriction l E F ι W he hideal n).Additive :=
  pbcRestrict_additive _

/-- Restriction of scalars is faithful. -/
instance ramifiedReductionRestriction_faithful :
    (ramifiedReductionRestriction l E F ι W he hideal n).Faithful where
  map_injective {M N f g} h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

/-- The reduction base-change isomorphism on a complex. -/
noncomputable def scalarReductionRestrictionComplexIso
    (P : CochainComplex (scalarReductionSource l F W) ℤ) :
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
        (((rationalScalarModuleRestriction l E F ι W).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((ramifiedReductionRestriction l E F ι W he hideal n).mapHomologicalComplex (.up ℤ)).obj
        (((scalarReductionExtension l F W (RamifiedPullback.index e n)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ scalarReductionRestrictionBaseChangeApp l E F ι W he hideal n (P.X i))
    (fun i j _ ↦ (scalarReductionRestrictionBaseChangeApp_naturality l E F ι W he hideal n
      (P.d i j)).symm)

/-- Derived reduction of a K-flat complex is computed termwise.
Source: Stacks Project, Tag 06YY. -/
noncomputable def scalarReductionDerivedExtensionKFlatIso (k : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P) :
    (scalarReductionDerivedExtension l E W k).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W k).mapHomologicalComplex (.up ℤ)).obj P) :=
  haveI : IsIso ((scalarReductionCounit l E W k).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    unrestrictedTowerCounit_isIso l E W k P hP
  (scalarReductionDerivedExtension l E W k).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((scalarReductionCounit l E W k).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso
      (((scalarReductionExtension l E W k).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E W k)).app
      (((scalarReductionExtension l E W k).mapHomologicalComplex (.up ℤ)).obj P)

/-- Derived reduction modulo `ϖ_E^(n+1)` of the derived restriction is the restriction of the
derived reduction modulo `ϖ_F^(e(n+1))`. Source: Stacks Project, Tag 06YY;
Bhatt--Scholze, Lemma 6.8.2(1). -/
theorem nonempty_scalarReductionDerivedRestrictionIso
    (X : DerivedCategory (scalarReductionSource l F W)) :
    Nonempty ((scalarReductionDerivedExtension l E W n).obj
        ((rationalScalarDerivedRestriction l E F ι W).obj X) ≅
      (ramifiedReductionRestriction l E F ι W he hideal n).mapDerivedCategory.obj
        ((scalarReductionDerivedExtension l F W (RamifiedPullback.index e n)).obj X)) := by
  obtain ⟨P, s, hP, -, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l F W)
      (DerivedCategory.Q.objPreimage X)
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).mpr hs
  let := (rationalScalarModuleRestriction_exact l E F ι W).1
  let := (rationalScalarModuleRestriction_exact l E F ι W).2
  let eX : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have hRP := (SheafOfModules.isKFlat_restrictScalars_of_flat (completedCoefficientMap l E F ι W)
    (completedCoefficientRestrictionUnit_isFlatOnSite l E F ι W) P hP).1
  exact ⟨(scalarReductionDerivedExtension l E W n).mapIso
      ((rationalScalarDerivedRestriction l E F ι W).mapIso eX.symm) ≪≫
    (scalarReductionDerivedExtension l E W n).mapIso
      ((rationalScalarModuleRestriction l E F ι W).mapDerivedCategoryFactors.app P) ≪≫
    scalarReductionDerivedExtensionKFlatIso l E W n _ hRP ≪≫
    DerivedCategory.Q.mapIso (scalarReductionRestrictionComplexIso l E F ι W he hideal n P) ≪≫
    ((ramifiedReductionRestriction l E F ι W he hideal n).mapDerivedCategoryFactors.app _).symm ≪≫
    (ramifiedReductionRestriction l E F ι W he hideal n).mapDerivedCategory.mapIso
      ((scalarReductionDerivedExtensionKFlatIso l F W _ P hP).symm ≪≫
        (scalarReductionDerivedExtension l F W (RamifiedPullback.index e n)).mapIso eX)⟩

/-- The ramified finite restriction is restriction along the constant-sheaf map of the
ramified quotient map. -/
theorem ramifiedReductionRestriction_eq :
    ramifiedReductionRestriction l E F ι W he hideal n =
      pbcRestrict ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1}
          (ramifiedCoefficientQuotient l E F ι he hideal n)))) := by
  unfold ramifiedReductionRestriction RamifiedPullback.ramifiedMap RamifiedPullback.constantMap
  congr 4

/-- Constructibility and cohomological bounds of a finite `F`-reduction pass to its
restriction along the ramified finite coefficient map.
Source: Stacks Project, Tags 093I, 09AJ and 03DA. -/
theorem intrinsicFiniteTorsionConstructible_of_iso_ramifiedRestriction {a b : ℤ}
    (Z : DerivedCategory (scalarReductionTarget l F W (RamifiedPullback.index e n)))
    (Y : DerivedCategory (scalarReductionTarget l E W n))
    (eY : Y ≅ (ramifiedReductionRestriction l E F ι W he hideal n).mapDerivedCategory.obj Z)
    (hZ : intrinsicFiniteTorsionConstructible l F (RamifiedPullback.index e n + 1)
      (Nat.succ_pos _) W Z)
    (hS : proEtaleCohomologicalSupport Z ⊆ Set.Icc a b) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W Y ∧
      proEtaleCohomologicalSupport Y ⊆ Set.Icc a b := by
  let R := ramifiedReductionRestriction l E F ι W he hideal n
  have hzero (i : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj Y) ↔
        IsZero ((DerivedCategory.homologyFunctor _ i).obj Z) :=
    ⟨fun h ↦ R.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eY.symm)),
      fun h ↦ (R.isZero_homologyFunctor_mapDerivedCategory_obj h).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso eY)⟩
  have hsupp : proEtaleCohomologicalSupport Y = proEtaleCohomologicalSupport Z :=
    Set.ext fun i ↦ not_congr (hzero i)
  have := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have := Padic.finite_coefficientExtensionRing l F (RamifiedPullback.index e n + 1)
    (Nat.succ_pos _)
  refine ⟨⟨hZ.1.subset fun i hi h ↦ hi ((hzero i).mpr h), fun i ↦ ?_⟩, hsupp ▸ hS⟩
  have h := isConstructibleProEtaleModuleSheaf_restrictScalars W
    (ramifiedCoefficientQuotient l E F ι he hideal n) _ (hZ.2 i)
  let e : (DerivedCategory.homologyFunctor _ i).obj Y ≅
      R.obj ((DerivedCategory.homologyFunctor _ i).obj Z) :=
    (DerivedCategory.homologyFunctor _ i).mapIso eY ≪≫
      ((R.mapDerivedCategoryHomologyFunctorIso i).app Z).symm
  rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
  rw [← ramifiedReductionRestriction_eq] at h
  exact ProEtale.isConstructible_of_iso
    ((proEtaleModuleRestriction W (Padic.coefficientExtensionRing l E (n + 1))).mapIso e.symm) h
end ReductionBaseChange

/-- Restricted reductions remain intrinsically constructible in one common interval.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
Proof: use the finite quotient square induced by the completed coefficient map and
exactness of scalar restriction to identify homology of every E-reduction with a
restricted F-reduction. Reuse the F object's finite stratifications and degree
interval. Restriction of each finite constant local model remains finite over the
source quotient ring, and the sheafification comparison is sectionwise. Taking
the interval supplied by `K.property` gives the common bounds for all levels.
No Noetherian hypothesis on `W` is used.
(blueprint: lem-sf-rational-scalar-restriction-reduction-constructible) -/
theorem rationalScalarDerivedRestriction_reduction_constructible
    (K : sfIntegralConstructibleCategory l F W) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
          ((scalarReductionDerivedExtension l E W n).obj
            ((rationalScalarDerivedRestriction l E F ι W).obj K.obj)) ∧
      proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E W n).obj
            ((rationalScalarDerivedRestriction l E F ι W).obj K.obj)) ⊆ Set.Icc a b := by
  obtain ⟨e, he, hideal⟩ := exists_coefficientRamification l E F ι
  obtain ⟨a, b, hab, hK⟩ := K.property.2
  refine ⟨a, b, hab, fun n ↦ ?_⟩
  obtain ⟨hc, hs⟩ := hK (RamifiedPullback.index e n)
  obtain ⟨iso⟩ := nonempty_scalarReductionDerivedRestrictionIso l E F ι W he hideal n K.obj
  exact intrinsicFiniteTorsionConstructible_of_iso_ramifiedRestriction l E F ι W he hideal n _ _
    iso hc hs

end WeilConjectures
