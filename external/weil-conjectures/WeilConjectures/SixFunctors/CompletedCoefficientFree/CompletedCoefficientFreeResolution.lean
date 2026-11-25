/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.Completed.CompletedFreeCellOrdinaryLimit
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
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
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!+# Free resolutions over completed integral coefficient sheaves

Source: Stacks Project, proetale.tex, Tag 09C3, and algebraization.tex, Tag 099I;
sites-modules.tex, Tags 093J and 093M; sites-cohomology.tex, Tags 06YQ and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution).

The index `n` denotes the positive exponent `n + 1`. All coefficients and maps are
the published constant quotient sheaves, their inverse limit and their projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxErrors 8
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits

namespace WeilConjectures.CompletedCoefficientFree

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The free rank-one complex in degree zero over the existing completion.
Source: Stacks Tag 09C3 (blueprint: lem-sf-completed-coefficient-free-resolution). -/
abbrev freeUnitComplex : CochainComplex (scalarReductionSource l E T) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))

/-- Multiplication by the positive uniformizer power on the degree-zero free complex.
Source: Stacks Tags 093M and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
def uniformizerPower (n : ℕ) : freeUnitComplex l E T ⟶ freeUnitComplex l E T :=
  (integralScalarChainAction l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app (freeUnitComplex l E T)

/-- The actual two-term free complex `[B --varpi^(n+1)--> B]` in degrees `-1,0`.
Source: Stacks Tags 093M and 06YM
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
def quotientResolution (n : ℕ) : CochainComplex (scalarReductionSource l E T) ℤ :=
  CochainComplex.mappingCone (uniformizerPower l E T n)

/-- The finite coefficient ring as a module over the completion via its projection.
Source: Stacks Tags 093M and 03CZ
(blueprint: lem-sf-completed-coefficient-free-resolution). -/
abbrev residueModule (n : ℕ) : scalarReductionSource l E T :=
  (scalarReductionRestriction l E T n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T n))

/-- The actual quotient projection `B -> R_(n+1)`, as the unit-module map taking
`1` to `1`; the action on the target is restricted along the limit projection.
Source: Stacks Tag 093M (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def quotientProjection (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) ⟶
      residueModule l E T n :=
  (residueModule l E T n).unitHomEquiv.symm
    ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _))

/-- A finite free cell, with rank zero allowed, in an arbitrary integer degree.
Finite products here are the canonical finite direct sums in the abelian module category.
Source: Stacks Tag 09C3 (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def freeCell (r : ℕ) (d : ℤ) : CochainComplex (scalarReductionSource l E T) ℤ :=
  (CochainComplex.singleFunctor _ d).obj
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))

/-- The canonical reduction of every unbounded derived object. The normalized derived
adjunction fixes this unit on K-flat representatives by `x -> 1 tensor x`; thus the
choice of witness does not introduce an arbitrary arrow.
Source: Stacks Tag 06YY (blueprint: lem-sf-completed-coefficient-free-resolution). -/
def reductionMap (n : ℕ) (M : DerivedCategory (scalarReductionSource l E T)) :
    M ⟶ (scalarReductionDerivedRestriction l E T n).obj
      ((scalarReductionDerivedExtension l E T n).obj M) :=
  (derivedScalarExtensionRestrictionAdjunction l E T n).choose.unit.app M

private abbrev coefficientMultiplication (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) ⟶
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) :=
  (uniformizerPower l E T n).f 0

private theorem coefficientMultiplication_apply (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    (coefficientMultiplication l E T n).val.app U x =
      integralScalarConstant l E T U
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) * x := by
  exact (integralScalarChainAction_existsUnique l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).exists.choose_spec
      (freeUnitComplex l E T) 0 U x

private theorem coefficientMultiplication_one (n : ℕ) (U : T.ProEtᵒᵖ) :
    (coefficientMultiplication l E T n).val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) =
      integralScalarConstant l E T U
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) := by
  rw [coefficientMultiplication_apply, mul_one]

private theorem uniformizerPower_eq (n : ℕ) :
    uniformizerPower l E T n =
      (CochainComplex.singleFunctor _ 0).map (coefficientMultiplication l E T n) := by
  apply HomologicalComplex.from_single_hom_ext
  rfl

private theorem quotientProjection_apply (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    (quotientProjection l E T n).val.app U x =
      (limit.π (integralCoefficientSheafSystem l E T) (Opposite.op n)).hom.app U x := by
  have h := congrArg (fun s ↦ s.val U)
    ((residueModule l E T n).unitHomEquiv.apply_symm_apply
      ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _)))
  change (quotientProjection l E T n).val.app U
    (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) =
      (1 : (integralCoefficientSheaf l E T n).obj.obj U) at h
  let x₁ : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U := 1
  let y₁ : (integralCoefficientSheaf l E T n).obj.obj U :=
    (quotientProjection l E T n).val.app U x₁
  have hx := ((quotientProjection l E T n).val.app U).hom.map_smul x x₁
  change (quotientProjection l E T n).val.app U (x * x₁) =
    @id ((integralCoefficientSheaf l E T n).obj.obj U)
      ((limit.π (integralCoefficientSheafSystem l E T) (Opposite.op n)).hom.app U x) * y₁ at hx
  change y₁ = 1 at h
  simpa only [x₁, mul_one, h, id_eq] using hx

private theorem scalarConstant_eq (U : T.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarConstant l E T U a =
      (integralConstantToCompletionOfUniverses l E T).hom.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up a)) := by
  apply (integralScalarConstant_existsUnique l E T U a).unique
    (integralScalarConstant_existsUnique l E T U a).exists.choose_spec
  intro n
  have hc := congrArg (fun h ↦ h.hom.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up a)))
    (limit.lift_π (integralConstantConeOfUniverses l E T) (Opposite.op n))
  refine hc.trans ?_
  let q := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact (congrArg (fun h ↦ (h.app U).hom (ULift.up a))
    (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map q))).symm

private theorem scalarConstant_pow (U : T.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) (m : ℕ) :
    integralScalarConstant l E T U (a ^ m) = (integralScalarConstant l E T U a) ^ m := by
  rw [scalarConstant_eq, scalarConstant_eq]
  let f : ULift.{t + 1} (Padic.coefficientExtensionIntegers l E) →+*
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U :=
    ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom.comp
      (((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom)
  change f ((ULift.up a) ^ m) = f (ULift.up a) ^ m
  exact map_pow f _ _

private theorem coefficientMultiplication_regular (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Injective ((coefficientMultiplication l E T n).val.app U) := by
  intro x y hxy
  apply AlgebraicGeometry.ProEtale.completedIntegralScalar_regular l E T (n + 1) U
  rw [coefficientMultiplication_apply, coefficientMultiplication_apply,
    scalarConstant_pow, scalarConstant_eq] at hxy
  exact hxy

private theorem coefficient_zero (n : ℕ) :
    coefficientMultiplication l E T n ≫ quotientProjection l E T n = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (quotientProjection l E T n).val.app U
    ((coefficientMultiplication l E T n).val.app U x) = 0
  rw [quotientProjection_apply, coefficientMultiplication_apply, map_mul]
  have h := (integralScalarConstant_existsUnique l E T U
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).exists.choose_spec n
  erw [h]
  have hz : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
  have hz' : integralScalarFiniteConstant l E T n U
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
    unfold integralScalarFiniteConstant
    rw [hz]
    exact map_zero _
  rw [hz', zero_mul]

private theorem sheaf_shortExact_of_app
    {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    [HasSheafify J AddCommGrpCat.{w}]
    (h : ∀ U, ((S.map (sheafToPresheaf J _)).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)).ShortExact) :
    S.ShortExact := by
  let F := sheafToPresheaf J AddCommGrpCat.{w}
  let K := S.map F
  have he : K.Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).2
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext U
    have hz := (ShortComplex.exact_iff_isZero_homology _).1 (h U).exact
    have hz' : IsZero (K.homology.obj U) :=
      hz.of_iso (K.mapHomologyIso ((evaluation Cᵒᵖ _).obj U)).symm
    exact hz'.eq_of_src _ _
  have : Mono K.f := (NatTrans.mono_iff_mono_app _).2 (fun U ↦ (h U).mono_f)
  have : Epi K.g := (NatTrans.epi_iff_epi_app _).2 (fun U ↦ (h U).epi_g)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F ⟨he⟩

private theorem coefficient_shortExact (n : ℕ) :
    (ShortComplex.mk (coefficientMultiplication l E T n) (quotientProjection l E T n)
      (coefficient_zero l E T n)).ShortExact := by
  let F := SheafOfModules.toSheaf.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E T)
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful F
  apply sheaf_shortExact_of_app.{t + 1, t, max u (t + 1)}
    (AlgebraicGeometry.Scheme.ProEt.topology T)
  intro U
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ab_exact_iff _).2
    intro x hx
    change (quotientProjection l E T n).val.app U x = 0 at hx
    rw [quotientProjection_apply] at hx
    obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.completedIntegralProjection_divisible
      l E T n U x hx
    refine ⟨y, ?_⟩
    change (coefficientMultiplication l E T n).val.app U y = x
    rw [coefficientMultiplication_apply, scalarConstant_pow, scalarConstant_eq]
    exact hy.symm
  · exact (AddCommGrpCat.mono_iff_injective _).2
      (coefficientMultiplication_regular l E T n U)
  · apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E T n U x
    refine ⟨(integralConstantToCompletionOfUniverses l E T).hom.app U y, ?_⟩
    change (quotientProjection l E T n).val.app U _ = x
    rw [quotientProjection_apply]
    exact (congrArg (fun h ↦ h.hom.app U y)
      (limit.lift_π (integralConstantConeOfUniverses l E T) (Opposite.op n))).trans hy

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

private theorem quotientResolution_augmentation (n : ℕ) :
    ∃ ε : quotientResolution l E T n ⟶
        (CochainComplex.singleFunctor _ 0).obj (residueModule l E T n),
      QuasiIso ε ∧ CochainComplex.mappingCone.inr (uniformizerPower l E T n) ≫ ε =
        (CochainComplex.singleFunctor _ 0).map (quotientProjection l E T n) := by
  let A := SheafOfModules.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E T)
  let F := HomologicalComplex.single A (.up ℤ) 0
  have ha : uniformizerPower l E T n = F.map (coefficientMultiplication l E T n) := by
    exact uniformizerPower_eq l E T n
  have hz : uniformizerPower l E T n ≫ F.map (quotientProjection l E T n) = 0 := by
    rw [ha, ← F.map_comp, coefficient_zero, F.map_zero]
  let S := ShortComplex.mk (uniformizerPower l E T n)
    (F.map (quotientProjection l E T n)) hz
  have hS : S.ShortExact := by
    have h := (coefficient_shortExact l E T n).map_of_exact F
    simpa only [S, ha, ShortComplex.map, freeUnitComplex, F, A,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors] using h
  exact ⟨CochainComplex.mappingCone.descShortComplex S,
    CochainComplex.mappingCone.quasiIso_descShortComplex hS,
    CochainComplex.mappingCone.inr_descShortComplex S⟩

section ReductionTensorInstances

local instance (priority := high + 1) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify T

namespace ReductionTensor
open SheafOfModules MonoidalCategory
open scoped ChangeOfRings
variable {C : Type (t + 1)} [Category.{t} C]
private abbrev forgetRing (J : GrothendieckTopology C) :
    Sheaf J CommRingCat.{max u (t + 1)} ⥤ Sheaf J RingCat.{max u (t + 1)} where
  obj R := ⟨R.obj ⋙ forget₂ CommRingCat RingCat,
    GrothendieckTopology.HasSheafCompose.isSheaf _ R.property⟩
  map f := ⟨CategoryTheory.Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)⟩
variable (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{max u (t + 1)})
  {S : Sheaf J CommRingCat.{max u (t + 1)}} (φ : R ⟶ S)
  [HasSheafify J AddCommGrpCat.{max u (t + 1)}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]

private noncomputable def tensorUnitPresheafIso
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    siteTensorPresheaf (unit ((forgetRing J).obj R)).val M.val ≅ M.val := by
  refine PresheafOfModules.isoMk (fun V ↦
    (TensorProduct.lid (R.obj.obj V) (M.val.obj V)).toModuleIso) ?_
  intro V W f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a x
  change (R.obj.map f (show R.obj.obj V from a)) • (show M.val.obj W from M.val.map f x) =
    M.val.map f ((show R.obj.obj V from a) • x)
  exact ((M.val.map f).hom.map_smul a x).symm

private abbrev sheafifyR :=
  PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)

private noncomputable def tensorR
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R) ⥤
      SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R) where
  obj N := (sheafifyR J R).obj (siteTensorPresheaf N.val M.val)
  map f := (sheafifyR J R).map (siteTensorHom f.val M.val)
  map_id N := by
    change (sheafifyR J R).map (siteTensorHom (𝟙 N.val) M.val) = _
    rw [siteTensorHom_id]
    exact (sheafifyR J R).map_id _
  map_comp f g := by
    change (sheafifyR J R).map (siteTensorHom (f.val ≫ g.val) M.val) = _
    rw [siteTensorHom_comp, Functor.map_comp]

private theorem tensorR_eq
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    tensorR J R M = siteSheafTensorRight (A := R) M := rfl

private theorem sheafificationCounit_isIso
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((forgetRing J).obj R).obj)).counit.app M) := by
  infer_instance

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def tensorUnitIso
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    (tensorR J R M).obj (unit ((forgetRing J).obj R)) ≅ M := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)
  let e : (sheafifyR J R).obj M.val ≅ M :=
    @asIso _ _ _ _ (adj.counit.app M) (sheafificationCounit_isIso J R M)
  let f := (sheafifyR J R).mapIso (tensorUnitPresheafIso J R M)
  change (sheafifyR J R).obj (siteTensorPresheaf (unit ((forgetRing J).obj R)).val M.val) ≅ M
  exact f ≪≫ e

attribute [local semireducible] PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification

private noncomputable def restrictedSheafification
    (P : _root_.PresheafOfModules.{max u (t + 1)} ((forgetRing J).obj S).obj) :
    (PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 ((forgetRing J).obj R).obj)).obj
      ((PresheafOfModules.restrictScalars.{max u (t + 1)} ((forgetRing J).map φ).hom).obj P) ⟶
      (restrictScalars.{max u (t + 1)} ((forgetRing J).map φ)).obj
        ((PresheafOfModules.sheafification.{max u (t + 1)}
          (𝟙 ((forgetRing J).obj S).obj)).obj P) := by
  refine (PresheafOfModules.sheafificationHomEquiv.{max u (t + 1)}
    (P := (PresheafOfModules.restrictScalars.{max u (t + 1)} ((forgetRing J).map φ).hom).obj P)
    (F := (restrictScalars.{max u (t + 1)} ((forgetRing J).map φ)).obj
      ((PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 ((forgetRing J).obj S).obj)).obj P))
    (𝟙 ((forgetRing J).obj R).obj)).symm ?_
  exact (PresheafOfModules.restrictScalars.{max u (t + 1)} ((forgetRing J).map φ).hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj S).obj)).unit.app P)

attribute [local irreducible] restrictedSheafification

private theorem restrictedSheafification_underlying
    (P : _root_.PresheafOfModules.{max u (t + 1)} ((forgetRing J).obj S).obj) :
    IsIso ((toSheaf ((forgetRing J).obj R)).map (restrictedSheafification J R φ P)) := by
  rw [restrictedSheafification,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  let adj := CategoryTheory.sheafificationAdjunction
    J AddCommGrpCat.{max u (t + 1)}
  change IsIso ((adj.homEquiv P.presheaf
    ((presheafToSheaf J AddCommGrpCat.{max u (t + 1)}).obj P.presheaf)).symm
      (adj.unit.app P.presheaf))
  have hh := adj.homEquiv_symm_unit P.presheaf
  exact hh.symm ▸ IsIso.id _

private theorem restrictedSheafification_isIso
    (P : _root_.PresheafOfModules.{max u (t + 1)} ((forgetRing J).obj S).obj) :
    IsIso (restrictedSheafification J R φ P) := by
  have : IsIso ((toSheaf ((forgetRing J).obj R)).map (restrictedSheafification J R φ P)) :=
    restrictedSheafification_underlying J R φ P
  exact isIso_of_reflects_iso _ (toSheaf ((forgetRing J).obj R))

private noncomputable def tensorQuotientPresheafIso
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    siteTensorPresheaf (R := R.obj)
        ((restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj
          S))).val M.val ≅
      (PresheafOfModules.restrictScalars ((forgetRing J).map φ).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · exact (LinearEquiv.refl (R.obj.obj V)
      (TensorProduct (R.obj.obj V)
        ((ModuleCat.restrictScalars (φ.hom.app V).hom).obj
          (ModuleCat.of (S.obj.obj V) (S.obj.obj V))) (M.val.obj V))).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b x
    exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) b x).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def tensorQuotientIso
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    (tensorR J R M).obj
        ((restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj S))) ≅
      (restrictScalars ((forgetRing J).map φ)).obj
        (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M) := by
  exact (sheafifyR J R).mapIso
      (tensorQuotientPresheafIso J R φ M) ≪≫
    @asIso _ _ _ _ (restrictedSheafification J R φ
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M))
      (restrictedSheafification_isIso J R φ _)

attribute [local irreducible] tensorUnitIso tensorQuotientPresheafIso tensorQuotientIso

private theorem tensorUnitIso_unit
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) (V : Cᵒᵖ) (x : M.val.obj V) :
    (tensorUnitIso J R M).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)).unit.app
        (siteTensorPresheaf (unit ((forgetRing J).obj R)).val M.val)).app V
          ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) = x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)
  let f := (tensorUnitPresheafIso J R M).hom
  have hn := adj.unit.naturality f
  have ht := adj.right_triangle_components M
  have hn' := congrArg (fun g ↦ g.app V
    ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
  have ht' := congrArg (fun g ↦ g.app V x) ht
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn' ht'
  change (tensorUnitIso J R M).hom.val.app V _ = _
  simp only [tensorUnitIso, id_eq, sheafifyR, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [← hn']
  have hf : f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) = x := by
    change (1 : R.obj.obj V) • x = x
    exact one_smul _ _
  change (adj.counit.app M).val.app V ((adj.unit.app M.val).app V
    (f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))) = x
  rw [hf]
  exact ht'

private theorem tensorUnitIso_inv_apply
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) (V : Cᵒᵖ) (x : M.val.obj V) :
    (tensorUnitIso J R M).inv.val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)).unit.app
        (siteTensorPresheaf (unit ((forgetRing J).obj R)).val M.val)).app V
          ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  apply_fun (tensorUnitIso J R M).hom.val.app V
  · have h := congrArg (fun g ↦ g.val.app V x) (tensorUnitIso J R M).inv_hom_id
    exact h.trans (tensorUnitIso_unit J R M V x).symm
  · intro a b hab
    have h := congrArg ((tensorUnitIso J R M).inv.val.app V) hab
    have hc := congrArg (fun g ↦ g.val.app V) (tensorUnitIso J R M).hom_inv_id
    have ha := ConcreteCategory.congr_hom hc a
    have hb := ConcreteCategory.congr_hom hc b
    exact ha.symm.trans (h.trans hb)

private theorem restrictedSheafification_unit
    (P : _root_.PresheafOfModules.{max u (t + 1)} ((forgetRing J).obj S).obj) (V : Cᵒᵖ) (x :
      P.obj V) :
    (restrictedSheafification J R φ P).val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)).unit.app
        ((PresheafOfModules.restrictScalars ((forgetRing J).map φ).hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj S).obj)).unit.app
        P).app V x := by
  unfold restrictedSheafification
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars ((forgetRing J).map φ).hom).obj P)
    (F := (restrictScalars ((forgetRing J).map φ)).obj
      ((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj S).obj)).obj P))
    (𝟙 ((forgetRing J).obj R).obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars ((forgetRing J).map φ).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj S).obj)).unit.app P))
  have hh := congrArg (fun g ↦ g.app V x) h
  exact hh

variable
  (p : unit ((forgetRing J).obj R) ⟶
    (restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj S)))
  (f : unit ((forgetRing J).obj R) ⟶ unit ((forgetRing J).obj R))

private noncomputable def quotientMorphism
    (p : unit ((forgetRing J).obj R) ⟶
      (restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj S)))
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) :
    M ⟶ (restrictScalars ((forgetRing J).map φ)).obj
      (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M) :=
  (tensorUnitIso J R M).inv ≫ (tensorR J R M).map
    p ≫ (tensorQuotientIso J R φ M).hom

private theorem sheafification_map_unit
    {P Q : _root_.PresheafOfModules.{max u (t + 1)} ((forgetRing J).obj R).obj}
    (f : P ⟶ Q) (V : Cᵒᵖ) (x : P.obj V) :
    ((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map f).val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)).unit.app
        P).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)).unit.app
        Q).app V (f.app V x) := by
  exact (congrArg (fun g ↦ g.app V x)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((forgetRing J).obj R).obj)).unit.naturality f)).symm

private theorem quotientMorphism_apply
    (p : unit ((forgetRing J).obj R) ⟶
      (restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj S)))
    (hp : ∀ V : Cᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) (V : Cᵒᵖ) (x : M.val.obj V) :
    (quotientMorphism J R φ (p := p) M).val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)
  let g := siteTensorHom p.val M.val
  let k := (tensorQuotientPresheafIso J R φ M).hom
  have hg : g.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) =
      ((show ((restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj
        S))).val.obj V from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x) := by
    change (p.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x = _
    rw [hp V]
  have hk : k.app V
      ((show ((restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj
        S))).val.obj V from (1 : S.obj.obj V)) ⊗ₜ[R.obj.obj V] x) =
      (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x := by
    dsimp only [k]
    unfold tensorQuotientPresheafIso
    rfl
  simp only [quotientMorphism, tensorQuotientIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hinv := tensorUnitIso_inv_apply J R M V x
  have hi := congrArg (fun y ↦ (restrictedSheafification J R φ
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).val.app V
    (((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map k).val.app V
      (((tensorR J R M).map p).val.app V y))) hinv
  refine hi.trans ?_
  change (restrictedSheafification J R φ
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).val.app V
    (((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map k).val.app V
      (((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map g).val.app V
        ((adj.unit.app _).app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)))) = _
  let σ := (restrictedSheafification J R φ
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).val.app V
  have h₁ := sheafification_map_unit J R g V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)
  have h₂ := sheafification_map_unit J R k V (g.app V
    ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))
  have h₃ := congrArg (fun y ↦ σ
    (((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map k).val.app V y)) h₁
  refine h₃.trans ((congrArg σ h₂).trans ?_)
  have hkg := (congrArg (k.app V) hg).trans hk
  exact (congrArg (fun y ↦ σ ((adj.unit.app _).app V y)) hkg).trans
    (restrictedSheafification_unit J R φ _ V _)

private noncomputable def tensorMultiplication
    (f : unit ((forgetRing J).obj R) ⟶ unit ((forgetRing J).obj R))
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) : M ⟶ M :=
  (tensorUnitIso J R M).inv ≫ (tensorR J R M).map
    f ≫ (tensorUnitIso J R M).hom

private theorem tensorMultiplication_apply
    (f : unit ((forgetRing J).obj R) ⟶ unit ((forgetRing J).obj R))
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R)) (V : Cᵒᵖ) (x : M.val.obj V) :
    (tensorMultiplication J R f M).val.app V x =
      (show R.obj.obj V from f.val.app V (1 : R.obj.obj V)) • x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj R).obj)
  let g := siteTensorHom f.val M.val
  simp only [tensorMultiplication, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have hinv := tensorUnitIso_inv_apply J R M V x
  have hi := congrArg (fun y ↦ (tensorUnitIso J R M).hom.val.app V
    (((tensorR J R M).map f).val.app V y)) hinv
  refine hi.trans ?_
  change (tensorUnitIso J R M).hom.val.app V
    (((PresheafOfModules.sheafification (𝟙 ((forgetRing J).obj R).obj)).map g).val.app V
      ((adj.unit.app _).app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))) = _
  have ht : g.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) =
      (1 : R.obj.obj V) ⊗ₜ[R.obj.obj V]
        ((show R.obj.obj V from f.val.app V (1 : R.obj.obj V)) • x) := by
    change (f.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x = _
    have hh := TensorProduct.smul_tmul (R := R.obj.obj V) (R' := R.obj.obj V)
      (f.val.app V (1 : R.obj.obj V)) (1 : R.obj.obj V) x
    simpa only [smul_eq_mul, mul_one] using hh
  have h := sheafification_map_unit J R g V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)
  refine (congrArg ((tensorUnitIso J R M).hom.val.app V) h).trans ?_
  exact (congrArg (fun y ↦ (tensorUnitIso J R M).hom.val.app V
    ((adj.unit.app _).app V y)) ht).trans (tensorUnitIso_unit J R M V _)

private theorem quotientUnit
    (p : unit ((forgetRing J).obj R) ⟶
      (restrictScalars ((forgetRing J).map φ)).obj (unit ((forgetRing J).obj S)))
    (hp : ∀ V : Cᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (M : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj R))
    (N : SheafOfModules.{max u (t + 1)} ((forgetRing J).obj S))
    (he : N = SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M)
    (η : M ⟶ (restrictScalars ((forgetRing J).map φ)).obj N)
    (hη : ∀ (V : Cᵒᵖ) (x : M.val.obj V), η.val.app V x =
      ((restrictScalars ((forgetRing J).map φ)).map (eqToHom he.symm)).val.app V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((forgetRing J).obj S).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).app V
            ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app V).hom).unit.app
              (M.val.obj V) x))) :
    quotientMorphism J R φ p M ≫
      (restrictScalars ((forgetRing J).map φ)).map (eqToHom he.symm) = η := by
  cases he
  simp only [eqToHom_refl, ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at hη ⊢
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (quotientMorphism_apply J R φ p hp M V x).trans (hη V x).symm

end ReductionTensor

attribute [local irreducible] ReductionTensor.tensorR
  PresheafOfModules.sheafificationAdjunction PresheafOfModules.sheafification
  ModuleCat.extendRestrictScalarsAdj

local instance : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
local instance : PreservesFilteredColimitsOfSize.{t + 1, t + 1}
    (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
  preservesFilteredColimitsOfSize_shrink _

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def ordinaryQuotientIso (n : ℕ) (M : scalarReductionSource l E T) :
    (ReductionTensor.tensorR (AlgebraicGeometry.Scheme.ProEt.topology T)
      (completedIntegralCommRingSheafUnrestricted l E T) M).obj
        (residueModule l E T n) ≅
      (scalarReductionRestriction l E T n).obj ((scalarReductionExtension l E T n).obj M) :=
  ReductionTensor.tensorQuotientIso
      (AlgebraicGeometry.Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
      (completedIntegralCommRingProjectionUnrestricted l E T n) M ≪≫
    (scalarReductionRestriction l E T n).mapIso
      (eqToIso ((scalarReductionExistence l E T n).choose_spec.choose M)).symm

attribute [local irreducible] ordinaryQuotientIso

private theorem ordinaryQuotient_unit (n : ℕ) (M : scalarReductionSource l E T) :
    (ReductionTensor.tensorUnitIso
      (AlgebraicGeometry.Scheme.ProEt.topology T)
      (completedIntegralCommRingSheafUnrestricted l E T) M).inv ≫
        (ReductionTensor.tensorR (AlgebraicGeometry.Scheme.ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) M).map
          (quotientProjection l E T n) ≫ (ordinaryQuotientIso l E T n M).hom =
      (scalarReductionExtension_adjunction l E T n).choose.unit.app M := by
  have hp (U : T.ProEtᵒᵖ) : (quotientProjection l E T n).val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) =
        (1 : (integralCoefficientSheaf l E T n).obj.obj U) := by
    have h := congrArg (fun s ↦ s.val U)
      ((residueModule l E T n).unitHomEquiv.apply_symm_apply
        ((SheafOfModules.unit (integralCoefficientSheaf l E T n)).unitHomEquiv (𝟙 _)))
    exact h
  have h := ReductionTensor.quotientUnit
    (AlgebraicGeometry.Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (quotientProjection l E T n) hp M ((scalarReductionExtension l E T n).obj M)
    ((scalarReductionExistence l E T n).choose_spec.choose M)
    ((scalarReductionExtension_adjunction l E T n).choose.unit.app M)
    (by
      intro V x
      exact (scalarReductionExtension_adjunction l E T n).choose_spec M V x)
  simp only [ReductionTensor.quotientMorphism, Category.assoc] at h
  simp only [ordinaryQuotientIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, eqToIso.inv]
  convert h using 1 <;> rfl

private theorem scalar_flat_sequence (n : ℕ) (M : scalarReductionSource l E T)
    (hM : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology T)
      (R := completedIntegralCommRingSheafUnrestricted l E T) M) :
    ∃ hz : (((integralScalarChainAction l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app
          ((CochainComplex.singleFunctor _ 0).obj M)).f 0) ≫
        (scalarReductionExtension_adjunction l E T n).choose.unit.app M = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let F : scalarReductionSource l E T ⥤ scalarReductionSource l E T :=
    ReductionTensor.tensorR (AlgebraicGeometry.Scheme.ProEt.topology T) R M
  have hMF : CategoryTheory.exactFunctor _ _ F := by
    simpa only [F, ReductionTensor.tensorR_eq, SheafOfModules.IsFlatOnSite] using hM
  let := (exactFunctor_iff F).mp hMF |>.1
  let := (exactFunctor_iff F).mp hMF |>.2
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let e : F.obj (SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E T)) ≅ M :=
    ReductionTensor.tensorUnitIso
      (AlgebraicGeometry.Scheme.ProEt.topology T) R M
  let eR : F.obj (residueModule l E T n) ≅
      (scalarReductionRestriction l E T n).obj ((scalarReductionExtension l E T n).obj M) :=
    ordinaryQuotientIso l E T n M
  let a : M ⟶ M := (((integralScalarChainAction l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app
      ((CochainComplex.singleFunctor _ 0).obj M)).f 0)
  let η : M ⟶ (scalarReductionRestriction l E T n).obj
      ((scalarReductionExtension l E T n).obj M) :=
    (scalarReductionExtension_adjunction l E T n).choose.unit.app M
  have ha : a = e.inv ≫ F.map (coefficientMultiplication l E T n) ≫ e.hom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a.val.app U x) =
      (ReductionTensor.tensorMultiplication
        (AlgebraicGeometry.Scheme.ProEt.topology T) R
        (coefficientMultiplication l E T n) M).val.app U x
    have hact := (integralScalarChainAction_existsUnique l E T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).exists.choose_spec
      ((CochainComplex.singleFunctor _ 0).obj M) 0 U x
    have hone := coefficientMultiplication_one l E T n U
    have htensor := ReductionTensor.tensorMultiplication_apply
      (AlgebraicGeometry.Scheme.ProEt.topology T) R
      (coefficientMultiplication l E T n) M U x
    exact hact.trans ((congrArg (fun b : R.obj.obj U ↦ b • x) hone).symm.trans htensor.symm)
  have hη : η = e.inv ≫ F.map (quotientProjection l E T n) ≫ eR.hom :=
    (ordinaryQuotient_unit l E T n M).symm
  have hz : a ≫ η = 0 := by
    calc
      a ≫ η = e.inv ≫ F.map
          (coefficientMultiplication l E T n ≫ quotientProjection l E T n) ≫ eR.hom := by
        rw [ha, hη]
        simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
      _ = 0 := by
        have hzero := congrArg (fun f ↦ F.map f) (coefficient_zero l E T n)
        exact (congrArg (fun f ↦ e.inv ≫ f ≫ eR.hom) hzero).trans (by
          simp only [Functor.map_zero, zero_comp, comp_zero])
  let S := ShortComplex.mk (coefficientMultiplication l E T n)
    (quotientProjection l E T n) (coefficient_zero l E T n)
  let i : S.map F ≅ ShortComplex.mk a η hz :=
    ShortComplex.isoMk e e eR
      (by
        change e.hom ≫ a = F.map (coefficientMultiplication l E T n) ≫ e.hom
        rw [ha]
        simp only [Iso.hom_inv_id_assoc])
      (by
        change e.hom ≫ η = F.map (quotientProjection l E T n) ≫ eR.hom
        rw [hη]
        simp only [Iso.hom_inv_id_assoc])
  exact ⟨hz, ShortComplex.shortExact_of_iso i ((coefficient_shortExact l E T n).map_of_exact F)⟩

attribute [local semireducible] PresheafOfModules.sheafificationAdjunction
  PresheafOfModules.sheafification ModuleCat.extendRestrictScalarsAdj

end ReductionTensorInstances

private theorem quotientResolution_kflat (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T)
      (quotientResolution l E T n) := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let A := scalarReductionSource l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.tensorPreadditive R
  have hunit : ObjectProperty.flat (show A from SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E T)) := by
    exact ObjectProperty.prop_unit ObjectProperty.flat
  have hs (i : ℤ) : ObjectProperty.flat ((freeUnitComplex l E T).X i) := by
    by_cases hi : i = 0
    · subst i
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm hunit
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
  have hb : (quotientResolution l E T n).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff _ _).2
    exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ (i + 1) (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i (by omega)⟩
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (R := R) _ 0
  intro i
  have hf : ObjectProperty.flat ((quotientResolution l E T n).X i) := by
    apply ObjectProperty.prop_of_iso _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (uniformizerPower l E T n) i (i + 1) rfl).symm
    apply ObjectProperty.prop_of_iso _ (biprod.isoProd _ _).symm
    exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair _ _))
      (by rintro ⟨_ | _⟩ <;> exact hs _)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

private def reductionComplexCounit (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (scalarReductionDerivedExtension l E T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarReductionDerivedExtension l E T n).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (scalarReductionCounit l E T n).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension l E T n).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj P)

private theorem reductionComplexCounit_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P) :
    IsIso (reductionComplexCounit l E T n P) := by
  have := (scalarReductionDerivedExistence l E T n).choose_spec.choose_spec.2.2 P hP
  dsimp only [reductionComplexCounit, scalarReductionCounit]
  infer_instance

private theorem normalizedUnit_complex
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (d : LD ⊣ R.mapDerivedCategory) (P : CochainComplex A ℤ)
    (hp : d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((L.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) =
        DerivedCategory.Qh.map
          ((adj.mapHomotopyCategory (.up ℤ)).unit.app
            ((HomotopyCategory.quotient _ _).obj P))) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map
        (LD.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
          DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
  change d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj P)) = _ at hp
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hp
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, Functor.map_id,
    Category.id_comp, Category.comp_id] at hp ⊢
  erw [LD.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id] at hp
  erw [Category.comp_id]
  erw [Category.id_comp] at hp
  exact hp

private theorem reductionMap_complex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P) :
    reductionMap l E T n (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedRestriction l E T n).map (reductionComplexCounit l E T n P) ≫
        (scalarReductionRestriction l E T n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (scalarReductionExtension_adjunction l E T n).choose.unit (.up ℤ)).app P) := by
  exact normalizedUnit_complex (scalarReductionExtension l E T n)
    (scalarReductionRestriction l E T n)
    (scalarReductionExtension_adjunction l E T n).choose
    (scalarReductionDerivedExtension l E T n) (scalarReductionCounit l E T n)
    (derivedScalarExtensionRestrictionAdjunction l E T n).choose P
    ((derivedScalarExtensionRestrictionAdjunction l E T n).choose_spec P hP)

private theorem scalarChainAction_degree (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) (i : ℤ) :
    ((integralScalarChainAction l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app P).f i =
      ((integralScalarChainAction l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app
          ((CochainComplex.singleFunctor _ 0).obj (P.X i))).f 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ((integralScalarChainAction_existsUnique l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).exists.choose_spec P i U x).trans
      ((integralScalarChainAction_existsUnique l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).exists.choose_spec
          ((CochainComplex.singleFunctor _ 0).obj (P.X i)) 0 U x).symm

private theorem scalarDerivedAction_Q (a : Padic.coefficientExtensionIntegers l E)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (integralScalarDerivedAction l E T a).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((integralScalarChainAction l E T a).app P) := by
  exact WeilConjectures.integralScalarDerivedAction_app_Q l E T a P

private theorem reductionTriangle_model (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) P)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology T)
      (R := completedIntegralCommRingSheafUnrestricted l E T) (P.X i)) :
    ∃ δ : (scalarReductionDerivedRestriction l E T n).obj
        ((scalarReductionDerivedExtension l E T n).obj (DerivedCategory.Q.obj P)) ⟶
          (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧,
      Triangle.mk
        ((integralScalarDerivedAction l E T
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app (DerivedCategory.Q.obj P))
        (reductionMap l E T n (DerivedCategory.Q.obj P)) δ ∈ distTriang _ := by
  let a := (integralScalarChainAction l E T
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app P
  let η := (NatTrans.mapHomologicalComplex
    (scalarReductionExtension_adjunction l E T n).choose.unit (.up ℤ)).app P
  have hz : a ≫ η = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change a.f i ≫ (scalarReductionExtension_adjunction l E T n).choose.unit.app (P.X i) = 0
    exact (congrArg (fun f ↦ f ≫
      (scalarReductionExtension_adjunction l E T n).choose.unit.app (P.X i))
        (scalarChainAction_degree l E T n P i)).trans
      (scalar_flat_sequence l E T n (P.X i) (hflat i)).choose
  have hs : (ShortComplex.mk a η hz).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    change (ShortComplex.mk (a.f i)
      ((scalarReductionExtension_adjunction l E T n).choose.unit.app (P.X i)) _).ShortExact
    let S := ShortComplex.mk _ _
      (scalar_flat_sequence l E T n (P.X i) (hflat i)).choose
    let e : S ≅ ShortComplex.mk (a.f i)
        ((scalarReductionExtension_adjunction l E T n).choose.unit.app (P.X i))
        (congrArg (fun f ↦ f.f i) hz) :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
          scalarChainAction_degree l E T n P i)
        (by simp only [S, Iso.refl_hom,
          Category.id_comp, Category.comp_id])
    exact ShortComplex.shortExact_of_iso e
      (scalar_flat_sequence l E T n (P.X i) (hflat i)).choose_spec
  have := reductionComplexCounit_isIso l E T n P hP
  let e := (scalarReductionDerivedRestriction l E T n).mapIso
      (asIso (reductionComplexCounit l E T n P)) ≪≫
    (scalarReductionRestriction l E T n).mapDerivedCategoryFactors.app
      (((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj P)
  let δ := e.hom ≫ DerivedCategory.triangleOfSESδ hs
  refine ⟨δ, isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hs) _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change ((integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app
        (DerivedCategory.Q.obj P)) ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map a
    simpa only [Category.id_comp, Category.comp_id] using
      scalarDerivedAction_Q l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) P
  · change reductionMap l E T n (DerivedCategory.Q.obj P) ≫ e.hom =
      𝟙 _ ≫ DerivedCategory.Q.map η
    simpa only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      Iso.app_hom, Category.id_comp] using reductionMap_complex l E T n P hP
  · simp [δ]

private theorem reductionTriangle (n : ℕ) (M : DerivedCategory (scalarReductionSource l E T)) :
    ∃ δ : (scalarReductionDerivedRestriction l E T n).obj
        ((scalarReductionDerivedExtension l E T n).obj M) ⟶ M⟦(1 : ℤ)⟧,
      Triangle.mk
        ((integralScalarDerivedAction l E T
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app M)
        (reductionMap l E T n M) δ ∈ distTriang _ := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) (DerivedCategory.Q.objPreimage M)
  let := hq
  let e : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology T)
      (R := completedIntegralCommRingSheafUnrestricted l E T) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E T) _).symm (hflat i)
  obtain ⟨δ, hδ⟩ := reductionTriangle_model l E T n P hP hsite
  let F := scalarReductionDerivedExtension l E T n ⋙ scalarReductionDerivedRestriction l E T n
  let eR := F.mapIso e
  refine ⟨eR.inv ≫ δ ≫ e.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hδ _ ?_⟩
  refine Triangle.isoMk _ _ e.symm e.symm eR.symm ?_ ?_ ?_
  · exact ((integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).naturality e.inv).symm
  · exact ((derivedScalarExtensionRestrictionAdjunction l E T n).choose.unit.naturality
      e.inv).symm
  · simp

private theorem complexTower_roos
    (T₀ : AlgebraicGeometry.Scheme.{t})
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E T₀) ℤ)
    (ht : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i))
    (c : Cone T) (hc : IsLimit c) :
    HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))],
      ∃ δ, IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op))
        (DerivedCategory.Q.obj c.pt)
        (Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (op n)))) δ := by
  classical
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T₀)
      AddCommGrpCat.{max u (t + 1)} := integralOperationsAbSheafify.{t, u} T₀
  let : (AlgebraicGeometry.Scheme.ProEt.topology T₀).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralOperationsAbLocallyBijective.{t, u} T₀
  let K := fun n : ℕ ↦ T.obj (op n)
  let B : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hB : IsLimit B := productIsProduct K
  let shift : B.pt ⟶ B.pt := towerProductShift
    (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hshift (n : ℕ) : shift ≫ B.proj n =
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := Pi.lift_comp_π _ _
  let S := ShortComplex.mk _ _
    (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hB shift hshift c)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hB shift hshift hc
  have hepi (i : ℤ) : Epi ((𝟙 B.pt - shift).f i) := by
    let F := fun n : ℕ ↦ (T.obj (op n)).X i
    let f := fun n : ℕ ↦ (T.map (homOfLE n.le_succ).op).f i
    obtain ⟨_, _, hEpi, _⟩ :=
      AlgebraicGeometry.ProEtale.proEtale_surjectiveTower_derivedLimit T₀
        (completedIntegralCommRingSheafUnrestricted l E T₀) F f (fun n ↦ ht n i)
    let hBi := isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hB
    let e : B.pt.X i ≅ ∏ᶜ F := hBi.conePointUniqueUpToIso (productIsProduct F)
    have he (n : ℕ) : e.hom ≫ Pi.π F n = (B.proj n).f i :=
      hBi.conePointUniqueUpToIso_hom_comp (productIsProduct F) ⟨n⟩
    have hconj : (𝟙 B.pt - shift).f i =
        e.hom ≫ towerTransitionEndomorphism f ≫ e.inv := by
      apply (cancel_mono e.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π,
        HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      have hn := congrArg (fun q ↦ q.f i) (hshift n)
      simpa only [HomologicalComplex.comp_f, Category.assoc, reassoc_of% he, f] using
        congrArg (fun q ↦ (B.proj n).f i - q) hn
    rw [hconj]
    infer_instance
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ hepi
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  have := AlgebraicGeometry.ProEtale.exact_countable_products T₀
    (completedIntegralCommRingSheafUnrestricted l E T₀)
  obtain ⟨hD, hQ, _⟩ := derivedCategory_countableProducts_core.{0}
    (scalarReductionSource l E T₀)
  have hQB : IsLimit (DerivedCategory.Q.mapCone B) := (hQ ℕ K).some
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K B) hQB
  refine ⟨inferInstance, ?_⟩
  intro hprod
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op)
  let p : DerivedCategory.Q.obj c.pt ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (op n)))
  let E : DerivedCategory.Q.obj B.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (B.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n =
      DerivedCategory.Q.map (c.π.app (op n)) := Pi.lift_comp_π _ _
  have hi : DerivedCategory.Q.map S.f ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hπ]
    exact congrArg DerivedCategory.Q.map (hB.fac _ ⟨n⟩)
  have hu (n : ℕ) : S.g ≫ B.proj n = B.proj n -
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := by
    change (𝟙 B.pt - shift) ≫ B.proj n = _
    rw [Preadditive.sub_comp, Category.id_comp, hshift]
  have htrans : DerivedCategory.Q.map S.g ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hu, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  let δ := DerivedCategory.triangleOfSESδ hS
  refine ⟨E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) htrans (by simp))).mp
    (DerivedCategory.triangleOfSES_distinguished hS)

private theorem freeCell_good (r : ℕ) (d : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E T) (freeCell l E T r d) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := AlgebraicGeometry.Scheme.ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted l E T) ((freeCell l E T r d).X i) := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let A := scalarReductionSource l E T
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.tensorPreadditive R
  have hunit : ObjectProperty.flat (show A from SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted l E T)) :=
    ObjectProperty.prop_unit ObjectProperty.flat
  have hfree : ObjectProperty.flat (show A from ∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) :=
    ObjectProperty.prop_of_isLimit _ (productIsProduct _) (fun _ ↦ hunit)
  have hs (i : ℤ) : ObjectProperty.flat ((freeCell l E T r d).X i) := by
    by_cases hi : i = d
    · subst i
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXSelf (.up ℤ) d _).symm hfree
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) d _ i hi)
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology T) (R := R)
      ((freeCell l E T r d).X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm (hs i).2
  have : (freeCell l E T r d).IsStrictlyLE d :=
    inferInstanceAs (((CochainComplex.singleFunctor A d).obj _).IsStrictlyLE d)
  exact ⟨SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (R := R) _ d hsite, hsite⟩

private def auxiliaryDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard

private theorem freeCell_complete (r : ℕ) (d : ℤ) :
    IntegralOnSlice.IsComplete l E T none (DerivedCategory.Q.obj (freeCell l E T r d)) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let D := auxiliaryDatum p hp
  have hl : l ≠ D.p := by change l ≠ p; omega
  let P := freeCell l E T r d
  have hP := (freeCell_good l E T r d).1
  have hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheaf l E T D hl) (𝟙 P) := ⟨inferInstance, hP⟩
  obtain ⟨hc, ht⟩ := completedFreeCell_ordinaryLimit l E T D hl r d
  let F := Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P)
    (integralTowerTransition l E T D hl P)
  let c := completedFreeCellCone l E T D hl P
  have hct : IsLimit c := hc.some
  obtain ⟨hprod, hroos⟩ := complexTower_roos l E T F
    (fun n i ↦ by simpa only [F, Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_obj, P, freeCell, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors] using ht n i) c hct
  let := hprod
  obtain ⟨δ, hδ⟩ := hroos
  refine ⟨D, hl, P, P, 𝟙 P, hq, Iso.refl _, hprod, δ, ?_⟩
  have hleg (n : ℕ) :
      ((integralReductionTowerCone l E T D hl (𝟙 P) hq).extend
        (Iso.refl (DerivedCategory.Q.obj P)).inv).π.app (op n) =
        DerivedCategory.Q.map (integralTowerUnit l E T D hl P n) := by
    change 𝟙 _ ≫ inv (DerivedCategory.Q.map (𝟙 P)) ≫
      DerivedCategory.Q.map (integralTowerUnit l E T D hl P n) = _
    simp only [DerivedCategory.Q.map_id, IsIso.inv_id, Category.id_comp]
  simp only [IsDerivedLimitTriangle, integralReductionTower, c, completedFreeCellCone,
    F, Functor.ofOpSequence_map_homOfLE_succ,
    NatTrans.ofOpSequence_app, hleg] at hδ ⊢
  exact hδ

/-- The free quotient resolution is K-flat and its canonical augmentation is a
quasi-isomorphism; every finite free cell is complete through the actual quotient
projections; and canonical reduction of every unbounded derived object is the cone
of its uniformizer power.

Source: Stacks Project, proetale.tex Tag 09C3, algebraization.tex Tag 099I,
sites-modules.tex Tags 093J/093M, sites-cohomology.tex Tags 06YQ/06YM;
Bhatt--Scholze, Propositions 3.1.9--3.1.10
(blueprint: lem-sf-completed-coefficient-free-resolution).

Proof:
1. Sectionwise regularity of the completed scalar and divisibility of the kernel of
   each completion projection give the actual coefficient short exact sequence.
   Its image under the single-complex functor has the canonical cone augmentation;
   the standard mapping-cone short-exact-sequence theorem makes it a quasi-isomorphism.
2. The unit sheaf is flat over itself. Finite products and the two-term cone have
   flat terms and are bounded above, so the independent-coefficient bounded-flat
   criterion makes both the resolution and every free cell K-flat.
3. The ordinary finite-free quotient tower has the free cell as its limit, with
   its specified augmentation and epimorphic transitions in every degree. The
   pro-etale surjective-tower theorem makes one minus shift epimorphic on the
   complex product. Its kernel is the ordinary limit. The resulting short exact
   sequence, together with preservation of countable products by localization,
   gives the required derived-limit triangle with the original augmentation.
4. On a flat-term K-flat complex, tensor the coefficient short exact sequence
   degree by degree. Tensor-unit and scalar-extension comparisons identify its
   maps with scalar multiplication and the ordinary scalar-extension unit.
   Its derived short-exact-sequence triangle therefore computes reduction.
   The normalized derived adjunction identifies the second arrow with reductionMap.
   Finally take a flat-term K-flat resolution of any unbounded object and
   transport this triangle along its quasi-isomorphism. -/
theorem completed_coefficient_free_resolution :
    (∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E T)
        (quotientResolution l E T n) ∧
      ∃ ε : quotientResolution l E T n ⟶
          (CochainComplex.singleFunctor _ 0).obj (residueModule l E T n),
        QuasiIso ε ∧
          CochainComplex.mappingCone.inr (uniformizerPower l E T n) ≫ ε =
            (CochainComplex.singleFunctor _ 0).map (quotientProjection l E T n)) ∧
    (∀ (r : ℕ) (d : ℤ), IntegralOnSlice.IsComplete l E T none
      (DerivedCategory.Q.obj (freeCell l E T r d))) ∧
    ∀ (n : ℕ) (M : DerivedCategory (scalarReductionSource l E T)),
      ∃ δ : (scalarReductionDerivedRestriction l E T n).obj
          ((scalarReductionDerivedExtension l E T n).obj M) ⟶ M⟦(1 : ℤ)⟧,
        Triangle.mk
          ((integralScalarDerivedAction l E T
            (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app M)
          (reductionMap l E T n M) δ ∈ distTriang _ := by
  exact ⟨fun n ↦ ⟨quotientResolution_kflat l E T n,
    quotientResolution_augmentation l E T n⟩, freeCell_complete l E T,
    reductionTriangle l E T⟩

end WeilConjectures.CompletedCoefficientFree
