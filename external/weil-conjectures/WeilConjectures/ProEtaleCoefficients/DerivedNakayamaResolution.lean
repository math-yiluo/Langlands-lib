/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution

import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-!
# The two-term resolution of the finite coefficient sheaves

Source: blueprint main-20261015, chap-The-pro-etale-site,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-resolution.md`
(blueprint: lemma-reduction-derived-nakayama--1).

All coefficients are continuous condensed rings pulled back from the point. A natural
cone is expressed using the standard cone functor on complexes, with its standard maps.
The comparison with a functor on the derived category also asserts its descent and naturality.

## Main definitions

* `quotientModule`: the continuous finite quotient with its restricted integer action.
* `reductionFunctor`: derived tensor with the pulled-back quotient in degree zero.
* `coneFunctor`: the standard localized mapping-cone model and its maps.

## Main statements

* `derived_nakayama_resolution`: exactness, the natural cone comparison, and the
  specified quotient-power triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ScalarTools
universe v w
open Category BraidedCategory
namespace UnitScalar
variable (A : Type u) [Category.{v} A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
@[instance_reducible] private def scalarRing : CommRing (End (𝟙_ A)) :=
  { (inferInstance : Ring (End (𝟙_ A))) with
    mul_comm := fun a b ↦ by
      apply End.ext
      have h := unitEndAction_naturality a.asHom b
      simpa only [End.mul_asHom, unitEndAction_unit] using h }
-- A private copy fixes the scalar action on each Hom space.
private def Scalars := End (𝟙_ A)

private instance : CommRing (Scalars A) := scalarRing A
variable [BraidedCategory A]
end UnitScalar

namespace UnitScalar
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
end UnitScalar

end ScalarTools

section Sectionwise
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u + 1}]
private theorem shortExact_of_sectionwise
    (S : ShortComplex (Sheaf J Ab.{u + 1}))
    (hS : ∀ T : Cᵒᵖ,
      ((S.map (sheafToPresheaf J Ab)).map ((evaluation Cᵒᵖ Ab).obj T)).ShortExact) :
    S.ShortExact := by
  let F := sheafToPresheaf J Ab.{u + 1}
  have hk : IsLimit (KernelFork.ofι (S.map F).f (S.map F).zero) :=
    evaluationJointlyReflectsLimits _ fun T ↦
      by
        have := (hS T).mono_f
        exact (KernelFork.isLimitMapConeEquiv ..).2 (hS T).exact.fIsKernel
  have hk' : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects F ((KernelFork.isLimitMapConeEquiv ..).2 hk)
  have : Mono S.f := mono_of_isLimit_fork hk'
  have : ∀ T, Epi (((S.map F).g).app T) := fun T ↦ (hS T).epi_g
  have : Epi ((S.map F).g) := NatTrans.epi_of_epi_app _
  have hEpi : Epi (F.map S.g) := by
    change Epi ((S.map F).g)
    infer_instance
  have : Epi S.g := Functor.epi_of_epi_map F hEpi
  exact ⟨S.exact_of_f_is_kernel hk'⟩
end Sectionwise

section QuotientTools
universe v
open Category
namespace PowerQuotients
variable {C : Type u} [Category.{v} C] [Abelian C]
  {U : C} (d : End U) (B : ℕ → C) (r : ∀ n, U ⟶ B n)
  (hz : ∀ n, (d ^ n).asHom ≫ r n = 0)
  (hs : ∀ n, (ShortComplex.mk _ _ (hz n)).ShortExact)
end PowerQuotients

end QuotientTools

private theorem coefficientTopology :
    (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace =
      @UniformSpace.toTopologicalSpace E
        (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace := by
  have h : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  exact congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) h

theorem quotientDiscrete (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  cases n with
  | zero =>
    have : Subsingleton (Padic.coefficientExtensionRing l E 0) := by
      apply Ideal.Quotient.subsingleton_iff.mpr
      simp [Padic.coefficientExtensionIdeal]
    exact Subsingleton.discreteTopology
  | succ n =>
    have htop := coefficientTopology l E
    have hb : ∀ x : Padic.coefficientExtensionIntegers l E,
        (nhds x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
          {y | Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x}) := by
      have h := Padic.coefficientExtension_integers_coset_basis l E
      change ∀ x, Filter.HasBasis
        (@nhds _ (TopologicalSpace.induced Subtype.val
          (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace) x) _ _ at h
      rw [htop] at h
      exact h
    have hq : IsLocallyConstant
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro x
      exact (hb x).mem_of_mem (i := n) trivial
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isQuotientMap_quot_mk.isOpen_preimage]
    exact hq.isOpen_fiber _

private def uniformizerMap : integerRing l E ⟶ integerRing l E := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨{ app := fun S ↦ ?_, naturality := ?_ }⟩
  · exact AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up
          (ContinuousMap.const S.unop (Padic.coefficientExtensionUniformizer l E) * f.down)
        map_zero' := by apply ULift.ext; exact mul_zero _
        map_add' := by intro f g; apply ULift.ext; exact mul_add _ _ _ }
  · intro S T f
    rfl

private def uniformizerEnd : End (Mod.regular (integerRing l E)) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine .of (Mod.homMk (uniformizerMap l E) ?_)
  change MonObj.mul ≫ uniformizerMap l E =
    integerRing l E ◁ uniformizerMap l E ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Category.assoc, Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro f g
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change Padic.coefficientExtensionUniformizer l E * (f.down x * g.down x) =
    f.down x * (Padic.coefficientExtensionUniformizer l E * g.down x)
  ring

private def reductionHom (n : ℕ) :
    Mod.regular (integerRing l E) ⟶ quotientModule l E n :=
  Mod.homMk (reductionRing l E n) (by
    change MonObj.mul ≫ reductionRing l E n =
      integerRing l E ◁ reductionRing l E n ≫
        reductionRing l E n ▷ quotientRing l E n ≫ MonObj.mul
    simpa only [tensorHom_def', Category.assoc] using
      (IsMonHom.mul_hom (reductionRing l E n)))

private theorem uniformizerEnd_apply (S : Profinite.{u}ᵒᵖ)
    (f : (integerRing l E).obj.obj S) (x : S.unop) :
    (((uniformizerEnd l E).asHom.hom.hom.app S) f).down x =
      Padic.coefficientExtensionUniformizer l E * f.down x := by
  rfl

private theorem uniformizer_ne_zero : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro h0
  apply hm
  rw [← hgen, h0, Ideal.span_singleton_eq_bot]

private theorem uniformizerPower_apply (n : ℕ) (S : Profinite.{u}ᵒᵖ)
    (f : (integerRing l E).obj.obj S) (s : S.unop) :
    (((uniformizerEnd l E ^ n).asHom.hom.hom.app S) f).down s =
      Padic.coefficientExtensionUniformizer l E ^ n * f.down s := by
  induction n generalizing f with
  | zero =>
    change f.down s = _
    simp
  | succ n ih =>
    rw [pow_succ, End.mul_asHom]
    change (((uniformizerEnd l E ^ n).asHom.hom.hom.app S)
      (((uniformizerEnd l E).asHom.hom.hom.app S) f)).down s = _
    rw [ih, uniformizerEnd_apply, pow_succ, mul_assoc]

private theorem reduction_zero (n : ℕ) :
    (uniformizerEnd l E ^ n).asHom ≫ reductionHom l E n = 0 := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  ext f
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      ((((uniformizerEnd l E ^ n).asHom.hom.hom.app S) f).down s) = 0
  rw [uniformizerPower_apply, map_mul]
  have h : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E ^ n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [h, zero_mul]

private theorem pointResolution (n : ℕ) :
    (ShortComplex.mk (uniformizerEnd l E ^ n).asHom (reductionHom l E n)
      (reduction_zero l E n)).ShortExact := by
  let S := ShortComplex.mk (uniformizerEnd l E ^ n).asHom (reductionHom l E n)
    (reduction_zero l E n)
  have hs : (S.map (Mod.forget _)).ShortExact := by
    apply shortExact_of_sectionwise
    intro T
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let := quotientDiscrete l E n
    let S' := ((S.map (Mod.forget _)).map
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab)).map
        ((evaluation Profinite.{u}ᵒᵖ Ab).obj T)
    have hf : Function.Injective S'.f := by
      intro f g h
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      have h' := congrArg (fun f ↦ f.down t) h
      change (((uniformizerEnd l E ^ n).asHom.hom.hom.app T) f).down t =
        (((uniformizerEnd l E ^ n).asHom.hom.hom.app T) g).down t at h'
      rw [uniformizerPower_apply, uniformizerPower_apply] at h'
      exact mul_left_cancel₀ (pow_ne_zero n (uniformizer_ne_zero l E)) h'
    have hg : Function.Surjective S'.g := by
      intro f
      let lift : Padic.coefficientExtensionRing l E n →
          Padic.coefficientExtensionIntegers l E :=
        Function.surjInv Ideal.Quotient.mk_surjective
      refine ⟨ULift.up ⟨lift ∘ f.down, continuous_of_discreteTopology.comp f.down.continuous⟩, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
    have he : S'.Exact := by
      apply S'.ab_exact_iff.mpr
      intro f hf
      have hdiv : ∀ t : T.unop, (f.down t : E) ∈ Set.range
          (fun a : Padic.coefficientExtensionIntegers l E ↦
            (Padic.coefficientExtensionUniformizer l E : E) ^ n * (a : E)) := by
        intro t
        have hft := congrArg (fun f ↦ f.down t) hf
        change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n) (f.down t) = 0 at hft
        rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hft
        obtain ⟨a, ha⟩ := hft
        refine ⟨a, ?_⟩
        have ha' := congrArg
          (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) ha.symm
        simpa using ha'
      obtain ⟨g, hg, hgf, _⟩ := (Padic.continuous_uniformizer_division l E n).2
        f.down f.down.continuous hdiv
      refine ⟨ULift.up ⟨g, hg⟩, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      change (((uniformizerEnd l E ^ n).asHom.hom.hom.app T)
        (ULift.up (⟨g, hg⟩ : C(T.unop, Padic.coefficientExtensionIntegers l E)))).down t = _
      rw [uniformizerPower_apply]
      exact Subtype.ext (by simpa using hgf t)
    have : Mono S'.f := (AddCommGrpCat.mono_iff_injective _).mpr hf
    have : Epi S'.g := (AddCommGrpCat.epi_iff_surjective _).mpr hg
    exact ⟨he⟩
  have := hs.mono_f
  have := hs.epi_g
  have : Mono S.f := Functor.mono_of_mono_map (Mod.forget _) hs.mono_f
  have : Epi S.g := Functor.epi_of_epi_map (Mod.forget _) hs.epi_g
  exact ⟨(S.exact_map_iff_of_faithful (Mod.forget _)).mp hs.exact⟩

end AlgebraicGeometry.ProEtale.DerivedNakayama
