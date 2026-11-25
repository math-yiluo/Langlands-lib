/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
import WeilConjectures.SmoothPurity.Point.PointSectionsIntegralCohomologyControl
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.FlatScalarExtensionFiniteCohomology
import WeilConjectures.Algebra.Homology.Derived.DerivedCompleteModuleFinite
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedCompleteHomology
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Noetherian.Basic

/-! Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: lem-weil-point-sections-integral-finiteness). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Strictly separated integral and rational clauses from the point-sections finiteness assertion.
Proof: obtain bounded support, derived completeness and finite residue from the
cohomological-control lemma. The coefficient ring is a complete Noetherian DVR,
using finite_module_adic_complete_and_hom on the ring itself and transport through ULift.
Apply the derived-complete-module finiteness criterion to each cohomology module.
The uniformizer localization is flat; flat scalar extension commutes with homology
and carries each finite generating set to a finite spanning set over E.
Source: the landing assertion in the finite coefficient point construction;
(blueprint: lem-weil-point-sections-integral-finiteness).
-/
theorem point_sections_finiteness_integral (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ,
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFgComplete (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
          (DerivedCategory.Q.obj
            (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)) ∧
        DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (pointIntegralToField l E)).mapHomologicalComplex
              (.up ℤ)).obj
              (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)))) := by
  intro C hC
  let O := Padic.coefficientExtensionIntegers l E
  let R := ULift.{u + 1, u} O
  let J : Ideal O := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  let M := DerivedCategory.Q.obj
    (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)
  have hdvr := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  letI : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  letI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv O ULift.ringEquiv.symm
  have hO : Function.Bijective (AdicCompletion.of J O) :=
    ((Padic.finite_module_adic_complete_and_hom.{u, u, u} l E).1 O).2.1
  letI : IsAdicComplete J O := AdicCompletion.of_bijective_iff.mp hO
  have hR : IsAdicComplete I R := by
    have ht := (IsAdicComplete.congr_ringEquiv J
      (ULift.ringEquiv.symm : O ≃+* R)).mpr (inferInstance : IsAdicComplete J O)
    dsimp only [J] at ht
    rw [Ideal.map_span, Set.image_singleton] at ht
    convert! ht using 1
  have hcomplete : Function.Bijective (AdicCompletion.of I R) :=
    AdicCompletion.of_bijective_iff.mpr hR
  obtain ⟨hs, hc, hcoh⟩ := point_sections_integral_cohomology_control D l _hl E C hC
  have hfg : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M) := by
    intro i
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M
    letI : Finite (N ⧸ (I • ⊤ : Submodule R N)) := hcoh i
    exact (ModuleCat.finite_and_completion_bijective_of_isDerivedComplete I hcomplete
      N (DerivedCategory.isDerivedComplete_homology I M hc i)
      (inferInstance : Module.Finite (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N)))).1
  refine ⟨⟨hs, hfg, hc⟩, ?_⟩
  have hf : (pointIntegralToField l E).Flat := by
    letI := (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).1
    have ho : (O.subtype : O →+* E).Flat :=
      RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat E (Submonoid.powers (Padic.coefficientExtensionUniformizer l E)))
    change (RingHom.ulift O.subtype).Flat
    exact RingHom.Flat.ulift_iff.mpr ho
  exact DerivedCategory.pointFiniteDimensional_of_flat_scalar_extension
    (pointIntegralToField l E) hf
    (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C) hs hfg

end WeilConjectures
