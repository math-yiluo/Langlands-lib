/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerConstructible
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerVanishing

/-! # The residue layers of the target coefficient filtration

Source: Stacks, sites-modules, lemma-tensor-product-locally-constant;
proetale, lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layers).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The actual power ideals in the finite target ring, regarded as submodules.
Source: parent finite-level-bounds proof, explicit uniformizer devissage
(blueprint: lem-sf-integral-scalar-residue-layers). -/
def integralScalarPowerFiltration (n : ℕ) :
    Fin (n + 1 + 1) → Submodule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
  fun j ↦ (Ideal.span ({ULift.up ((Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L))} :
        Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^ (j : ℕ)

/-- Power ideals decrease with the exponent.
Source: parent finite-level-bounds proof, power ideal filtration
(blueprint: lem-sf-integral-scalar-residue-layers). -/
theorem integralScalarPowerFiltration_antitone (n : ℕ) :
    Antitone (integralScalarPowerFiltration l L n) := by
  intro i j hij
  exact Ideal.pow_le_pow_right hij

/-- The first power ideal is the whole coefficient module.
Source: parent finite-level-bounds proof, power ideal filtration
(blueprint: lem-sf-integral-scalar-residue-layers). -/
theorem integralScalarPowerFiltration_zero (n : ℕ) :
    integralScalarPowerFiltration l L n 0 = ⊤ := by
  simp [integralScalarPowerFiltration]

/-- The last power ideal vanishes in the defining quotient.
Source: parent finite-level-bounds proof, power ideal filtration
(blueprint: lem-sf-integral-scalar-residue-layers). -/
theorem integralScalarPowerFiltration_last (n : ℕ) :
    integralScalarPowerFiltration l L n (Fin.last (n + 1)) = ⊥ := by
  have hz : ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L)) ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  change ((Ideal.span ({ULift.up ((Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L))} :
        Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^
          (n + 1) : Ideal _) = ⊥
  rw [Ideal.span_singleton_pow]
  have hu : (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L)) :
        ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) ^ (n + 1) = 0 := by
    apply ULift.ext
    exact hz
  rw [hu, Ideal.span_singleton_zero]

/-- Each successive layer tensor has constructible cohomology in the residue interval.
Source: parent lem-sf-integral-scalar-finite-level-bounds, steps 1--2;
Stacks sites-modules, lemma-tensor-product-locally-constant, and proetale,
lemma-constructible-serre; finite residue-field specialization.
(blueprint: lem-sf-integral-scalar-residue-layers).
Proof: the chosen uniformizer generates the maximal ideal of the target DVR.
Multiplication by its j-th power identifies the quotient of its j-th and (j+1)-st
power ideals in A_(L,n+1) with k_L. To check the kernel, lift an equality to O_L
and cancel the nonzero uniformizer power; since j<n+1, the remainder is divisible
by the uniformizer. This includes j=n. The coefficient map to this quotient
factors through k_E, since the local field embedding maps the maximal ideal of
O_E into that of O_L. K-flat computation of the source derived reduction and
balanced tensor associativity identify each layer tensor with the extension of
that reduction from k_E to k_L, followed by restriction to A_(L,n+1).
Apply finiteFieldSheafScalarExtension: exactness commutes with homology, finite
models extend to finite models and the interval endpoints are unchanged.
Restriction from k_L to A_(L,n+1) keeps the same finite constant models and zero
objects. The finite-model and geometric-stalk constructibility predicates agree
by trivializing on each stratum. Derived homology agrees with homology of the
K-flat representative. These identifications prove both clauses at every degree.
At n=0 there is one layer, the residue field itself; zero inputs and the empty
scheme give the same comparisons and zero homology. No completeness is used. -/
theorem integralScalarResidueLayers_bounds
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r s : ℤ) (hrs : r ≤ s)
    (h₁ : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)))
    (hbound : ∀ i : ℤ,
      i ∈ proEtaleCohomologicalSupport
        ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)) →
      r ≤ i ∧ i ≤ s) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    let F := integralScalarPowerFiltration l L n
    ∀ (j : Fin (n + 1)) (i : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i) ∧
      ((i < r ∨ s < i) → IsZero
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i)) := by
  have hc := integralScalarResidueLayer_constructible l E L ι Y D hl P r s hrs h₁
    hbound n (integralScalarPowerFiltration l L n) rfl
  have hz := integralScalarResidueLayer_vanishing l E L ι Y D hl P r s hrs h₁
    hbound n (integralScalarPowerFiltration l L n) rfl
  dsimp only
  intro j i
  exact ⟨hc j i, hz j i⟩

end WeilConjectures
