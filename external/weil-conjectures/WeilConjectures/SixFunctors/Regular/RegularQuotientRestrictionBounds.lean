/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import WeilConjectures.SixFunctors.Integral.IntegralReductionTorAmplitude
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleExactClosure
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleRestrictScalars
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Uniform constructibility and Tor bounds for finite quotient restriction

Source: Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ; Zheng Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-regular-quotient-restriction-bounds). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

open CategoryTheory.Limits

/-- The cohomology sheaves of a finite reduction of the restriction of a finite-level complex
`K` are controlled by those of `K`: the `i`-th one vanishes if the `i`-th and `(i+1)`-st
cohomology sheaves of `K` vanish, and it is constructible if all cohomology sheaves of `K`
are constructible.
Source: Stacks Project, Tags 06YY, 093U and 0A70
(blueprint: lem-sf-regular-quotient-restriction-bounds).

Proof: let `M` be the restriction of `K` to the completed coefficient ring. The derived
reduction triangle `M --ϖ^(m+1)--> M --> res_m(red_m M)` gives the exact sequence
`H^i M --> H^i M --> res_m H^i(red_m M) --> H^(i+1) M --> H^(i+1) M`. Restriction is exact, so
`H^j M` is the restriction of `H^j K`. For the vanishing, use exactness at the middle term
and faithfulness of restriction. For constructibility, restrict everything to the finite
quotient `A_(n+m+1)`, through which both restrictions factor, and lift the exact sequence
there by full faithfulness of restriction. Constructibility over `A_(n+m+1)` is closed under
kernels, cokernels and extensions, so the middle term is constructible over `A_(n+m+1)`, and
restriction along the surjection `A_(n+m+1) → A_(m+1)` reflects constructibility. -/
theorem scalarReductionDerivedRestriction_reduction_homology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n)) (m : ℕ) (i : ℤ) :
    (IsZero ((DerivedCategory.homologyFunctor _ i).obj K) →
      IsZero ((DerivedCategory.homologyFunctor _ (i + 1)).obj K) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((scalarReductionDerivedExtension.{u, u} l E T m).obj
          ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)))) ∧
    (letI := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega);
      letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega);
      (∀ j : ℤ, IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (n + 1))
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (n + 1)))) j).obj K)) →
      IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (m + 1))
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (m + 1)))) i).obj
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)))) := by
  let M := (scalarReductionDerivedRestriction.{u, u} l E T n).obj K
  let C := (scalarReductionDerivedExtension.{u, u} l E T m).obj M
  obtain ⟨δ, hT⟩ :=
    (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.2 m M
  let H (j : ℤ) := DerivedCategory.homologyFunctor (scalarReductionSource.{u, u} l E T) j
  let eK (j : ℤ) : (H j).obj M ≅ (scalarReductionRestriction.{u, u} l E T n).obj
      ((DerivedCategory.homologyFunctor _ j).obj K) :=
    (((scalarReductionRestriction.{u, u} l E T n).mapDerivedCategoryHomologyFunctorIso j).app
      K).symm
  let eC : (H i).obj ((scalarReductionDerivedRestriction.{u, u} l E T m).obj C) ≅
      (scalarReductionRestriction.{u, u} l E T m).obj
        ((DerivedCategory.homologyFunctor _ i).obj C) :=
    (((scalarReductionRestriction.{u, u} l E T m).mapDerivedCategoryHomologyFunctorIso i).app
      C).symm
  have ex₂ := DerivedCategory.HomologySequence.exact₂ _ hT i
  have ex₃ := DerivedCategory.HomologySequence.exact₃ _ hT i (i + 1)
  have ex₁ := DerivedCategory.HomologySequence.exact₁ _ hT i (i + 1)
  constructor
  · intro h₀ h₁
    have hz : IsZero ((H i).obj ((scalarReductionDerivedRestriction.{u, u} l E T m).obj C)) := by
      exact ex₃.isZero_X₂_iff.2 ⟨(((scalarReductionRestriction.{u, u} l E T n).map_isZero h₀).of_iso
        (eK i)).eq_of_src _ _, (((scalarReductionRestriction.{u, u} l E T n).map_isZero
          h₁).of_iso (eK (i + 1))).eq_of_tgt _ _⟩
    rw [IsZero.iff_id_eq_zero]
    apply (scalarReductionRestriction.{u, u} l E T m).map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (hz.of_iso eC.symm).eq_of_src _ _
  · intro hc
    have hn : n ≤ n + m := Nat.le_add_right n m
    have hm : m ≤ n + m := Nat.le_add_left m n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    let := Padic.finite_coefficientExtensionRing l E (n + m + 1) (by omega)
    let en := scalarReductionRestrictionTransitionIso l E T hn
    let em := scalarReductionRestrictionTransitionIso l E T hm
    obtain ⟨hk, hext⟩ :=
      constructibleProEtale_exactClosure T (Padic.coefficientExtensionRing l E (n + m + 1))
    have hP := ObjectProperty.prop_X₃_of_exact_of_fullyFaithful
      (scalarReductionRestriction.{u, u} l E T (n + m))
      (IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (n + m + 1)))
      (fun _ _ f hX hY ↦ (hk _ _ f hX hY).1) (fun _ _ f hX hY ↦ (hk _ _ f hX hY).2) hext
      ex₂ ex₃ ex₁ (eK i ≪≫ (en.app _).symm) (eK i ≪≫ (en.app _).symm)
      (eC ≪≫ (em.app _).symm) (eK (i + 1) ≪≫ (en.app _).symm)
      (eK (i + 1) ≪≫ (en.app _).symm)
      ((hc i).restrictScalars _) ((hc i).restrictScalars _)
      ((hc (i + 1)).restrictScalars _) ((hc (i + 1)).restrictScalars _)
    exact IsConstructibleProEtaleModuleSheaf.of_restrictScalars _
      (coefficientExtensionRingMap_surjective l E hm) hP

/-- Restriction of a finite-Tor constructible quotient complex has constructible finite
reductions with one cohomological and Tor interval, independent of the reduction level.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Project, Tags 06YY, 07A6 and 08FZ.
(blueprint: lem-sf-regular-quotient-restriction-bounds).

Proof: choose a bounded flat representative in a Tor interval [a,b] for K. Each flat
module over the fixed quotient B=A/(pi^(n+1)) has flat dimension at most one over A:
tensor the length-one free resolution of B with it, or use the change-of-rings Tor
spectral sequence and B-flatness. The bounded representative therefore has A-Tor
amplitude [a-1,b]. Derived tensor with any quotient A/(pi^(m+1)) retains this same
interval over the target quotient, by derived tensor associativity. Tensoring with
the unit gives the same cohomological bound, for every m at once. To check
constructibility, use a finite locally closed stratification trivializing the bounded
constructible finite-Tor B-complex locally by bounded finite projective B-complexes.
Resolve each finite projective term over A using the regular principal resolution,
and tensor this finite model with A/(pi^(m+1)). Its cohomology is finite over the
finite target ring, and the local constant models give constructible cohomology on
each of the same strata. The normalized scalar-extension counit identifies these
computations with the prescribed scalarReductionDerivedExtension, and exact scalar
restriction identifies their input with scalarReductionDerivedRestriction. Isomorphism
invariance transfers both predicates to those functors. Enlarge the two finite bounds
if necessary to obtain ordered a,b common to cohomology and Tor. Positivity of n+1
and m+1 includes level zero; zero complexes and empty strata satisfy the same bounds.
This statement does not assert derived completeness or any adjunction. -/
theorem scalarReductionDerivedRestriction_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) T
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (m + 1))
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) a b := by
  obtain ⟨⟨hfin, hcon⟩, -⟩ := hK
  obtain ⟨s, t, hst, hK⟩ : ∃ s t : ℤ, s ≤ t ∧ ∀ i : ℤ,
      ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K) → s ≤ i ∧ i ≤ t := by
    obtain ⟨s, hs⟩ := hfin.bddBelow
    obtain ⟨t, ht⟩ := hfin.bddAbove
    exact ⟨min s t, t, min_le_right _ _,
      fun i hi ↦ ⟨(min_le_left _ _).trans (hs hi), ht hi⟩⟩
  have hsupp (m : ℕ) : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E T m).obj
        ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc (s - 1) t := by
    intro i hi
    by_contra hni
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hni
    apply hi
    refine (scalarReductionDerivedRestriction_reduction_homology l E T n K m i).1 ?_ ?_
    · by_contra h
      have := hK i h
      omega
    · by_contra h
      have := hK (i + 1) h
      omega
  refine ⟨s - 1, t, by omega, fun m ↦ ⟨⟨(Set.finite_Icc (s - 1) t).subset (hsupp m),
    fun i ↦ (scalarReductionDerivedRestriction_reduction_homology l E T n K m i).2 hcon⟩,
    hsupp m, ?_⟩⟩
  exact scalarReductionDerivedExtension_torAmplitude_of_residue_support l E T _ (s - 1) t
    (by omega) (fun i hi ↦ hsupp 0 hi) m

end WeilConjectures
