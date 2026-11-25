/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import all WeilConjectures.SmoothPurity.Pur.PurAdicScalarExtensionTorBound

/-! # Finite Tor constructibility under ordinary completed scalar extension

Source: Bhatt--Scholze, Sections 6.5--6.6; Stacks Tag 06YY.
(blueprint: lem-pur-finite-tor-integral-completed-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Ordinary completed coefficient extension preserves constructibility and one uniform
finite Tor interval on the finite reductions.

Source: Bhatt--Scholze, Sections 6.5--6.6; Stacks Tag 06YY.
(blueprint: lem-pur-finite-tor-integral-completed-scalar-extension).

Proof: intrinsic derived completeness gives unrestricted completeness, by testing
against a finite-field datum of auxiliary prime characteristic different from l.
The finite-free completed comparison identifies ordinary derived scalar extension
with its completed scalar-tower functor on this complete input. Transport the existing
intrinsic constructibility theorem along that isomorphism. At each equal positive
quotient exponent the completed scalar/reduction comparison identifies the reduced
output with finite scalar extension of the reduced input. Finite scalar extension
preserves its given Tor interval. Compose the isomorphisms in the test-object
condition to transport the Tor bound, retaining the same interval at every level.
No ramification exponent or geometric condition on the scheme is needed. -/
theorem finiteTorIntegralCompletedScalarExtension
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) := by
  have hc : IsDerivedCompleteUnrestricted l E X M := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    have : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one p).symm
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
    exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E X D₀ hl₀ M).mp hM.1.1⟩
  have hchi := ((finiteFreeCompletedScalarComparison l E F i X).2.1 M hc).1
  have := hchi
  have hscalar : sfIntegralConstructible l F X
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) :=
    (sfIntegralConstructible l F X).prop_of_iso
      (asIso ((completedScalarComparison l E F i X).app M)).symm
      (sfIntegralScalarExtension_constructible p l hl E F i X M hM.1)
  have hF : finiteTorConstructibleIntegral l F X
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) := by
    refine ⟨hscalar, ?_⟩
    obtain ⟨a, b, hab, hbounds⟩ := hM.2
    refine ⟨a, b, hab, fun n ↦ ?_⟩
    obtain ⟨e⟩ := WeilConjectures.completedScalarReductionComparison l E F i X n
    have ht := AlgebraicGeometry.ProEtale.scalarExtension_tor
      (integralScalarQuotientMap l E F i n) X _ a b (hbounds n)
    refine ⟨ht.1, ?_⟩
    intro N P hN v hv hP L k hk
    obtain ⟨eN⟩ := hN
    exact ht.2 N P ⟨eN ≪≫ e.app M⟩ v hv hP L k hk
  exact hF

end WeilConjectures
