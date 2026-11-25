/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension

import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Algebra.Field.ULift

/-!
# Integral scalar extension preserves intrinsic bounded constructibility

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

private noncomputable def scalarExtensionDatum (p : ℕ) (hp : p.Prime) :
    FiniteFieldDatum.{u} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ULift.{u} (ZMod p)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod p)) }

private theorem constructible_iff_legacy
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y)) :
    sfIntegralConstructible l E Y K ↔
      boundedConstructibleDerivedCompleteIntegral D l hl E Y K := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    constructor
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl K).mp hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 hi⟩
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl K).mpr hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩

/-- Completed integral scalar extension preserves the intrinsic bounded constructible
predicate over arbitrary schemes.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the K-flat augmented-tower definition of completeness is equivalent to the intrinsic
one, by the canonical tensor counits, normalized units, and pure-tensor transitions.
Finite-level constructibility and the common cohomological interval are the same in the
two predicates. Choose an auxiliary finite-field datum of prime characteristic larger
than l, transfer the input to the legacy predicate, apply the published completed
scalar-extension preservation theorem, and transfer its output back. The auxiliary
datum imposes no condition on the scheme and disappears from the conclusion.
-/
theorem sfIntegralScalarExtension_constructible
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l L Y
      ((integralScalarExtension l E L ι Y).obj K) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let D := scalarExtensionDatum.{u} q hprime
    have hlD : l ≠ D.p := by
      change l ≠ q
      omega
    have hlegacy := (constructible_iff_legacy l E Y D hlD K).mp hK
    exact (constructible_iff_legacy l L Y D hlD _).mpr
      (integralScalarExtension_constructible D l hlD E L ι Y ⟨K, hlegacy⟩)

/-- The completed scalar extension restricted to intrinsic bounded constructible
objects. Its object map is the ambient extension and its morphism map is inherited.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/
noncomputable def sfConstructibleIntegralScalarExtension
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l L Y :=
  (sfIntegralConstructible l L Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y)
    (fun X ↦ sfIntegralScalarExtension_constructible p l _hl E L ι Y X.obj X.property)

/-- The restricted functor is linear for the integral coefficient action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient completed extension is linear on morphisms; the full-subcategory
restriction preserves the same equality.
-/
theorem sfConstructibleIntegralScalarExtension_smul
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K K' : sfIntegralConstructibleCategory l E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (integralScalarExtension l E L ι Y).map
        ((integralScalarDerivedAction l E Y a).app K.obj ≫ f.hom) =
      (integralScalarDerivedAction l L Y
          (integralScalarIntegerInclusion l E L ι a)).app
          ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).obj K).obj ≫
        ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).map f).hom := by
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures
