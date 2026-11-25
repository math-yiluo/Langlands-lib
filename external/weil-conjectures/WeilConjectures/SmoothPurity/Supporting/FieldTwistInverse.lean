/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
import Mathlib.Data.Nat.Prime.Infinite

/-! # Inverse evaluation for the recorded field coefficient twists

Source: definition-tate-twists--10, proof steps 9--13.
(blueprint: lem-weil-field-twist-inverse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Opposite signed root lines give inverse twists after rationalization and common stages.
Source: blueprint definition-tate-twists--10, proof steps 9--13
(blueprint: lem-weil-field-twist-inverse).

Proof: restrict the exact integral line tensor functors to the intrinsic constructible
subcategory. Their evaluation maps are inverse isomorphisms, checked on a rank-one
trivializing cover, and are linear for the canonical coefficient action. Localize these
functors and their evaluations by integral_twist_rationalization. The normalization of
rationalDerivedTensor on integral objects and pure localized arrows identifies these
localized functors with sfRationalTwistingFunctor, yielding its inverse evaluation.
For every finite extension the ordinary-to-completed scalar comparison identifies
base change of the line with the corresponding root line. The canonical beta maps
commute with evaluation, identity extensions and successive extensions by
integral_twist_base_change and integral_twist_scalar_coherence. Apply
qbar_twist_common_stage to these normalized rational functors and comparisons.
Its representative formula is exactly commonStageDerivedTensor with the signed line
represented at the least finite stage; enlarge to the common stage and cancel the
beta maps. Thus its descended evaluation is the displayed Qbar inverse. All maps
are natural on pure localized arrows and extend by additivity. Empty schemes and
m = 0 use the same unit/evaluation formulas. No discrete field sheaves are introduced. -/
theorem fieldTwist_inverse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (m : ℤ) :
    Nonempty (sfRationalTwistingFunctor l E S m ⋙
      sfRationalTwistingFunctor l E S (-m) ≅ 𝟭 _) ∧
    Nonempty (sfQbarTwistingFunctor l S Ω m ⋙ sfQbarTwistingFunctor l S Ω (-m) ≅ 𝟭 _) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (Padic l)
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hfinite, hint, hfield⟩ :=
    AlgebraicGeometry.Scheme.tateTwist_locallyFree S l E Ω
      (IsAlgClosed.lift : E →ₐ[Padic l] Ω)
  have hpos (n : ℕ) :
      Nonempty (sfRationalTwistingFunctor l E S (n : ℤ) ⋙
        sfRationalTwistingFunctor l E S (-(n : ℤ)) ≅ 𝟭 _) ∧
      Nonempty (sfQbarTwistingFunctor l S Ω (n : ℤ) ⋙
        sfQbarTwistingFunctor l S Ω (-(n : ℤ)) ≅ 𝟭 _) ∧
      Nonempty (sfRationalTwistingFunctor l E S (-(n : ℤ)) ⋙
        sfRationalTwistingFunctor l E S (n : ℤ) ≅ 𝟭 _) ∧
      Nonempty (sfQbarTwistingFunctor l S Ω (-(n : ℤ)) ⋙
        sfQbarTwistingFunctor l S Ω (n : ℤ) ≅ 𝟭 _) := by
    obtain ⟨er, hrf, hri⟩ := ((hfield D hl).2.2 n).2.1
    obtain ⟨eq, hqf, hqi⟩ := ((hfield D hl).2.2 n).2.2
    have hr := er.unitIso.symm
    have hr' := er.counitIso
    have hq := eq.unitIso.symm
    have hq' := eq.counitIso
    rw [hrf, hri] at hr hr'
    rw [hqf, hqi] at hq hq'
    exact ⟨⟨hr⟩, ⟨hq⟩, ⟨hr'⟩, ⟨hq'⟩⟩
  cases m with
  | ofNat n => exact ⟨(hpos n).1, (hpos n).2.1⟩
  | negSucc n =>
    simpa only [Int.natCast_add, Int.cast_ofNat_Int, Int.natCast_one, neg_neg,
      Int.negSucc_eq] using (hpos (n + 1)).2.2

end WeilConjectures
