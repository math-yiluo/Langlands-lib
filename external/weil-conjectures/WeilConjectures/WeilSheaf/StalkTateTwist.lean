/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Evaluation
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.StalkPairing
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The Frobenius on the stalks of the Tate sheaves

The Tate sheaf `ℚ̄_ℓ(m)` is the constant Weil twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafIso`), where `χ_ℓ(σ) = q⁻¹` is the scalar by which the
geometric Frobenius of `k̄` acts on roots of unity. The local Frobenius of the constant sheaf
`ℚ̄_ℓ` is the identity, so the local Frobenius of `ℚ̄_ℓ(m)` at a closed point `x` of degree `d` is
`(q⁻ᵐ)ᵈ = Q_x⁻ᵐ`, where `Q_x = #κ(x) = qᵈ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.stalk_frobenius_tateTwistSheaf`: the geometric Frobenius of the
  stalk of `ℚ̄_ℓ(m)` at a closed point `x` is `Q_x⁻ᵐ`.

## Blueprint

`AlgebraicGeometry.WeilSheaf.stalk_frobenius_tateTwistSheaf` implements
`proposition-weights-under-usual-operations--13`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (n : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.hom =
    (specGeometricFrobenius k₀ ^ n).asIso.hom ≫ s)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The Frobenius of the stalk of the constant twist `ℚ̄_ℓ ⊗ 𝓑_b` relative to `𝔽_{qⁿ}` is
multiplication by `bⁿ`. -/
theorem stalkAt_frobenius_constantTwist_adicConstant (b : (PadicAlgCl l)ˣ)
    (w : (((adicConstant k₀ l X).constantTwist b).stalkAt s n hs).carrier) :
    (((adicConstant k₀ l X).constantTwist b).stalkAt s n hs).frobenius w =
      (b : PadicAlgCl l) ^ n • w := by
  obtain ⟨E⟩ := nonempty_equiv_stalkAt_constantTwist (adicConstant k₀ l X) b s n hs
  apply E.toLinearEquiv.injective
  rw [E.map_frobenius, map_smul]
  refine (FrobeniusModule.frobeniusEnd_rescale_apply (M := (adicConstant k₀ l X).stalkAt s n hs)
    (pow_ne_zero n b.ne_zero) (E.toLinearEquiv w)).trans (congrArg _ ?_)
  exact LinearEquiv.congr_fun (adicConstant_stalkAt_frobenius (k₀ := k₀) (l := l) s n hs) _

/-- The Frobenius of the stalk of `ℚ̄_ℓ(m)` at a geometric point, relative to `𝔽_{qⁿ}`, is
multiplication by `χ_ℓ(σ)ᵐⁿ`. -/
theorem stalkAt_frobenius_tateTwistSheaf (m : ℤ)
    (v : ((tateTwistSheaf k₀ l X m).stalkAt s n hs).carrier) :
    ((tateTwistSheaf k₀ l X m).stalkAt s n hs).frobenius v =
      ((cyclotomicUnit k₀ l ^ m : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n • v := by
  apply injective_stalkAtMap s n hs (tateTwistSheafIso k₀ l X m).hom
  rw [stalkAtMap_frobenius, map_smul]
  exact stalkAt_frobenius_constantTwist_adicConstant s n hs _ _

/-- **Frobenius on the stalk of a twist.** For every `m ∈ ℤ` and every closed point `x`, the
geometric Frobenius of the stalk of `ℚ̄_ℓ(m)` at `x` is multiplication by `Q_x⁻ᵐ`, where
`Q_x = #κ(x)`. (blueprint: `proposition-weights-under-usual-operations--13`) -/
theorem stalk_frobenius_tateTwistSheaf (m : ℤ) (x : X.finitePoints)
    (v : ((tateTwistSheaf k₀ l X m).stalk x).carrier) :
    ((tateTwistSheaf k₀ l X m).stalk x).frobenius v =
      (X.pointNorm x.1 : PadicAlgCl l) ^ (-m) • v := by
  refine (stalkAt_frobenius_tateTwistSheaf _ _ _ m v).trans ?_
  rw [cyclotomicUnit_zpow_eq,
    Scheme.Hom.pointNorm_eq_pow_degreeOver (X ↘ Spec (CommRingCat.of k₀)) x.2, Nat.cast_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end AlgebraicGeometry.WeilSheaf
