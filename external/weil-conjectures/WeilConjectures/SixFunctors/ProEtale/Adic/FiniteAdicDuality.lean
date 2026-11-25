/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.PadicTorsionLinear
public import WeilConjectures.Algebra.Module.ZModSelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtale

/-!
# Finite-level Poincaré duality for the pro-étale cohomology `Hⁱ(X, ℤ_ℓ/ℓᵐ)`

Let `k` be separably closed and `a : X ⟶ Spec k` proper with a Tate orientation of relative
dimension `d` for the coefficients `Λ = ℤ/ℓᵐ`. For `i + j = 2d`, there is a `ℤ_ℓ`-bilinear
pairing `Hⁱ(X_proét, ℤ_ℓ/ℓᵐ) × Hʲ(X_proét, ℤ_ℓ/ℓᵐ) ⟶ ℤ_ℓ/ℓᵐ` which is nondegenerate on both sides
(`AlgebraicGeometry.ProEtale.exists_injective_pairing_finiteAdicH`): the étale finite-level
duality (`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_unitPairing`) read through
`Hⁿ(X_proét, ℤ_ℓ/ℓᵐ) ≅ Hom_{D(X_ét, Λ)}(Λ_X, Λ_X[n])`
(`AlgebraicGeometry.ProEtale.nonempty_addEquiv_finiteAdicH_unitShift`). These are the
finite-level pairings of `AlgebraicGeometry.ProEtale.exists_isPerfPair_adicConstantH`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

/-- The characteristic of `ULift (ZMod n)` is `n`. -/
instance ZMod.neZero_ringChar_ulift (n : ℕ) [NeZero n] :
    NeZero (ringChar (ULift.{u} (ZMod n))) :=
  ⟨by rw [ringChar.eq (ULift.{u} (ZMod n)) n]; exact NeZero.ne n⟩

/-- `ULift (ZMod n)` cogenerates its modules. -/
theorem ZMod.exists_ulift_apply_ne_zero (n : ℕ) [NeZero n]
    {M : Type u} [AddCommGroup M] [Module (ULift.{u} (ZMod n)) M] {x : M} (hx : x ≠ 0) :
    ∃ χ : M →ₗ[ULift.{u} (ZMod n)] ULift.{u} (ZMod n), χ x ≠ 0 :=
  ZModLike.exists_apply_ne_zero (Nat.pos_of_ne_zero (NeZero.ne n)) (ULift.ext (by simp))
    (fun x ↦ ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext (by
      simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩)
    (fun z hz ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd z n).1 (by simpa using congrArg ULift.down hz))
    hx

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- **Finite-level Poincaré duality for `Hⁱ(X_proét, ℤ_ℓ/ℓᵐ)`** (finite level of blueprint
`theorem-poincare-duality--9`, for the constant sheaf). Let `k` be separably closed, `X`
quasi-compact and quasi-separated, `a : X ⟶ Spec k` proper with a Tate orientation `γ` of relative
dimension `d` for `Λ = ℤ/ℓᵐ`. For `i + j = 2d`, there is a `ℤ_ℓ`-bilinear pairing
`Hⁱ(X, ℤ_ℓ/ℓᵐ) × Hʲ(X, ℤ_ℓ/ℓᵐ) ⟶ ℤ_ℓ/ℓᵐ` which is nondegenerate on both sides. -/
theorem exists_injective_pairing_finiteAdicH {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (a : X ⟶ Spec (.of k))
    [HasCompactification a] [IsProper a] (d m : ℕ)
    [HasInvertibleExponent (ULift.{u + 1} (ZMod (l ^ m))) X]
    [HasInvertibleExponent (ULift.{u + 1} (ZMod (l ^ m))) (Spec (.of k))]
    (γ : Etale.TateOrientation (ULift.{u + 1} (ZMod (l ^ m))) a d) (i j : ℕ)
    (hij : i + j = 2 * d) :
    ∃ Q : FiniteAdicH X l m i →ₗ[ℤ_[l]] FiniteAdicH X l m j →ₗ[ℤ_[l]]
        ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m},
      Function.Injective Q ∧ Function.Injective Q.flip := by
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨P, hP₁, hP₂⟩ := γ.exists_nondegenerate_unitPairing
    (fun _ _ hx ↦ ZMod.exists_ulift_apply_ne_zero _ hx) i j (by exact_mod_cast hij)
  obtain ⟨eI⟩ := nonempty_addEquiv_finiteAdicH_unitShift l X m i
  obtain ⟨eJ⟩ := nonempty_addEquiv_finiteAdicH_unitShift l X m j
  let eΛ : ULift.{u + 1} (ZMod (l ^ m)) ≃+ ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m} :=
    AddEquiv.ulift.trans (PadicInt.quotientSpanPowRingEquiv m).symm.toAddEquiv
  let P' : FiniteAdicH X l m i →+ FiniteAdicH X l m j →+ ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ m} :=
    AddMonoidHom.mk' (fun x ↦ (eΛ.toAddMonoidHom.comp (P (eI x))).comp eJ.toAddMonoidHom)
      fun x x' ↦ by ext y; simp
  refine ⟨PadicInt.bilinearOfPowSMulEqZero (pow_smul_finiteAdicH X l m i)
    (pow_smul_finiteAdicH X l m j) PadicInt.pow_smul_quotient_eq_zero P',
    (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_⟩
  · refine eI.injective ((hP₁ (eI x) fun y' ↦ ?_).trans eI.map_zero.symm)
    obtain ⟨y, rfl⟩ := eJ.surjective y'
    simpa [P'] using LinearMap.congr_fun hx y
  · refine eJ.injective ((hP₂ (eJ y) fun x' ↦ ?_).trans eJ.map_zero.symm)
    obtain ⟨x, rfl⟩ := eI.surjective x'
    simpa [P'] using LinearMap.congr_fun hy x

end AlgebraicGeometry.ProEtale
