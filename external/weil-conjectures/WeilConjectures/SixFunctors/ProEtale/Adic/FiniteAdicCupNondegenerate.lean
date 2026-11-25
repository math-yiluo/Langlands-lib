/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.ZModSelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TraceCupNondegenerate
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCup

/-!
# Poincaré duality for the cup product on `Hⁿ(S_proét, ℤ/ℓᵐ)`

Let `k` be a separably closed field in which `ℓ` is invertible and `a : S ⟶ Spec k` proper and
smooth of relative dimension `d`. For `i + j = 2d` the cup product pairing
`Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ H^{2d}(S, ℤ/ℓᵐ)` is nondegenerate on both sides
(`AlgebraicGeometry.ProEtale.finiteAdicHCup_nondegenerate`): through the comparison with
`Hom(Λ_S, Λ_S[n])` in `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`, the cup product is the étale cup product
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH_cupProduct`), whose trace–cup pairing is
nondegenerate for a Tate orientation of `a`
(`AlgebraicGeometry.Etale.TateOrientation.exists_nondegenerate_traceCup`); a Tate orientation exists
by smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`,
`proposition-smooth-purity-finite-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k] {S : Scheme.{u}}
  (a : S ⟶ Spec (.of k)) [IsProper a] {d : ℕ} [SmoothOfRelativeDimension d a]
  [HasCompactification a] [CompactSpace S] [QuasiSeparatedSpace S]

include a in
/-- **The cup product pairing on `Hⁿ(S, ℤ/ℓᵐ)` is nondegenerate in complementary degrees** for `S`
proper and smooth of relative dimension `d` over a separably closed field in which `ℓ` is
invertible. -/
theorem finiteAdicHCup_nondegenerate (hl : (l : k) ≠ 0) (m : ℕ) {i j n : ℕ} (h : i + j = n)
    (hn : n = 2 * d) :
    (∀ x : FiniteAdicH S l m i, (∀ y, finiteAdicHCup l m S h x y = 0) → x = 0) ∧
      (∀ y : FiniteAdicH S l m j, (∀ x, finiteAdicHCup l m S h x y = 0) → y = 0) := by
  let Λ := ULift.{u + 1} (ZMod (l ^ m))
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (ringChar Λ) := by rw [ringChar.eq Λ (l ^ m)]; infer_instance
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨l ^ m, Nat.pos_of_ne_zero (NeZero.ne _), ULift.ext (by simp [Λ]), by
      simpa using ((Ne.isUnit (pow_ne_zero m hl)).map (Scheme.ΓSpecIso (.of k)).inv.hom)⟩
  have : HasInvertibleExponent Λ S := .of_hom a
  have hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0 :=
    fun M x hx ↦ ZModLike.exists_apply_ne_zero (n := l ^ m)
      (Nat.pos_of_ne_zero (NeZero.ne _)) (ULift.ext (by
        simpa using (Nat.cast_pow l m).symm.trans (ZMod.natCast_self (l ^ m))))
      (fun x ↦ ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext (by
        simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩)
      (fun z hz ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd z _).1 (by
        simpa using congrArg ULift.down hz)) hx
  obtain ⟨θ⟩ := Etale.nonempty_iso_dualizingComplex_twistShift Λ (d := d) a (𝟙 _)
  obtain ⟨T, hT⟩ := Etale.TateOrientation.exists_nondegenerate_traceCup hcog θ.symm
  subst hn
  have hij : (i : ℤ) + (j : ℤ) = 2 * (d : ℤ) := by exact_mod_cast h
  obtain ⟨h₁, h₂⟩ := hT i j hij
  -- a vanishing cup product in `FiniteAdicH` gives a vanishing étale cup product
  have hzero : ∀ x y, finiteAdicHCup l m S h (unitShiftAddEquivFiniteAdicH l m S i x)
      (unitShiftAddEquivFiniteAdicH l m S j y) = 0 →
      T (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫ eqToHom (by rw [hij])) = 0 := by
    intro x y hxy
    rw [← unitShiftAddEquivFiniteAdicH_cupProduct, AddEquiv.map_eq_zero_iff] at hxy
    rw [Preadditive.IsIso.comp_right_eq_zero] at hxy
    rw [hxy, zero_comp, map_zero]
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective x
    rw [h₁ x fun y ↦ hzero x y (hx _), map_zero]
  · obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective y
    rw [h₂ y fun x ↦ hzero x y (hy _), map_zero]

end AlgebraicGeometry.ProEtale
