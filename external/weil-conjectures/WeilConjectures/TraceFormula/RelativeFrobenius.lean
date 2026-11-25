/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
public import WeilConjectures.TraceFormula.Frobenius

/-!
# The relative Frobenius of model Frobenii

Let `k₀` be a finite field, `k` a field over `k₀`, and `X = X₀ ×_{k₀} k`, `Y = Y₀ ×_{k₀} k`
objects of `Over (Spec (.of k))` with model Frobenii `Φ_X`, `Φ_Y`. For a morphism `f : X ⟶ Y`
with `Φ_X ≫ f = f ≫ Φ_Y`, the relative Frobenius `r_m = (f, Φ_X ^ m) : X ⟶ X'_m` into
`X'_m = Y ×_{Φ_Y ^ m, Y, f} X` is a finite universal homeomorphism, and if `f` is the base
change of a morphism `f₀ : X₀ ⟶ Y₀`, then `r_m` is the base change of the relative
`#k₀ ^ m`-power Frobenius of `f₀`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.isFinite_frobeniusIterate_left`,
  `AlgebraicGeometry.ProEtale.CondensedRing.isUniversalHomeomorphism_frobeniusIterate_left`:
  iterates of finite (universally homeomorphic) endomorphisms.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.relativeFrobenius_frobeniusIterate`:
  the relative Frobenius `r_m` is a finite universal homeomorphism with `p_m ∘ r_m = Φ_X ^ m`
  and `f'_m ∘ r_m = f` (blueprint `lemma-comparison-via-relative-frobenius--1`).
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.isPullback_relativeFrobenius_left`:
  `r_m` is the base change of the relative `#k₀ ^ m`-power Frobenius of a model `f₀`
  (blueprint `lemma-comparison-via-relative-frobenius--text-1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Iterate

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (Φ : X ⟶ X)

/-- The iterates `Φ_m` of a finite endomorphism are finite (blueprint
`lemma-comparison-via-relative-frobenius--1`). -/
instance isFinite_frobeniusIterate_left [IsFinite Φ.left] (m : ℕ) :
    IsFinite (frobeniusIterate Φ m).left := by
  rw [frobeniusIterate_left]
  exact MorphismProperty.endAsHom_pow_mem @IsFinite ‹_› m

/-- The iterates `Φ_m` of a universal homeomorphism are universal homeomorphisms (blueprint
`lemma-comparison-via-relative-frobenius--1`). -/
instance isUniversalHomeomorphism_frobeniusIterate_left [IsUniversalHomeomorphism Φ.left]
    (m : ℕ) : IsUniversalHomeomorphism (frobeniusIterate Φ m).left := by
  rw [frobeniusIterate_left]
  exact MorphismProperty.endAsHom_pow_mem @IsUniversalHomeomorphism ‹_› m

end Iterate

section Model

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}}
  {fX₀ : X₀ ⟶ Spec (.of k₀)} {fY₀ : Y₀ ⟶ Spec (.of k₀)} {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀}

/-- **Relative Frobenius** (blueprint `lemma-comparison-via-relative-frobenius--1`,
`lemma-comparison-via-relative-frobenius` (1)). Let `Φ_X`, `Φ_Y` be model Frobenii of models `X₀`,
`Y₀` locally of finite type over `k₀`, and `f : X ⟶ Y` with `Φ_X ≫ f = f ≫ Φ_Y`. For every `m`, the
relative Frobenius `r_m = (f, Φ_X ^ m) : X ⟶ Y ×_{Φ_Y ^ m, Y, f} X` is finite and a universal
homeomorphism, and `p_m ∘ r_m = Φ_X ^ m`, `f'_m ∘ r_m = f`. -/
theorem IsModelFrobenius.relativeFrobenius_frobeniusIterate [LocallyOfFiniteType fX₀]
    [LocallyOfFiniteType fY₀] (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY) (m : ℕ) :
    IsFinite (relativeFrobenius f (frobeniusIterate ΦX m) (frobeniusIterate ΦY m)
        (frobeniusIterate_comp_of_comp hf m)).left ∧
      IsUniversalHomeomorphism (relativeFrobenius f (frobeniusIterate ΦX m)
        (frobeniusIterate ΦY m) (frobeniusIterate_comp_of_comp hf m)).left ∧
      relativeFrobenius f (frobeniusIterate ΦX m) (frobeniusIterate ΦY m)
          (frobeniusIterate_comp_of_comp hf m) ≫ pullback.snd (frobeniusIterate ΦY m) f =
        frobeniusIterate ΦX m ∧
      relativeFrobenius f (frobeniusIterate ΦX m) (frobeniusIterate ΦY m)
          (frobeniusIterate_comp_of_comp hf m) ≫ pullback.fst (frobeniusIterate ΦY m) f = f := by
  have := hX.isFinite m
  have := hY.isFinite m
  have := hX.isUniversalHomeomorphism m
  have := hY.isUniversalHomeomorphism m
  exact ⟨inferInstance, inferInstance, relativeFrobenius_snd .., relativeFrobenius_fst ..⟩

/-- **The relative Frobenius factorization** (blueprint
`lemma-comparison-via-relative-frobenius--text-1`, in `Over`). Let `Φ_X`, `Φ_Y` be model Frobenii of
models `X₀`, `Y₀` over `k₀`, and let `f : X ⟶ Y` with `Φ_X ≫ f = f ≫ Φ_Y` be the base change of
`f₀ : X₀ ⟶ Y₀` (`f ≫ p_Y = p_X ≫ f₀`). Put `Q = #k₀ ^ m`. There are the `Q`-power Frobenii `F_X`,
`F_Y` of `X₀`, `Y₀` (the `m`-th powers of the `#k₀`-power Frobenii) and a morphism
`g : X'_m ⟶ X₀^{(Q)} = Y₀ ×_{F_Y, Y₀, f₀} X₀`, the product of `p_Y` and `p_X`, exhibiting
`X'_m = Y ×_{Φ_Y ^ m, Y, f} X` as the base change `X₀^{(Q)} ×_{k₀} k`, such that `r_m` is the base
change of the relative `Q`-power Frobenius `F_{X₀/Y₀} = (f₀, F_X)`. -/
theorem IsModelFrobenius.isPullback_relativeFrobenius_left (hX : IsModelFrobenius ΦX fX₀ pX)
    (hY : IsModelFrobenius ΦY fY₀ pY) (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY) {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (m : ℕ) :
    ∃ (FX : X₀ ⟶ X₀) (FY : Y₀ ⟶ Y₀) (h₀ : FX ≫ f₀ = f₀ ≫ FY)
      (g : (pullback (frobeniusIterate ΦY m) f).left ⟶ pullback FY f₀),
      FX.IsFrobenius (Nat.card k₀ ^ m) ∧ FY.IsFrobenius (Nat.card k₀ ^ m) ∧
      g ≫ pullback.fst FY f₀ = (pullback.fst (frobeniusIterate ΦY m) f).left ≫ pY ∧
      g ≫ pullback.snd FY f₀ = (pullback.snd (frobeniusIterate ΦY m) f).left ≫ pX ∧
      IsPullback g (pullback (frobeniusIterate ΦY m) f).hom (pullback.snd FY f₀ ≫ fX₀)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
      IsPullback (relativeFrobenius f (frobeniusIterate ΦX m) (frobeniusIterate ΦY m)
        (frobeniusIterate_comp_of_comp hf m)).left pX g (relativeFrobenius f₀ FX FY h₀) := by
  obtain ⟨FX, hFX, hpX⟩ := hX.exists_isFrobenius
  obtain ⟨FY, hFY, hpY⟩ := hY.exists_isFrobenius
  have hXm : (frobeniusIterate ΦX m).left ≫ pX = pX ≫ End.asHom (End.of FX ^ m) := by
    rw [frobeniusIterate_left]
    exact End.asHom_pow_comp_eq_comp_asHom_pow hpX m
  have hYm : IsPullback (frobeniusIterate ΦY m).left pY pY (End.asHom (End.of FY ^ m)) := by
    rw [frobeniusIterate_left]
    exact isPullback_frobenius_pow_of_isFrobenius hY.isPullback hFY (Over.w ΦY) hpY m
  have h₀ := End.asHom_pow_comp_eq_comp_asHom_pow (hFX.comp_eq_comp fX₀ hFY f₀).symm m
  have hfl : (frobeniusIterate ΦX m).left ≫ f.left = f.left ≫ (frobeniusIterate ΦY m).left := by
    rw [← Over.comp_left, frobeniusIterate_comp_of_comp hf m, Over.comp_left]
  let e := (isPullback_left_pullback f (frobeniusIterate ΦY m)).isoPullback
  refine ⟨_, _, h₀, e.hom ≫ pullback.map _ _ _ _ pY pX pY hYm.w hfp, hFX.pow fX₀ m,
    hFY.pow fY₀ m, by simp [e], by simp [e], ?_, ?_⟩
  · refine (isPullback_pullbackMap hX.isPullback hfp hYm).of_iso e.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    simp only [e, Iso.refl_hom, Category.comp_id, Iso.symm_hom, pullback_hom_eq,
      IsPullback.isoPullback_inv_snd_assoc]
  · refine (isPullback_relativeFrobenius hX.isPullback hfp h₀
      (End.asHom_pow_comp_of_comp_eq (hFX.comp_eq fX₀) m) hfl (Over.w _) hXm hYm).of_iso
      (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) (by simp)
    rw [← relativeFrobenius_left_comp_isoPullback_hom (h := frobeniusIterate_comp_of_comp hf m)]
    simp [e]

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
