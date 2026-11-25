/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusPoints
public import WeilConjectures.Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.TraceFormula.Frobenius

/-!
# The fixed points of the model Frobenius

Let `k₀` be a finite field with `q` elements, `k` a field extension of `k₀`, `X₀` a scheme over
`k₀` with structure morphism `f₀`, `X = X₀ ×_{k₀} k` with projection `p : X ⟶ X₀`, and
`Φ = F₀ × 𝟙` the model Frobenius of `X`. The rational points `x : s ⟶ X` fixed by
`Φ_m = Φ^m` correspond, through `x ↦ x ≫ p`, to the `k`-points `g : Spec k ⟶ X₀` over `k₀`
fixed by `Spec σ^m`, where `σ : a ↦ a ^ q` is the arithmetic Frobenius of `k` (blueprint
`lemma-frobenius-fixed-scheme--1`).

Indeed, sections of `X ⟶ Spec k` are the `k₀`-morphisms `Spec k ⟶ X₀` by the universal property
of the pullback, and since `Φ_m ≫ p = p ≫ F₀^m` and the Frobenius commutes with all morphisms,
`x ≫ Φ_m ≫ p = (x ≫ p) ≫ F₀^m = Spec σ^m ≫ x ≫ p`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.frobeniusIterate_left_comp`:
  `Φ_m ≫ p = p ≫ F₀^m`.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.comp_frobeniusIterate_left_eq_iff`:
  a morphism `x : Spec k ⟶ X` is fixed by `Φ_m` if and only if `x ≫ p` is fixed by
  `Spec σ^m`.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.fixedPointEquiv`: the
  rational points of `X` fixed by `Φ_m` are the `k`-points of `X₀` fixed by `Spec σ^m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- The iterates of the model Frobenius are the base changes of the iterates of `F₀`:
`Φ_m ≫ p = p ≫ F₀^m` for any `F₀` with `Φ ≫ p = p ≫ F₀`. -/
lemma IsModelFrobenius.frobeniusIterate_left_comp {F₀ : X₀ ⟶ X₀} (hp : Φ.left ≫ p = p ≫ F₀)
    (m : ℕ) : (frobeniusIterate Φ m).left ≫ p = p ≫ End.asHom (End.of F₀ ^ m) := by
  rw [frobeniusIterate_left]
  exact End.asHom_pow_comp_eq_comp_asHom_pow hp m

/-- A morphism `x : Spec k ⟶ X` is fixed by `Φ_m` if and only if the `k`-point
`x ≫ p` of `X₀` is fixed by `Spec σ^m`, for `σ : a ↦ a ^ #k₀` the arithmetic Frobenius of
`k`. -/
lemma IsModelFrobenius.comp_frobeniusIterate_left_eq_iff [Fintype k₀]
    (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ) (x : Spec (.of k) ⟶ X.left) :
    x ≫ (frobeniusIterate Φ m).left = x ↔
      Spec.map (CommRingCat.ofHom
        ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k)) ≫ x ≫ p = x ≫ p := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  have key := frobeniusIterate_left_comp hp m
  have hfrob : (x ≫ p) ≫ End.asHom (End.of F₀ ^ m) = _ :=
    hF₀.comp_pow_eq_specMap_frobeniusAlgHom_pow f₀ (x ≫ p) m
  constructor
  · intro h
    rw [← hfrob, Category.assoc, ← key, ← Category.assoc, h]
  · intro h
    refine hΦ.isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, key, ← Category.assoc, hfrob, h]
    · rw [Category.assoc, Over.w]

omit [Algebra k₀ k] in
/-- The underlying morphism of a rational point of `X` is a section of `a_X`. -/
lemma rationalPoint_left_comp_hom (x : RationalPoint X) : x.left ≫ X.hom = 𝟙 _ :=
  Over.w x

/-- **The fixed points of the model Frobenius** (blueprint `lemma-frobenius-fixed-scheme--1`):
the rational points `x` of `X = X₀ ×_{k₀} k` fixed by `Φ_m` correspond, through
`x ↦ x ≫ p`, to the `k`-points of `X₀` over `k₀` fixed by the `m`-th power of the arithmetic
Frobenius `a ↦ a ^ #k₀` of `k`, that is to the points of `X₀` rational over `𝔽_{q^m}`. -/
noncomputable def IsModelFrobenius.fixedPointEquiv [Fintype k₀]
    (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ) : FixedPoint Φ m ≃
      f₀.fixedFieldPoints ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k) where
  toFun x := ⟨x.1.left ≫ p, by
    rw [Category.assoc, hΦ.isPullback.w, ← Category.assoc, rationalPoint_left_comp_hom]
    exact Category.id_comp _,
    (hΦ.comp_frobeniusIterate_left_eq_iff m x.1.left).1
      (congrArg CommaMorphism.left x.2)⟩
  invFun g := ⟨Over.homMk (hΦ.isPullback.lift g.1 (𝟙 _) (g.2.1.trans (Category.id_comp _).symm))
      (hΦ.isPullback.lift_snd _ _ _), by
    refine Over.OverMorphism.ext ?_
    refine (hΦ.comp_frobeniusIterate_left_eq_iff m
      (hΦ.isPullback.lift g.1 (𝟙 _) (g.2.1.trans (Category.id_comp _).symm))).2 ?_
    rw [IsPullback.lift_fst]
    exact g.2.2⟩
  left_inv x := Subtype.ext <| Over.OverMorphism.ext <| hΦ.isPullback.hom_ext
    (IsPullback.lift_fst _ _ _ _)
    ((IsPullback.lift_snd _ _ _ _).trans (rationalPoint_left_comp_hom x.1).symm)
  right_inv g := Subtype.ext (IsPullback.lift_fst _ _ _ _)

/-- The `m`-th power of the arithmetic Frobenius of `k` over `k₀` is `a ↦ a ^ (#k₀ ^ m)`. -/
lemma frobeniusAlgHom_pow_apply [Fintype k₀] (m : ℕ) (a : k) :
    ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k) a =
      a ^ (Nat.card k₀ ^ m) := by
  rw [Nat.card_eq_fintype_card]
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [AlgHom.coe_toRingHom] at ih ⊢
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
    simp only [← pow_mul, pow_succ]

/-- For `m ≥ 1` there are finitely many rational points of `X` fixed by `Φ_m` (blueprint
`lemma-frobenius-fixed-scheme--1`). -/
theorem IsModelFrobenius.finite_fixedPoint [IsAlgClosed k] [Finite k₀] [QuasiCompact f₀]
    [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : m ≠ 0) :
    Finite (FixedPoint Φ m) := by
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  have h := f₀.finite_fixedFieldPoints hm _ (frobeniusAlgHom_pow_apply (k := k) m)
  have : Finite (f₀.fixedFieldPoints
      ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k)) := h.to_subtype
  exact Finite.of_equiv _ (hΦ.fixedPointEquiv m).symm

/-- **Counting fixed points.** For a function `h` on the points of `X₀` and `m ≥ 1`, the sum of
`h` over the closed points of `X₀` underlying the rational points of `X` fixed by `Φ_m` is
`∑_{deg y ∣ m} deg y • h y`: a closed point `y` of degree `d ∣ m` carries exactly `d` fixed
points (blueprint `lemma-frobenius-fixed-scheme--1`). The sum may be taken over any finite set
`T` of closed points containing those of degree dividing `m`. -/
theorem IsModelFrobenius.sum_fixedPoint [IsAlgClosed k] [Finite k₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : m ≠ 0) [Fintype (FixedPoint Φ m)] {M : Type*}
    [AddCommMonoid M] (h : X₀ → M) {T : Finset X₀.finitePoints}
    (hT : ∀ y : X₀.finitePoints, f₀.degreeOver y.1 ∣ m → y ∈ T) :
    ∑ x : FixedPoint Φ m, h ((x.1.left ≫ p).base (default : Spec (.of k))) =
      ∑ y ∈ T with f₀.degreeOver y.1 ∣ m, f₀.degreeOver y.1 • h y.1 := by
  classical
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  let _ : Fintype (f₀.fixedFieldPoints
      ((FiniteField.frobeniusAlgHom k₀ k ^ m : k →ₐ[k₀] k) : k →+* k)) :=
    Fintype.ofEquiv _ (hΦ.fixedPointEquiv m)
  rw [← f₀.sum_fixedFieldPoints hm _ (frobeniusAlgHom_pow_apply (k := k) m) h hT]
  exact Fintype.sum_equiv (hΦ.fixedPointEquiv m) _ _ (fun _ ↦ rfl)

end AlgebraicGeometry.ProEtale.CondensedRing
