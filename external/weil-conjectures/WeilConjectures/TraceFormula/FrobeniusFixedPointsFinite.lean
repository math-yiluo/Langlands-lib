/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusTwistFixedPoints
public import WeilConjectures.Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# Finiteness of the points of degree `n + 1` for an automorphism of finite order

For an automorphism `e` of finite order of a scheme `X` of finite type over a finite field `k`,
the points of degree `n + 1` for the Frobenius twisted by `e`
(`ProEtale.CondensedRing.frobeniusFixedPoints e (n + 1)`) are finite: they are fixed by a power
`σ^N` of the geometric Frobenius of `Spec k̄`, hence factor through `Spec L` for the finite field
`L ⊆ k̄` fixed by `σ^N`, and there are only finitely many morphisms `Spec L ⟶ X`.

## Main statements

- `ProEtale.CondensedRing.finite_frobeniusFixedPoints_of_pow_eq_refl`.
- `ProEtale.CondensedRing.finite_frobeniusFixedPoints`, and the resulting `Fintype` structure
  `ProEtale.CondensedRing.fintypeFrobeniusFixedPoints` on the points of degree `n ≠ 0`.

-/

@[expose] public section

universe u

open CategoryTheory FiniteField

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] [Finite k]

/-- The `N`-th power of the geometric Frobenius of `Spec k̄` is `Spec` of the `N`-th power of the
geometric Frobenius of `k̄`. -/
lemma geometricFrobeniusField_hom_pow (N : ℕ) :
    (End.of (geometricFrobeniusField k).hom ^ N).asHom =
      Spec.map (CommRingCat.ofHom
        ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toRingEquiv.toRingHom) := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero, End.one_asHom]
    exact (Spec.map_id _).symm
  | succ N ih =>
    rw [pow_succ, End.mul_asHom, ih, geometricFrobeniusField_hom, ← Spec.map_comp]
    congr 1
    ext y
    simp [pow_succ', AlgEquiv.mul_apply]

/-- The `N`-th power of the geometric Frobenius is a `#k ^ N`-th root:
`(σ^N z) ^ (#k ^ N) = z`. -/
lemma geometricFrobenius_pow_apply_pow_card_pow (N : ℕ) (z : AlgebraicClosure k) :
    ((geometricFrobenius k (AlgebraicClosure k)) ^ N) z ^ (Nat.card k ^ N) = z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    rw [pow_succ (geometricFrobenius k (AlgebraicClosure k)) N, AlgEquiv.mul_apply,
      pow_succ (Nat.card k) N, pow_mul, ih, geometricFrobenius_pow_card]

/-- If the `N`-th power of the geometric Frobenius fixes `y`, then `y ^ (#k ^ N) = y`. -/
lemma pow_card_pow_eq_of_geometricFrobenius_pow (N : ℕ) (y : AlgebraicClosure k)
    (hy : ((geometricFrobenius k (AlgebraicClosure k)) ^ N) y = y) :
    y ^ (Nat.card k ^ N) = y := by
  conv_rhs => rw [← geometricFrobenius_pow_apply_pow_card_pow N y]
  rw [hy]

variable (k) in
/-- The subfield of `k̄` fixed by the `N`-th power of the geometric Frobenius. -/
noncomputable def geometricFrobeniusPowFixedField (N : ℕ) :
    IntermediateField k (AlgebraicClosure k) :=
  Subalgebra.toIntermediateField
    (AlgHom.equalizer ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toAlgHom
      (AlgHom.id k _))
    (fun y hy ↦ by
      change ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toAlgHom y⁻¹ = y⁻¹
      rw [map_inv₀]
      exact congrArg (·⁻¹) hy)

lemma mem_geometricFrobeniusPowFixedField {N : ℕ} {y : AlgebraicClosure k} :
    y ∈ geometricFrobeniusPowFixedField k N ↔
      ((geometricFrobenius k (AlgebraicClosure k)) ^ N) y = y :=
  Iff.rfl

/-- The field fixed by a positive power of the geometric Frobenius is finite. -/
lemma finite_geometricFrobeniusPowFixedField {N : ℕ} (hN : N ≠ 0) :
    Finite (geometricFrobeniusPowFixedField k N) := by
  let p : Polynomial (AlgebraicClosure k) := Polynomial.X ^ (Nat.card k ^ N) - Polynomial.X
  have hp : p ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero (AlgebraicClosure k) hN Finite.one_lt_card
  have hfin : {y : AlgebraicClosure k | p.IsRoot y}.Finite :=
    Polynomial.finite_setOfPred_isRoot hp
  refine Set.Finite.to_subtype (hfin.subset fun y hy ↦ ?_)
  change p.IsRoot y
  simp only [Polynomial.IsRoot.def, p, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [pow_card_pow_eq_of_geometricFrobenius_pow N y hy, sub_self]

/-- A geometric point `x : Spec k̄ ⟶ T` fixed by a power `σ^N` of the geometric Frobenius factors
through `Spec L` for the field `L ⊆ k̄` fixed by `σ^N`. -/
lemma exists_comp_eq_of_geometricFrobenius_pow {T : Scheme.{u}} (N : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ T)
    (hx : (End.of (geometricFrobeniusField k).hom ^ N).asHom ≫
      x = x) :
    ∃ g : Spec (.of (geometricFrobeniusPowFixedField k N)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap (geometricFrobeniusPowFixedField k N)
        (AlgebraicClosure k))) ≫ g = x := by
  set e := Scheme.SpecToEquivOfField (AlgebraicClosure k) T
  set F := ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toRingEquiv.toRingHom
  have hx' : x = Spec.map (e x).2 ≫ T.fromSpecResidueField (e x).1 := (e.left_inv x).symm
  have hfix : ∀ t, F ((e x).2 t) = (e x).2 t := by
    have h₁ : e.symm ⟨(e x).1, (e x).2 ≫ CommRingCat.ofHom F⟩ = e.symm (e x) := by
      change Spec.map ((e x).2 ≫ CommRingCat.ofHom F) ≫ T.fromSpecResidueField (e x).1 =
        Spec.map (e x).2 ≫ T.fromSpecResidueField (e x).1
      rw [Spec.map_comp, Category.assoc, ← hx', ← geometricFrobeniusField_hom_pow, hx]
    have h₂ := eq_of_heq (Sigma.ext_iff.mp (e.symm.injective h₁)).2
    intro t
    exact congrArg (fun φ ↦ φ t) (congrArg CommRingCat.Hom.hom h₂)
  let φ : T.residueField (e x).1 ⟶ .of (geometricFrobeniusPowFixedField k N) :=
    CommRingCat.ofHom ((e x).2.hom.codRestrict (geometricFrobeniusPowFixedField k N).toSubfield
      fun t ↦ hfix t)
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap (geometricFrobeniusPowFixedField k N)
      (AlgebraicClosure k)) = (e x).2 := by
    ext t
    rfl
  refine ⟨Spec.map φ ≫ T.fromSpecResidueField (e x).1, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hφ]
  exact e.left_inv x


/-- **Finiteness of the points of degree `n + 1`** for an automorphism `e` of finite order of a
scheme of finite type over a finite field (the finiteness part of blueprint
`lemma-frobenius-fixed-scheme--1`, for the Frobenius twisted by `e`): a point `x̄` with
`x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` is fixed by `σ^{(n+1)(m+1)}` when `e^{m+1} = 𝟙`, so it factors
through `Spec L` for the finite field `L` fixed by `σ^{(n+1)(m+1)}`. -/
theorem finite_frobeniusFixedPoints_of_pow_eq_refl {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (e : X ≅ X)
    (he : ∃ m : ℕ, e.pow (m + 1) = Iso.refl X) (n : ℕ) :
    Finite (frobeniusFixedPoints e (n + 1)) := by
  obtain ⟨m, hm⟩ := he
  set N := (n + 1) * (m + 1)
  have hN : N ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero n) (Nat.succ_ne_zero m)
  have hm' : End.of e.hom ^ (m + 1) = 1 := by
    apply End.ext
    rw [← Iso.pow_hom_eq_pow, hm]
    rfl
  have hA : (End.of (e.pow (n + 1)).hom.left ^ (m + 1)).asHom = 𝟙 X.left := by
    rw [Iso.pow_hom_eq_pow, ← Over.pow_left, ← pow_mul, mul_comm, pow_mul, hm', one_pow]
    rfl
  have hfix : ∀ x : frobeniusFixedPoints e (n + 1),
      (End.of (geometricFrobeniusField k).hom ^ N).asHom ≫
        x.1 = x.1 := by
    rintro ⟨y, -, hy⟩
    have h := End.comp_pow_eq_pow_comp y (End.of (e.pow (n + 1)).hom.left)
      (End.of ((geometricFrobeniusField k).pow (n + 1)).hom) hy (m + 1)
    rw [hA, Category.comp_id, Iso.pow_hom_eq_pow, ← pow_mul] at h
    exact h.symm
  have := finite_geometricFrobeniusPowFixedField (k := k) hN
  set L := geometricFrobeniusPowFixedField k N
  have := X.hom.finite_fieldPoints L
  choose g hg using fun x : frobeniusFixedPoints e (n + 1) ↦
    exists_comp_eq_of_geometricFrobenius_pow N x.1 (hfix x)
  have hg' : ∀ x : frobeniusFixedPoints e (n + 1),
      g x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    intro x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x ≫ X.hom)
    rw [← hφ]
    have h := x.2.1
    rw [← hg x, Category.assoc, ← hφ, ← Spec.map_comp, specAlgebraicClosure] at h
    have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    congr 1
    ext a
    exact congrArg (fun ψ ↦ ψ a) h'
  exact Finite.of_injective (β := X.hom.fieldPoints L) (fun x ↦ ⟨g x, hg' x⟩)
    fun x₁ x₂ h ↦ Subtype.ext (by
      rw [← hg x₁, ← hg x₂]
      exact congrArg (_ ≫ ·) (congrArg Subtype.val h))

/-- **Finiteness of the points of degree `n + 1`** of a separated scheme of finite type over a
finite field, for the Frobenius twisted by an automorphism `e` (the twisted analogue of the
finiteness part of blueprint `lemma-frobenius-fixed-scheme--1`, which is stated for the model
Frobenius, `ProEtale.CondensedRing.IsModelFrobenius.finite_fixedPoint`): a point `x̄` with
`x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` is fixed by `e^{n+1} ≫ Fr^{(q^{n+1})}`, since
`σ^{n+1} ≫ Fr^{(q^{n+1})} = 𝟙` on `Spec k̄`, and the fixed points of a Frobenius twisted by an
endomorphism are finite (`AlgebraicGeometry.Scheme.Hom.finite_fixedPoints_comp_absoluteFrobenius`).
-/
theorem finite_frobeniusFixedPoints {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (e : X ≅ X) (n : ℕ) :
    Finite (frobeniusFixedPoints e (n + 1)) := by
  have hg : (e.pow (n + 1)).hom.left ≫ X.hom = X.hom := Over.w (e.pow (n + 1)).hom
  have := X.hom.finite_fixedPoints_comp_absoluteFrobenius (e.pow (n + 1)).hom.left hg
    (M := n + 1) (Nat.succ_ne_zero n) (AlgebraicClosure k) (specAlgebraicClosure k)
  set σN := (geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1)
  have hσ : ((geometricFrobeniusField k).pow (n + 1)).hom =
      Spec.map (CommRingCat.ofHom σN.toRingEquiv.toRingHom) := by
    rw [Iso.pow_hom_eq_pow]
    exact geometricFrobeniusField_hom_pow (n + 1)
  let ρ : AlgebraicClosure k →+* AlgebraicClosure k := σN.symm.toRingEquiv.toRingHom
  have hρ (z : AlgebraicClosure k) : ρ z = z ^ (Nat.card k ^ (n + 1)) := by
    have h := geometricFrobenius_pow_apply_pow_card_pow (k := k) (n + 1) (σN.symm z)
    change σN (σN.symm z) ^ _ = σN.symm z at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  have hρσ : Spec.map (CommRingCat.ofHom σN.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ρ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext z
    exact σN.apply_symm_apply z
  refine Finite.of_injective (fun x : frobeniusFixedPoints e (n + 1) ↦
    (⟨x.1, x.2.1, ?_⟩ : {x : Spec (.of (AlgebraicClosure k)) ⟶ X.left //
      x ≫ X.hom = specAlgebraicClosure k ∧
        x ≫ (e.pow (n + 1)).hom.left ≫ X.hom.absoluteFrobenius (n + 1) = x}))
    fun x y h ↦ by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  obtain ⟨y, -, hy⟩ := x
  change y ≫ (e.pow (n + 1)).hom.left ≫ X.hom.absoluteFrobenius (n + 1) = y
  rw [hσ] at hy
  rw [← Category.assoc, hy, Category.assoc,
    X.hom.isFrobenius_absoluteFrobenius (n + 1) y (CommRingCat.ofHom ρ) hρ, reassoc_of% hρσ]

/-- The points of degree `n ≠ 0` form a finite type, with the `Fintype` structure chosen from
`finite_frobeniusFixedPoints`. It is not a global instance; enable it with
`attribute [local instance] fintypeFrobeniusFixedPoints` where sums over points are taken. -/
@[instance_reducible]
noncomputable def fintypeFrobeniusFixedPoints {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (e : X ≅ X) (n : ℕ)
    [NeZero n] : Fintype (frobeniusFixedPoints e n) :=
  have : Finite (frobeniusFixedPoints e n) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
    exact finite_frobeniusFixedPoints e m
  Fintype.ofFinite _

end AlgebraicGeometry.ProEtale.CondensedRing
