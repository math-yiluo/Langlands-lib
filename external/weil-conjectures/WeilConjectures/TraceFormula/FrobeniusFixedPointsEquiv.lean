/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite
public import WeilConjectures.ZetaSeries

/-!

# The points of degree `n + 1` for the identity are the `𝔽_{q^{n+1}}`-rational points

For a scheme `X` over a finite field `k = 𝔽_q`, the points of degree `n + 1` for the identity
(`ProEtale.CondensedRing.frobeniusFixedPoints (Iso.refl X) (n + 1)`) are the geometric points
`x̄ : Spec k̄ ⟶ X` over `Spec k` with `σ^{n+1} ≫ x̄ = x̄`. They are in bijection with the
`𝔽_{q^{n+1}}`-rational points of `X`: for the embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` chosen by
`IsAlgClosed.lift`, a rational point `y : Spec 𝔽_{q^{n+1}} ⟶ X` gives the geometric point
`Spec ι ≫ y`, and every point of degree `n + 1` factors uniquely in this way, since `ι` identifies
`𝔽_{q^{n+1}}` with the subfield of `k̄` fixed by `σ^{n+1}`.

## Main definitions

- `ProEtale.CondensedRing.fieldPointsEquivFrobeniusFixedPointsRefl`: the bijection
  `X(𝔽_{q^{n+1}}) ≃ frobeniusFixedPoints (Iso.refl X) (n + 1)`, with
  `ProEtale.CondensedRing.fieldPointsEquivFrobeniusFixedPointsRefl_apply_coe`: the geometric point
  of a rational point `y` is `Spec ι ≫ y`.

-/

@[expose] public section

universe u

open CategoryTheory FiniteField

namespace FiniteField.galoisExtension

variable (k : Type u) [Field k]

/-- The `k`-embedding `ι : 𝔽_{q^n} ↪ k̄` chosen by `IsAlgClosed.lift`. The trace function of a
Weil sheaf (`AlgebraicGeometry.WeilSheaf.traceFunction`) is taken at the geometric points
defined by this embedding. -/
noncomputable abbrev liftAlgebraicClosure (n : ℕ) :
    galoisExtension k n →ₐ[k] AlgebraicClosure k :=
  haveI : Module.IsTorsionFree k (galoisExtension k n) := Module.Flat.isTorsionFree
  IsAlgClosed.lift

end FiniteField.galoisExtension

namespace AlgebraicGeometry.ProEtale.CondensedRing

open FiniteField.galoisExtension

variable {k : Type u} [Field k] [Finite k]

/-- An element of `k̄` is fixed by the `N`-th power of the geometric Frobenius if and only if it
is fixed by `y ↦ y ^ (#k ^ N)`. -/
lemma geometricFrobenius_pow_apply_eq_iff (N : ℕ) (y : AlgebraicClosure k) :
    ((geometricFrobenius k (AlgebraicClosure k)) ^ N) y = y ↔ y ^ (Nat.card k ^ N) = y := by
  refine ⟨pow_card_pow_eq_of_geometricFrobenius_pow N y, fun hy ↦ ?_⟩
  let := Fintype.ofFinite k
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have := Fact.mk hp
  have : CharP (AlgebraicClosure k) (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective _
  have hinj : Function.Injective fun z : AlgebraicClosure k ↦ z ^ (Nat.card k ^ N) := by
    rw [Nat.card_eq_fintype_card, hm, ← pow_mul]
    exact iterateFrobenius_inj (AlgebraicClosure k) (ringChar k) (m * N)
  exact hinj ((geometricFrobenius_pow_apply_pow_card_pow N y).trans hy.symm)

/-- The number of elements of `𝔽_{q^{n+1}}`, as a `Fintype.card`. -/
private lemma fintype_card_galoisExtension (n : ℕ) [Fintype (galoisExtension k (n + 1))] :
    Fintype.card (galoisExtension k (n + 1)) = Nat.card k ^ (n + 1) := by
  rw [← Nat.card_eq_fintype_card, nat_card_galoisExtension k (n + 1) n.succ_ne_zero]

/-- The image of the embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` consists exactly of the elements of `k̄`
fixed by `σ^{n+1}`. -/
lemma geometricFrobenius_pow_apply_eq_iff_mem_range (n : ℕ) (y : AlgebraicClosure k) :
    ((geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1)) y = y ↔
      y ∈ Set.range (liftAlgebraicClosure k (n + 1)) := by
  have : Finite (galoisExtension k (n + 1)) := Module.finite_of_finite k
  let := Fintype.ofFinite (galoisExtension k (n + 1))
  rw [geometricFrobenius_pow_apply_eq_iff, ← fintype_card_galoisExtension n]
  exact pow_card_eq_self_iff_mem_range (liftAlgebraicClosure k (n + 1)).toRingHom

/-- The embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` chosen by `IsAlgClosed.lift` lands in the subfield fixed
by `σ^{n+1}`. -/
lemma geometricFrobenius_pow_lift_apply (n : ℕ) (a : galoisExtension k (n + 1)) :
    ((geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1)) (liftAlgebraicClosure k (n + 1) a) =
      liftAlgebraicClosure k (n + 1) a :=
  (geometricFrobenius_pow_apply_eq_iff_mem_range n _).2 ⟨a, rfl⟩

/-- An element of `k̄` fixed by `σ^{n+1}` is in the image of the embedding
`ι : 𝔽_{q^{n+1}} ↪ k̄`. -/
lemma mem_fieldRange_lift_of_geometricFrobenius_pow (n : ℕ) {y : AlgebraicClosure k}
    (hy : ((geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1)) y = y) :
    y ∈ (liftAlgebraicClosure k (n + 1)).fieldRange :=
  (geometricFrobenius_pow_apply_eq_iff_mem_range n y).1 hy

/-- `σ^{n+1}` acts trivially on `Spec 𝔽_{q^{n+1}}` through the embedding `ι` chosen by
`IsAlgClosed.lift`: `σ^{n+1} ≫ Spec ι = Spec ι`. -/
lemma geometricFrobeniusField_pow_hom_comp_specMap_lift (n : ℕ) :
    ((geometricFrobeniusField k).pow (n + 1)).hom ≫
        Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom) =
      Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom) := by
  rw [Iso.pow_hom_eq_pow, geometricFrobeniusField_hom_pow, ← Spec.map_comp]
  congr 1
  ext a
  exact geometricFrobenius_pow_lift_apply n a

/-- A geometric point `x : Spec k̄ ⟶ T` fixed by `σ^{n+1}` factors through `Spec ι` for the
embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` chosen by `IsAlgClosed.lift`. -/
lemma exists_specMap_lift_comp_eq {T : Scheme.{u}} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ T)
    (hx : ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x = x) :
    ∃ g : Spec (.of (galoisExtension k (n + 1))) ⟶ T,
      Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom) ≫ g = x := by
  rw [Iso.pow_hom_eq_pow] at hx
  obtain ⟨g, hg⟩ := exists_comp_eq_of_geometricFrobenius_pow (n + 1) x hx
  set ι := liftAlgebraicClosure k (n + 1)
  have hle : geometricFrobeniusPowFixedField k (n + 1) ≤ ι.fieldRange :=
    fun _ hy ↦ mem_fieldRange_lift_of_geometricFrobenius_pow n hy
  let ψ : geometricFrobeniusPowFixedField k (n + 1) →+* galoisExtension k (n + 1) :=
    ((AlgEquiv.ofInjectiveField ι).symm.toAlgHom.comp (IntermediateField.inclusion hle)).toRingHom
  have hψ : ι.toRingHom.comp ψ =
      algebraMap (geometricFrobeniusPowFixedField k (n + 1)) (AlgebraicClosure k) := by
    ext y
    change (ι ((AlgEquiv.ofInjectiveField ι).symm (IntermediateField.inclusion hle y)) : _) = y
    exact congrArg Subtype.val ((AlgEquiv.ofInjectiveField ι).apply_symm_apply _)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ g, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, hg]

/-- `Spec ι : Spec k̄ ⟶ Spec 𝔽_{q^n}` is an epimorphism of schemes, being faithfully flat. -/
instance epi_specMap_liftAlgebraicClosure (n : ℕ) :
    Epi (Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k n).toRingHom)) := by
  have h : (liftAlgebraicClosure k n).toRingHom.FaithfullyFlat := by
    algebraize [(liftAlgebraicClosure k n).toRingHom]
    exact inferInstanceAs (Module.FaithfullyFlat (galoisExtension k n) (AlgebraicClosure k))
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (liftAlgebraicClosure k n).toRingHom)).2 h
  exact Flat.epi_of_flat_of_surjective _

variable {X : Over (Spec (.of k))} (n : ℕ)

/-- The geometric point `Spec ι ≫ y` of an `𝔽_{q^{n+1}}`-rational point `y` of `X`, for the
embedding `ι` chosen by `IsAlgClosed.lift`, is a point of degree `n + 1` for the identity. -/
noncomputable def frobeniusFixedPointsReflOfFieldPoint
    (y : X.hom.fieldPoints (galoisExtension k (n + 1))) :
    frobeniusFixedPoints (Iso.refl X) (n + 1) :=
  ⟨Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom) ≫ y.1, by
    rw [Category.assoc, y.2, ← Spec.map_comp, specAlgebraicClosure]
    congr 1
    ext a
    exact (liftAlgebraicClosure k (n + 1)).commutes a, by
    rw [Iso.pow_refl, Iso.refl_hom, Over.id_left, Category.comp_id, ← Category.assoc,
      geometricFrobeniusField_pow_hom_comp_specMap_lift]⟩

/-- **The points of degree `n + 1` for the identity are the `𝔽_{q^{n+1}}`-rational points**: the
bijection `X(𝔽_{q^{n+1}}) ≃ frobeniusFixedPoints (Iso.refl X) (n + 1)`, `y ↦ Spec ι ≫ y`, for the
embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` chosen by `IsAlgClosed.lift`. A point of degree `n + 1` is fixed
by `σ^{n+1}`, so it factors through `Spec ι` (`exists_specMap_lift_comp_eq`), uniquely since
`Spec ι` is an epimorphism. -/
noncomputable def fieldPointsEquivFrobeniusFixedPointsRefl :
    X.hom.fieldPoints (galoisExtension k (n + 1)) ≃ frobeniusFixedPoints (Iso.refl X) (n + 1) :=
  Equiv.ofBijective (frobeniusFixedPointsReflOfFieldPoint n) (by
    refine ⟨fun y₁ y₂ h ↦ Subtype.ext ((cancel_epi _).1 (congrArg Subtype.val h)),
      fun ⟨x, hx₁, hx₂⟩ ↦ ?_⟩
    rw [Iso.pow_refl, Iso.refl_hom, Over.id_left, Category.comp_id] at hx₂
    obtain ⟨g, hg⟩ := exists_specMap_lift_comp_eq n x hx₂.symm
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    refine (cancel_epi
      (Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom))).1 ?_
    rw [← Category.assoc, hg, hx₁, ← Spec.map_comp, specAlgebraicClosure]
    congr 1
    ext a
    exact ((liftAlgebraicClosure k (n + 1)).commutes a).symm)

@[simp]
lemma fieldPointsEquivFrobeniusFixedPointsRefl_apply_coe
    (y : X.hom.fieldPoints (galoisExtension k (n + 1))) :
    (fieldPointsEquivFrobeniusFixedPointsRefl n y).1 =
      Spec.map (CommRingCat.ofHom (liftAlgebraicClosure k (n + 1)).toRingHom) ≫ y.1 :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
