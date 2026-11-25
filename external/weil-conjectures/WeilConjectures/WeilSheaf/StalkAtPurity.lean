/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.UpperStarPointwise

/-!
# Purity at geometric points fixed by a power of the Frobenius

Let `X₀` be a scheme over a finite field `k` with `q` elements, `X = X₀ ×_k k̄` its geometric
fiber, `g_X` its geometric Galois Frobenius and `σ` the geometric Frobenius of `Spec k̄`. Let
`s : Spec k̄ ⟶ X` be a geometric point with `s ≫ g_Xᵐ = σᵐ ≫ s` for some `m ≥ 1`, lying over the
point `x` of `X₀`.

- The point `x` is a closed point of degree dividing `m`
  (`Scheme.Hom.mem_finitePoints_and_degreeOver_dvd_of_geometricGaloisFrobenius_pow`):
  the embedding `κ(x) ↪ k̄` given by `s` is invariant under `σᵐ`, so it lands in the field of
  the elements `a` with `a ^ (qᵐ) = a`.
- The stalk `F_s` with the local Frobenius `F_x^{(m)}` is pure of weight `w` relative to `qᵐ`
  exactly when the stalk at `x` is pure of weight `w` relative to `q_x = q ^ deg x`
  (`AlgebraicGeometry.WeilSheaf.isPureOfWeight_stalk_iff_stalkAt`): `F_x^{(m)}` has the
  characteristic polynomial of `F_x ^ (m / deg x)`. This is "the same power calculation at `x`"
  of blueprint `theorem-real-constructible-sheaves-are-mixed--1`, which allows to test punctual
  purity at any geometric point fixed by a power of the Frobenius
  (`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.stalkAt`,
  `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_of_forall_stalkAt`).
-/

@[expose] public section

universe u

open CategoryTheory

/-! ### General facts on finite fields -/

namespace FiniteField

/-- A field extension `L` of a finite field `K` with `q` elements in which every element
satisfies `a ^ (qᵐ) = a`, `m ≥ 1`, is finite of degree dividing `m`: its elements are roots of
the nonzero polynomial `X ^ (qᵐ) - X`, and the `m`-th power of the arithmetic Frobenius of `L/K`,
whose order is `[L : K]`, is the identity. -/
theorem finite_and_finrank_dvd_of_forall_pow_card_pow_eq_self (K L : Type*) [Field K] [Fintype K]
    [Field L] [Algebra K L] {m : ℕ} (hm : 0 < m) (h : ∀ a : L, a ^ (Fintype.card K ^ m) = a) :
    Finite L ∧ Module.finrank K L ∣ m := by
  have hfin : Finite L := by
    refine Set.finite_univ_iff.1 ((Polynomial.finite_setOfPred_isRoot
      (FiniteField.X_pow_card_pow_sub_X_ne_zero L hm.ne' (Fintype.one_lt_card (α := K)))).subset
      fun a _ ↦ ?_)
    simp [Polynomial.IsRoot, h a]
  refine ⟨hfin, ?_⟩
  rw [← orderOf_frobeniusAlgHom K L]
  refine orderOf_dvd_of_pow_eq_one (AlgHom.ext fun a ↦ ?_)
  rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply]
  exact h a

end FiniteField

/-! ### Points under geometric points fixed by a power of the Frobenius -/

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `s : Spec k̄ ⟶ X₀ ×_k k̄` be a geometric point fixed by a positive power of the
geometric Galois Frobenius up to reparametrisation, `s ≫ g_Xᵐ = σᵐ ≫ s`, `m ≥ 1`. Then the
point `x` of `X₀` under `s` has finite residue field, of degree `[κ(x) : k]` dividing `m`.

Indeed, `s ≫ pr` is invariant under `σᵐ`, as `g_Xᵐ ≫ pr = pr`. Writing
`s ≫ pr = Spec ι₀ ≫ (Spec κ(x) ⟶ X₀)` for an embedding `ι₀ : κ(x) ↪ k̄`, this says that the
image of `ι₀` is fixed by the `m`-th power of the geometric Frobenius of `k̄`, so that every
element `a` of `κ(x)` satisfies `a ^ (qᵐ) = a`. -/
theorem mem_finitePoints_and_degreeOver_dvd_of_geometricGaloisFrobenius_pow
    (s : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber) {m : ℕ} (hm : 0 < m)
    (hs : s ≫ (f.geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k ^ m).asIso.hom ≫ s) :
    (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) ∈ X.finitePoints ∧
      f.degreeOver ((s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _)) ∣ m := by
  let := Fintype.ofFinite k
  set x := (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _)
  obtain ⟨ι₀, hι₀⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField _ x rfl
  have hinv : (specGeometricFrobenius k ^ m).asIso.hom ≫ s ≫ f.geometricFiberProj =
      s ≫ f.geometricFiberProj := by
    rw [← Category.assoc, ← hs, Category.assoc,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  rw [hι₀, specGeometricFrobenius_pow_hom, ← Category.assoc, ← Spec.map_comp,
    cancel_mono, Spec.map_inj] at hinv
  have hfix (a : X.residueField x) :
      a ^ (Fintype.card k ^ m) = a := by
    refine ι₀.hom.injective ?_
    have ha : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)
        (ι₀.hom a) = ι₀.hom a := congrArg (fun φ ↦ φ.hom a) hinv
    rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at ha
    rw [map_pow]
    exact ha.symm
  let := (f.residueFieldAlgebraMap x).toAlgebra
  exact FiniteField.finite_and_finrank_dvd_of_forall_pow_card_pow_eq_self k _ hm hfix

end AlgebraicGeometry.Scheme.Hom

/-! ### Purity at geometric points fixed by a power of the Frobenius -/

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **Purity can be tested at any geometric point fixed by a power of the Frobenius.** Let `s`
be a geometric point with `s ≫ g_Xᵐ = σᵐ ≫ s`, `m ≥ 1`, over the closed point `x`. Then the
stalk `F_s` with the local Frobenius `F_x^{(m)}` is pure of weight `w` relative to `qᵐ` if and
only if the stalk `F_x̄` with `F_x` is pure of weight `w` relative to `q_x = q ^ deg x`.

Indeed `deg x ∣ m`, and `F_x^{(m)}` has the characteristic polynomial of `F_x ^ (m / deg x)`
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalkAt_of_dvd`), while
`qᵐ = q_x ^ (m / deg x)`: purity of `F_x` is purity of its `r`-th power relative to `q_xʳ`.
This is "the same power calculation at `x`" of blueprint
`theorem-real-constructible-sheaves-are-mixed--1`. -/
theorem isPureOfWeight_stalk_iff_stalkAt (F : WeilSheaf k₀ l X) (ι : PadicAlgCl l →+* ℂ)
    (w : ℝ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {m : ℕ} (hm : 0 < m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (x : X.finitePoints)
    (hx : (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint _) = x.1) :
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w ↔
      (F.stalkAt s m hs).IsPureOfWeight ι (Nat.card k₀ ^ m) w := by
  have hx₁ :=
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base x
  have hdvd :=
    (Scheme.Hom.mem_finitePoints_and_degreeOver_dvd_of_geometricGaloisFrobenius_pow _ s hm hs).2
  rw [hx] at hdvd
  have hd := Scheme.Hom.degreeOver_ne_zero (X ↘ Spec (CommRingCat.of k₀)) x.2
  have h := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ s (hx₁.trans hx.symm) (hx₁ ▸ x.2) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x) hs
  have hq : Nat.card k₀ ^ m = (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 ^
      (m / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) := by
    rw [Scheme.Hom.residueCard, ← pow_mul, Nat.mul_div_cancel' hdvd]
  rw [hq]
  exact FrobeniusModule.isPureOfWeight_iff_of_charpoly_eq_pow
    (Nat.div_pos (Nat.le_of_dvd hm hdvd) (Nat.pos_of_ne_zero hd)) h

/-- A punctually pure Weil sheaf of weight `w` is pure of weight `w` relative to `qᵐ` at every
geometric point `s` with `s ≫ g_Xᵐ = σᵐ ≫ s`, `m ≥ 1`: the point under `s` is a closed point,
at which `AlgebraicGeometry.WeilSheaf.isPureOfWeight_stalk_iff_stalkAt` applies. -/
theorem IsPunctuallyPureOfWeight.stalkAt {F : WeilSheaf k₀ l X} {ι : PadicAlgCl l →+* ℂ}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {m : ℕ} (hm : 0 < m)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).IsPureOfWeight ι (Nat.card k₀ ^ m) w :=
  (isPureOfWeight_stalk_iff_stalkAt F ι w s hm hs ⟨_,
    (Scheme.Hom.mem_finitePoints_and_degreeOver_dvd_of_geometricGaloisFrobenius_pow _ s hm
      hs).1⟩ rfl).1 (h _)

/-- A Weil sheaf is punctually pure of weight `w` as soon as, over every closed point `x`, there
is some geometric point `s` with `s ≫ g_Xᵐ = σᵐ ≫ s`, `m ≥ 1`, at which `F_s` with `F_x^{(m)}`
is pure of weight `w` relative to `qᵐ`
(`AlgebraicGeometry.WeilSheaf.isPureOfWeight_stalk_iff_stalkAt`). -/
theorem isPunctuallyPureOfWeight_of_forall_stalkAt {F : WeilSheaf k₀ l X}
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    (h : ∀ x : X.finitePoints, ∃ (s : Spec (.of (AlgebraicClosure k₀)) ⟶
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (m : ℕ) (_ : 0 < m)
      (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
        (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s),
      (s ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint _) = x.1 ∧
      (F.stalkAt s m hs).IsPureOfWeight ι (Nat.card k₀ ^ m) w) :
    F.IsPunctuallyPureOfWeight ι w := fun x ↦ by
  obtain ⟨s, m, hm, hs, hx, hpure⟩ := h x
  exact (isPureOfWeight_stalk_iff_stalkAt F ι w s hm hs x hx).2 hpure

end AlgebraicGeometry.WeilSheaf
