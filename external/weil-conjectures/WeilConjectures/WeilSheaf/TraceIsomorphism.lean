/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.PoincareDualityLisse
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The trace isomorphism for the constant Weil sheaf

Let `k₀ = 𝔽_q` be a finite field, `ℓ ≠ p` a prime and `X₀` a smooth, separated, geometrically
connected `k₀`-scheme of finite type and pure dimension `d`, not necessarily proper. Write
`H_c^i = H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ)` and `H^i = H^i(X₀ ⊗ k̄, ℚ̄_ℓ)` for the cohomology of the constant
Weil sheaf, with its geometric Frobenius `F`, and `ℚ̄_ℓ(d)` for the Tate sheaf
(`AlgebraicGeometry.WeilSheaf.tateTwistSheaf`). Poincaré duality with constant coefficients says
that the pairings `H_c^i × H^{2d-i}(ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` are perfect and Frobenius-invariant, and in
top degree that the trace is an isomorphism

`tr_X : H_c^{2d}(ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ`, `tr_X^{(-d)} : H_c^{2d} ≅ ℚ̄_ℓ(-d)`,

so that `F` acts as the identity on `H⁰ ≅ ℚ̄_ℓ` and by `q^d` on `H_c^{2d}`. For `X₀` proper the
same holds for `H^{2d}`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.poincareDuality_compactlySupportedCohomology_adicConstant`
  (`corollary-degreewise-duality-over-fields--1`): the perfect pairings, their line-valued form, and
  the top degree `H_c^{2d}(ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ`, `H_c^{2d} ≅ ℚ̄_ℓ(-d)`, also with `H` for `X₀` proper.
- `AlgebraicGeometry.WeilSheaf.traceIsomorphism_adicConstant`
(`theorem-trace-isomorphism-top-degree`): the
  trace isomorphisms with the Frobenius actions `F = id` on `H⁰` and `F = q^d` on `H_c^{2d}`, and
  on `H^{2d}` for `X₀` proper.

## Implementation notes

*Existential form.* The trace map `tr_X` of `corollary-cup-product-pairing--1` is defined in the
repository only for étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.TateOrientation.traceMap`, see
`WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` for its bijectivity at the
finite stage); Weil complexes have no `Ra^!`, orientation or derived tensor product of
complexes yet. As in `WeilConjectures.WeilSheaf.PoincareDuality`, the statements are therefore
existential: there are Frobenius-compatible perfect pairings and isomorphisms `H_c^{2d} ≅ ℚ̄_ℓ`
on which `F` acts as asserted. The value line `ℚ̄_ℓ(-d)` is `ℚ̄_ℓ` with `F` acting by `q^d`.

*Coefficients.* The blueprint states the field-stage results for `E` and `ℚ̄_ℓ`; Weil sheaves
in the repository have coefficients `ℚ̄_ℓ`, so only the stage `ℚ̄_ℓ` is stated.

*Ingredients.* The degreewise perfectness of another subsection, in the form needed,
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`,
is the case `F = ℚ̄_ℓ` of the lisse statement
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`, since
`ℚ̄_ℓ^∨(d) ≅ ℚ̄_ℓ(d)`
(`corollary-degreewise-duality-over-fields--1`, with the Frobenius invariance of
`theorem-poincare-duality-frobenius`). The other inputs are the clauses of
`prop-cohomological-finiteness` (`WeilConjectures.WeilSheaf.Finiteness`), put in the form needed:
`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_zero_adicConstant` (`H⁰ ≅ ℚ̄_ℓ` with
`F = id`) and `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_cohomology`
(`H_c = H` for `X₀` proper). The twist `ℚ̄_ℓ(m)` multiplies `F` by `q^{-m}`
on cohomology and compactly supported cohomology
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_tateTwistSheaf` and
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_tateTwistSheaf`,
`prose-10-21`). The two nodes are deduced from these by linear algebra.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

section Ingredients

/-- Blueprint `theorem-trace-isomorphism-top-degree--1` (connectedness clause,
`lemma-perfect-complexes-geometric-point`): for `X₀` separated, of finite type and geometrically
connected over `k₀`, `H⁰(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` and the geometric Frobenius acts on it as the
identity. Neither properness nor smoothness is needed. -/
theorem exists_linearEquiv_cohomology_zero_adicConstant
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ e : ((adicConstant k₀ l X).cohomology 0).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
      ∀ z, e (((adicConstant k₀ l X).cohomology 0).frobenius z) = e z :=
  have h := finrank_cohomology_zero_adicConstant k₀ l X
  ⟨LinearEquiv.ofFinrankEq _ _ (by rw [h, Module.finrank_self]), fun z ↦ by
    rw [frobenius_cohomology_zero_adicConstant k₀ l X, LinearEquiv.refl_apply]⟩

/-- Blueprint `corollary-degreewise-duality-over-fields--1` (for `K = ℚ̄_ℓ`, so that
`K^∨(d) = ℚ̄_ℓ(d)`), with the Frobenius invariance of `theorem-poincare-duality-frobenius` (a): for
`X₀` smooth, separated, of finite type and pure dimension `d` over `k₀`, the degreewise Poincaré
pairings `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ) × H^j(X₀ ⊗ k̄, ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius. Properness is not needed. -/
theorem exists_isPerfPair_compactlySupportedCohomology_adicConstant (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : ((adicConstant k₀ l X).compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        ((tateTwistSheaf k₀ l X d).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P (((adicConstant k₀ l X).compactlySupportedCohomology i).frobenius x)
        (((tateTwistSheaf k₀ l X d).cohomology j).frobenius y) = P x y := by
  have hA := isLisse_adicConstant k₀ l X
  obtain ⟨P, hP, hPF⟩ := exists_isPerfPair_compactlySupportedCohomology_dual d hA i j h
  -- `ℚ̄_ℓ(d) ≅ (ℚ̄_ℓ)^∨(d)`: both are `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵈ}`
  let e : tateTwistSheaf k₀ l X d ≅
      ((adicConstant k₀ l X).dual hA).constantTwist (cyclotomicUnit k₀ l ^ d) :=
    ObjectProperty.isoMk _ (tateTwistSheafObjIso k₀ l X d ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (by simp) _ ≪≫
      (ProEtaleWeilSheaf.constantTwistObjConstantTwistIso 1⁻¹ (cyclotomicUnit k₀ l ^ d) _).symm ≪≫
      (ProEtaleWeilSheaf.constantTwist k₀ l X _).mapIso
        (dualObjIsoOfIso _ hA (ProEtaleWeilSheaf.constantTwistOneObjIso _).symm).symm ≪≫
      (constantTwistObjIso _ _).symm)
  let E := cohomologyEquivOfIso e j
  refine ⟨P.compl₁₂ (LinearEquiv.refl _ _).toLinearMap E.toLinearEquiv.toLinearMap,
    LinearMap.IsPerfPair.compl₁₂ (p := P) (LinearEquiv.refl _ _) E.toLinearEquiv, fun x y ↦ ?_⟩
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
  rw [E.map_frobenius, hPF]

end Ingredients

section Proper

variable (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]
  [IsProper (Y ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `prop-cohomological-finiteness` (proper clause,
`proposition-forgetting-supports-composition--3`): for `X₀` proper over `k₀`, the canonical
comparison `H_cʳ(X₀ ⊗ k̄, F) ≅ Hʳ(X₀ ⊗ k̄, F)` of `Ra_! ≅ Ra_*` is Frobenius-equivariant. -/
theorem nonempty_equiv_compactlySupportedCohomology_cohomology (F : WeilSheaf k₀ l Y) (r : ℤ) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv (F.cohomology r)) :=
  WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology (toComplex.obj F) r

end Proper

section LinearAlgebra

variable {k₀ l X}

/-- Transport of a Frobenius-compatible isomorphism `M ≅ ℚ̄_ℓ`, on which Frobenius acts by `c`,
along an isomorphism of Frobenius modules `N ≅ M`. -/
private lemma exists_linearEquiv_of_equiv {M N : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)}
    (E : N.Equiv M) {c : PadicAlgCl l}
    (h : ∃ tr : M.carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l, ∀ z, tr (M.frobenius z) = c * tr z) :
    ∃ tr : N.carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l, ∀ z, tr (N.frobenius z) = c * tr z := by
  obtain ⟨tr, htr⟩ := h
  exact ⟨E.toLinearEquiv.trans tr, fun z ↦ by simp [E.map_frobenius, htr]⟩

/-- The Frobenius of the Tate twist `M(m)` is `q^{-m}` times that of `M`. -/
private lemma frobenius_tateTwist_apply {M : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)} {q : ℕ}
    (hq : q ≠ 0) (m : ℤ) (x : M.carrier) :
    (M.tateTwist q m).frobenius x = ((q : PadicAlgCl l) ^ (-m)) • M.frobenius x :=
  FrobeniusModule.frobeniusEnd_rescale_apply (zpow_ne_zero _ (Nat.cast_ne_zero.2 hq)) x

/-- Transport along a Tate twist: if Frobenius acts by `c` on `M ≅ ℚ̄_ℓ`, it acts by `q^{-m} * c`
on the twisted `N ≅ M(m)`. -/
private lemma exists_linearEquiv_of_equiv_tateTwist
    {M N : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)} {q : ℕ} (hq : q ≠ 0) (m : ℤ)
    (E : N.Equiv (M.tateTwist q m)) {c : PadicAlgCl l}
    (h : ∃ tr : M.carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l, ∀ z, tr (M.frobenius z) = c * tr z) :
    ∃ tr : N.carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (N.frobenius z) = ((q : PadicAlgCl l) ^ (-m) * c) * tr z := by
  obtain ⟨tr, htr⟩ := h
  refine ⟨E.toLinearEquiv.trans tr, fun z ↦ ?_⟩
  have h₁ : (E.toLinearEquiv (N.frobenius z) : M.carrier) =
      ((q : PadicAlgCl l) ^ (-m)) • M.frobenius (E.toLinearEquiv z) :=
    (E.map_frobenius z).trans (frobenius_tateTwist_apply hq m _)
  change tr (E.toLinearEquiv (N.frobenius z)) = _ * tr (E.toLinearEquiv z)
  rw [h₁, map_smul, htr, smul_eq_mul, mul_assoc]

end LinearAlgebra

variable (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- The multiplier `q^d` by which Frobenius acts on `ℚ̄_ℓ(-d)`. -/
local notation "𝐪" => (Nat.card k₀ : PadicAlgCl l) ^ d

/-- The top-degree trace isomorphism `H_c^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)`: Frobenius acts on it by
`q^d`. -/
private lemma exists_linearEquiv_compactlySupportedCohomology_two_mul :
    ∃ tr : ((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l]
        PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).frobenius z) =
        𝐪 * tr z := by
  have hq : (Nat.card k₀ : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨P, hP, hPF⟩ :=
    exists_isPerfPair_compactlySupportedCohomology_adicConstant k₀ l X d (2 * d) 0 (add_zero _)
  obtain ⟨E⟩ := nonempty_equiv_cohomology_tateTwistSheaf k₀ l X d 0
  obtain ⟨e, he⟩ := exists_linearEquiv_cohomology_zero_adicConstant k₀ l X
  -- `e' : H⁰(ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ`, on which Frobenius acts by `q^{-d}`
  obtain ⟨e', he'⟩ := exists_linearEquiv_of_equiv_tateTwist (Nat.card_pos.ne') (d : ℤ) E
    ⟨e, fun z ↦ by rw [he, one_mul]⟩
  set u := e'.symm 1
  have hu : ((tateTwistSheaf k₀ l X d).cohomology 0).frobenius u =
      ((Nat.card k₀ : PadicAlgCl l) ^ (-(d : ℤ))) • u := by
    apply e'.injective
    rw [he', map_smul, mul_one, smul_eq_mul, mul_comm]
  refine ⟨P.toPerfPair.trans (e'.symm.dualMap.trans (LinearMap.ringLmapEquivSelf _ _ _)),
    fun z ↦ ?_⟩
  have key := hPF z u
  rw [hu, map_smul, smul_eq_mul] at key
  have h₂ : (Nat.card k₀ : PadicAlgCl l) ^ (-(d : ℤ)) * 𝐪 = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq)]
  change P _ u = 𝐪 * P z u
  rw [← key, ← mul_assoc, mul_comm 𝐪, h₂, one_mul]

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Constant coefficients.

Let `X₀` be smooth, separated, of finite type and geometrically connected of pure dimension `d`
over `k₀ = 𝔽_q`, not necessarily proper, and write `H_c^i`, `H^i` for the cohomology of
`X₀ ⊗ k̄` with coefficients `ℚ̄_ℓ`, with geometric Frobenius `F`. Then:

1. Poincaré duality is a perfect Frobenius-invariant pairing
   `H_c^i × H^j(ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` for `i + j = 2d`;
2. equivalently, the line-valued pairing `H_c^i × H^j ⟶ ℚ̄_ℓ(-d)` is perfect: on its target
   Frobenius acts by `q^d`, `⟨F x, F y⟩ = q^d ⟨x, y⟩`;
3. in top degree, `H_c^{2d}(ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ`, Frobenius acting as the identity, and
4. `H_c^{2d} ≅ ℚ̄_ℓ(-d)`, Frobenius acting by `q^d`;
5. if `X₀` is proper, the same holds with `H_c` replaced by `H`.

See the module docstring for the existential form. -/
theorem poincareDuality_compactlySupportedCohomology_adicConstant :
    (∀ (i j : ℤ) (_ : i + j = 2 * d),
      ∃ P : ((adicConstant k₀ l X).compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
          ((tateTwistSheaf k₀ l X d).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
        P.IsPerfPair ∧
          ∀ x y, P (((adicConstant k₀ l X).compactlySupportedCohomology i).frobenius x)
            (((tateTwistSheaf k₀ l X d).cohomology j).frobenius y) = P x y) ∧
    (∀ (i j : ℤ) (_ : i + j = 2 * d),
      ∃ P : ((adicConstant k₀ l X).compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
          ((adicConstant k₀ l X).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
        P.IsPerfPair ∧
          ∀ x y, P (((adicConstant k₀ l X).compactlySupportedCohomology i).frobenius x)
            (((adicConstant k₀ l X).cohomology j).frobenius y) = 𝐪 * P x y) ∧
    (∃ tr : ((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).frobenius z) =
        tr z) ∧
    (∃ tr : ((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).frobenius z) =
        𝐪 * tr z) ∧
    (IsProper (X ↘ Spec (CommRingCat.of k₀)) →
      (∃ tr : ((tateTwistSheaf k₀ l X d).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l]
          PadicAlgCl l,
        ∀ z, tr (((tateTwistSheaf k₀ l X d).cohomology (2 * d)).frobenius z) = tr z) ∧
      ∃ tr : ((adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
        ∀ z, tr (((adicConstant k₀ l X).cohomology (2 * d)).frobenius z) = 𝐪 * tr z) := by
  have hq : (Nat.card k₀ : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hqd : (Nat.card k₀ : PadicAlgCl l) ^ (-(d : ℤ)) * 𝐪 = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq)]
  have htop := exists_linearEquiv_compactlySupportedCohomology_two_mul k₀ l X d
  -- the twisted top degree: Frobenius acts by `q^{-d} * q^d = 1`
  have htw : ∃ tr : ((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
      PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).frobenius z) =
        tr z := by
    obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_tateTwistSheaf k₀ l X d (2 * d)
    obtain ⟨tr, htr⟩ := exists_linearEquiv_of_equiv_tateTwist (Nat.card_pos.ne') (d : ℤ) E htop
    exact ⟨tr, fun z ↦ by rw [htr, hqd, one_mul]⟩
  refine ⟨fun i j h ↦ exists_isPerfPair_compactlySupportedCohomology_adicConstant k₀ l X d i j h,
    fun i j h ↦ ?_, htw, htop, fun hX ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨P, hP, hPF⟩ := exists_isPerfPair_compactlySupportedCohomology_adicConstant k₀ l X d
      i j h
    obtain ⟨E⟩ := nonempty_equiv_cohomology_tateTwistSheaf k₀ l X d j
    refine ⟨P.compl₁₂ (LinearEquiv.refl _ _).toLinearMap E.toLinearEquiv.symm.toLinearMap,
      inferInstance, fun x y ↦ ?_⟩
    -- `E⁻¹ (F y) = q^d • F (E⁻¹ y)`, since `E` multiplies Frobenius by `q^{-d}`
    have hE : E.toLinearEquiv.symm (((adicConstant k₀ l X).cohomology j).frobenius y) =
        𝐪 • ((tateTwistSheaf k₀ l X d).cohomology j).frobenius (E.toLinearEquiv.symm y) := by
      have h₁ : (E.toLinearEquiv (((tateTwistSheaf k₀ l X d).cohomology j).frobenius
          (E.toLinearEquiv.symm y)) : ((adicConstant k₀ l X).cohomology j).carrier) =
          ((Nat.card k₀ : PadicAlgCl l) ^ (-(d : ℤ))) •
            ((adicConstant k₀ l X).cohomology j).frobenius y := by
        refine (E.map_frobenius _).trans ((frobenius_tateTwist_apply Nat.card_pos.ne' _ _).trans ?_)
        rw [LinearEquiv.apply_symm_apply]
      apply E.toLinearEquiv.injective
      rw [LinearEquiv.apply_symm_apply, map_smul]
      erw [h₁]
      rw [smul_smul, mul_comm, hqd, one_smul]
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
    erw [hE]
    rw [map_smul, hPF, smul_eq_mul]
    rfl
  · have := hX
    obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_cohomology k₀ l X
      (tateTwistSheaf k₀ l X d) (2 * d)
    simpa using exists_linearEquiv_of_equiv (E := ⟨E.toLinearEquiv.symm, fun z ↦ by
      apply E.toLinearEquiv.injective
      rw [E.map_frobenius, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩)
      (c := 1) (by simpa using htw)
  · have := hX
    obtain ⟨E⟩ := nonempty_equiv_compactlySupportedCohomology_cohomology k₀ l X
      (adicConstant k₀ l X) (2 * d)
    exact exists_linearEquiv_of_equiv (E := ⟨E.toLinearEquiv.symm, fun z ↦ by
      apply E.toLinearEquiv.injective
      rw [E.map_frobenius, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩) htop

/-- Blueprint `theorem-trace-isomorphism-top-degree`: Trace isomorphism.

Let `X₀` be smooth, separated, of finite type and geometrically connected of pure dimension `d`
over `k₀ = 𝔽_q`, not necessarily proper. With coefficients `ℚ̄_ℓ` and geometric Frobenius `F`:

1. `H⁰(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, `F` acting as the identity;
2. the trace `tr_X : H_c^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ` is an isomorphism, `F` acting as the
   identity;
3. its untwisted form `tr_X^{(-d)} : H_c^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)` is an isomorphism, `F`
   acting by `q^d`;
4. if `X₀` is proper, `H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)`, `F` acting by `q^d`.

See the module docstring for the existential form. -/
theorem traceIsomorphism_adicConstant :
    (∃ e : ((adicConstant k₀ l X).cohomology 0).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
      ∀ z, e (((adicConstant k₀ l X).cohomology 0).frobenius z) = e z) ∧
    (∃ tr : ((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).frobenius z) =
        tr z) ∧
    (∃ tr : ((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).frobenius z) =
        𝐪 * tr z) ∧
    (IsProper (X ↘ Spec (CommRingCat.of k₀)) →
      ∃ tr : ((adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
        ∀ z, tr (((adicConstant k₀ l X).cohomology (2 * d)).frobenius z) = 𝐪 * tr z) := by
  obtain ⟨-, -, htw, htop, hprop⟩ :=
    poincareDuality_compactlySupportedCohomology_adicConstant k₀ l X d
  exact ⟨exists_linearEquiv_cohomology_zero_adicConstant k₀ l X, htw, htop,
    fun h ↦ (hprop h).2⟩

/-- Blueprint `theorem-poincare-duality--6`: Poincaré duality over `ℚ̄_ℓ`, for the constant
sheaf. Let `X₀` be smooth, separated, of finite type and geometrically connected of pure
dimension `d` over `k₀ = 𝔽_q`, and `F` the geometric Frobenius. Over `ℚ̄_ℓ`:

1. the degreewise Poincaré pairings `H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ) × H^j(X₀ ⊗ k̄, ℚ̄_ℓ) ⟶ ℚ̄_ℓ(-d)`,
   `i + j = 2d`, are perfect, with the Frobenius similitude `⟨F x, F y⟩ = q^d ⟨x, y⟩` of
   `theorem-poincare-duality-frobenius--4`;
2. the trace `tr_X : H_c^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ(d)) ≅ ℚ̄_ℓ` is an isomorphism, Frobenius-invariant;
3. the untwisted trace `H_c^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)` is an isomorphism, `F` acting by
   `q^d`; for `X₀` proper the same holds for `H^{2d}`.

In the existential form of this file, these are clauses of
`AlgebraicGeometry.WeilSheaf.poincareDuality_compactlySupportedCohomology_adicConstant`.
The statement asserts that *some* perfect pairing with the Frobenius similitude exists, not that
the Poincaré pairing (cup product followed by the trace) is perfect: it only repackages the
existential statement `poincareDuality_compactlySupportedCohomology_adicConstant`. -/
theorem exists_isPerfPair_similitude_adicConstant :
    (∀ (i j : ℤ) (_ : i + j = 2 * d),
      ∃ P : ((adicConstant k₀ l X).compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
          ((adicConstant k₀ l X).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
        P.IsPerfPair ∧
          ∀ x y, P (((adicConstant k₀ l X).compactlySupportedCohomology i).frobenius x)
            (((adicConstant k₀ l X).cohomology j).frobenius y) = 𝐪 * P x y) ∧
    (∃ tr : ((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((tateTwistSheaf k₀ l X d).compactlySupportedCohomology (2 * d)).frobenius z) =
        tr z) ∧
    (∃ tr : ((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).carrier ≃ₗ[
        PadicAlgCl l] PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).compactlySupportedCohomology (2 * d)).frobenius z) =
        𝐪 * tr z) ∧
    (IsProper (X ↘ Spec (CommRingCat.of k₀)) →
      ∃ tr : ((adicConstant k₀ l X).cohomology (2 * d)).carrier ≃ₗ[PadicAlgCl l] PadicAlgCl l,
        ∀ z, tr (((adicConstant k₀ l X).cohomology (2 * d)).frobenius z) = 𝐪 * tr z) := by
  obtain ⟨-, hP, htw, htop, hprop⟩ :=
    poincareDuality_compactlySupportedCohomology_adicConstant k₀ l X d
  exact ⟨hP, htw, htop, fun h ↦ (hprop h).2⟩

end WeilSheaf

end AlgebraicGeometry
