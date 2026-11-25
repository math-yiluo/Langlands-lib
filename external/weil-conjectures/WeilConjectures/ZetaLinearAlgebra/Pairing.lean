/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Eigenvalues of a similitude pair under a perfect pairing

Let `p : V →ₗ[L] W →ₗ[L] L` be a perfect pairing of finite dimensional vector spaces over a
field `L` and let `F : End L V`, `G : End L W` be a *similitude pair* with multiplier `c ≠ 0`,
i.e. `p (F v) (G w) = c * p v w` for all `v` and `w`. This file shows that the eigenvalues of
`F` and `G` correspond to each other by `λ ↦ c / λ`. This is the linear algebra behind the
functional equation of the zeta function of a smooth proper variety over a finite field, where
the pairing is Poincaré duality and `c = qᵈ`.

## Main declarations

* `LinearMap.injective_of_similitude`, `LinearMap.injective_right_of_similitude`: both members
  of a similitude pair are automatically injective, hence bijective.
* `LinearMap.dualMap_mul_conj_of_similitude`,
  `LinearMap.charpoly_eq_smul_inverse_dualMap_of_similitude`: transported along the isomorphism
  `W ≃ₗ[L] Dual L V` given by the pairing, `G` becomes `c • (F.dualMap)⁻¹`.
* `LinearMap.conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude`: the explicit conjugacy
  `G ∼ c • (F.dualMap)⁻¹`.
* `LinearMap.roots_map_charpoly_of_similitude`: the eigenvalues of `G` are the `c / λ` for the
  eigenvalues `λ` of `F`, computed in an algebraically closed extension field.
* `LinearMap.charpoly_roots_of_similitude`: the eigenvalues (with multiplicity) of `G` are the
  images of the eigenvalues of `F` under `λ ↦ c / λ`.
* `LinearMap.charpolyRev_roots_of_similitude`: the same statement in terms of the reverse
  characteristic polynomials `det (1 - t • F)`, in the shape of
  `AlgebraicGeometry.WeilFunctionalEquation`.
* `LinearMap.roots_map_charpolyRev_of_similitude`: the same reciprocal root identity for the
  roots computed *after* mapping the reverse characteristic polynomials into an algebraically
  closed extension field along a ring homomorphism `ι`. Here the base field carries no
  `IsAlgClosed` assumption. With `ι : L →+* ℂ`, `c = qᵈ` and `G` the dual endomorphism this
  is literally the shape of `AlgebraicGeometry.WeilFunctionalEquation`.
* `LinearMap.natDegree_map_charpolyRev_of_similitude`: both reverse characteristic polynomials
  of a similitude pair have degree `dim V` after mapping into an extension field along `ι`.
* `LinearMap.det_mul_det_of_similitude`: the determinants of the two members of a similitude
  pair multiply to `c ^ dim V`.

An auxiliary polynomial lemma `Polynomial.roots_reverse_of_monic` (the roots of the reverse of
a split monic polynomial with nonzero constant coefficient are the inverses of its roots) also
lives here: `#find_home` places it in this file, since it combines the two mirror files
`WeilConjectures.Mathlib.Algebra.Polynomial.Reverse` and
`WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision`, and no Mathlib file imports both.
-/

@[expose] public section

open Module Polynomial

namespace Polynomial

/-- The roots of the reverse of a monic split polynomial with nonzero constant coefficient are
the inverses of its roots. The splitting hypothesis is stated as `f.Splits` rather than as
`[IsAlgClosed L]`, so that it also applies to a polynomial that happens to split over a field
that is not algebraically closed. -/
theorem roots_reverse_of_monic {L : Type*} [Field L] {f : L[X]} (hf : f.Monic) (hsp : f.Splits)
    (h0 : f.coeff 0 ≠ 0) : f.reverse.roots = f.roots.map (·⁻¹) := by
  have hmem : (0 : L) ∉ f.roots := by
    intro h
    rw [mem_roots hf.ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero] at h
    exact h0 h
  conv_lhs => rw [hsp.eq_prod_roots_of_monic hf]
  rw [reverse_multiset_prod_X_sub_C, roots_multiset_prod_one_sub_C_mul_X hmem]

end Polynomial

namespace LinearMap

/-- The constant coefficient of the characteristic polynomial of an endomorphism with invertible
determinant stays nonzero after mapping the coefficients along a ring homomorphism of fields. -/
theorem coeff_zero_map_charpoly_ne_zero {L N M : Type*} [Field L] [AddCommGroup N] [Module L N]
    [FiniteDimensional L N] [Field M] (ι : L →+* M) {T : Module.End L N}
    (hT : IsUnit (LinearMap.det T)) : (T.charpoly.map ι).coeff 0 ≠ 0 := by
  rw [coeff_map, ne_eq, map_eq_zero_iff ι ι.injective]
  intro h
  rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero] at hT
  exact not_isUnit_zero hT

/-- For an endomorphism with invertible determinant, the roots of `det (1 - t • T)`, computed in
an algebraically closed extension field, are the inverses of the eigenvalues of `T`. -/
theorem roots_map_charpolyRev_eq_map_inv {L N M : Type*} [Field L] [AddCommGroup N]
    [Module L N] [FiniteDimensional L N] [Field M] [IsAlgClosed M] (ι : L →+* M)
    (T : Module.End L N) (hT : IsUnit (LinearMap.det T)) :
    (T.charpolyRev.map ι).roots = (T.charpoly.map ι).roots.map (·⁻¹) := by
  rw [charpolyRev_def, ← reverse_map ι.injective]
  exact roots_reverse_of_monic ((charpoly_monic T).map ι) (IsAlgClosed.splits _)
    (coeff_zero_map_charpoly_ne_zero ι hT)

section Similitude

variable {L V W : Type*} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
  [FiniteDimensional L V] [FiniteDimensional L W] {p : V →ₗ[L] W →ₗ[L] L} [p.IsPerfPair]
  {F : Module.End L V} {G : Module.End L W} {c : L}

variable (hc : c ≠ 0) (hFG : ∀ v w, p (F v) (G w) = c * p v w)
include hc hFG

omit [FiniteDimensional L V] [FiniteDimensional L W] in
/-- The first member of a similitude pair for a perfect pairing is injective. -/
theorem injective_of_similitude : Function.Injective F := by
  refine (injective_iff_map_eq_zero F).2 fun v hv ↦ ?_
  have hpv : p v = 0 := by
    ext w
    have h : c * p v w = 0 := by rw [← hFG v w, hv]; simp
    simpa using (mul_eq_zero.mp h).resolve_left hc
  exact (IsPerfPair.bijective_left p).injective (show p v = p 0 by simpa using hpv)

omit [FiniteDimensional L V] [FiniteDimensional L W] in
/-- The second member of a similitude pair for a perfect pairing is injective. -/
theorem injective_right_of_similitude : Function.Injective G := by
  refine (injective_iff_map_eq_zero G).2 fun w hw ↦ ?_
  have hpw : p.flip w = 0 := by
    ext v
    have h : c * p v w = 0 := by rw [← hFG v w, hw]; simp
    simpa using (mul_eq_zero.mp h).resolve_left hc
  exact (IsPerfPair.bijective_right p).injective (show p.flip w = p.flip 0 by simpa using hpw)

omit [FiniteDimensional L W] in
/-- The first member of a similitude pair for a perfect pairing has invertible determinant. -/
theorem isUnit_det_of_similitude : IsUnit (LinearMap.det F) := by
  have hinj := injective_of_similitude hc hFG
  have hb : Function.Bijective F := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have h := (LinearEquiv.ofBijective F hb).isUnit_det'
  rwa [show ((LinearEquiv.ofBijective F hb : V ≃ₗ[L] V) : V →ₗ[L] V) = F from rfl] at h

omit [FiniteDimensional L V] in
/-- The second member of a similitude pair for a perfect pairing has invertible determinant. -/
theorem isUnit_det_right_of_similitude : IsUnit (LinearMap.det G) := by
  have hinj := injective_right_of_similitude hc hFG
  have hb : Function.Bijective G := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have h := (LinearEquiv.ofBijective G hb).isUnit_det'
  rwa [show ((LinearEquiv.ofBijective G hb : W ≃ₗ[L] W) : W →ₗ[L] W) = G from rfl] at h

omit hc

omit [FiniteDimensional L V] [FiniteDimensional L W] in
/-- The similitude condition says that, after transporting `G` along the isomorphism
`W ≃ₗ[L] Dual L V` given by the pairing, the transpose of `F` and `G` are inverse to each
other up to the factor `c`. -/
theorem dualMap_comp_toPerfPair_comp_of_similitude :
    F.dualMap ∘ₗ (p.flip.toPerfPair : W →ₗ[L] Module.Dual L V) ∘ₗ G
      = c • (p.flip.toPerfPair : W →ₗ[L] Module.Dual L V) := by
  ext w v
  simpa using hFG v w

omit [FiniteDimensional L V] [FiniteDimensional L W] in
/-- The transpose of `F` and the conjugate of `G` by the pairing multiply to `c`. -/
theorem dualMap_mul_conj_of_similitude :
    F.dualMap * (p.flip.toPerfPair.conj G) = c • 1 := by
  refine LinearMap.ext fun φ ↦ ?_
  have h := congrArg (fun T ↦ T (p.flip.toPerfPair.symm φ))
    (dualMap_comp_toPerfPair_comp_of_similitude hFG)
  simpa [LinearEquiv.conj_apply_apply] using h

omit [FiniteDimensional L W] in
include hc in
/-- `G` is conjugate, by the isomorphism `W ≃ₗ[L] Dual L V` given by the pairing, to the
endomorphism `c • (F.dualMap)⁻¹` of the dual of `V`: the transpose of `F` is invertible, and
`G` corresponds to `c` times the transpose of its inverse. -/
theorem conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude :
    p.flip.toPerfPair.conj G = c • Ring.inverse F.dualMap := by
  set e := p.flip.toPerfPair with he
  have hab : F.dualMap * (c⁻¹ • e.conj G) = 1 := by
    rw [mul_smul_comm, dualMap_mul_conj_of_similitude hFG, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  have hba : (c⁻¹ • e.conj G) * F.dualMap = 1 := mul_eq_one_comm.mp hab
  have hinv : Ring.inverse F.dualMap = c⁻¹ • e.conj G :=
    Ring.inverse_unit (⟨F.dualMap, c⁻¹ • e.conj G, hab, hba⟩ : (Module.End L (Dual L V))ˣ)
  rw [hinv, smul_smul, mul_inv_cancel₀ hc, one_smul]

include hc in
/-- `G` is conjugate, by the isomorphism `W ≃ₗ[L] Dual L V` given by the pairing, to the
endomorphism `c • (F.dualMap)⁻¹` of the dual of `V`; in particular they have the same
characteristic polynomial. -/
theorem charpoly_eq_smul_inverse_dualMap_of_similitude :
    G.charpoly = (c • Ring.inverse F.dualMap : Module.End L (Module.Dual L V)).charpoly := by
  rw [← conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude hc hFG,
    LinearEquiv.charpoly_conj]

omit [FiniteDimensional L W] in
/-- **The determinant product rule.** If `F` and `G` multiply the perfect pairing `p` by the
similitude factor `c`, then their determinants multiply to `c ^ dim V`. -/
theorem det_mul_det_of_similitude :
    LinearMap.det F * LinearMap.det G = c ^ finrank L V := by
  have h := congrArg LinearMap.det (dualMap_mul_conj_of_similitude (p := p) hFG)
  rwa [show dualMap F * p.flip.toPerfPair.conj G
      = dualMap F ∘ₗ p.flip.toPerfPair.conj G from rfl, LinearMap.det_comp,
    det_dualMap, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj,
    LinearMap.det_smul, map_one, mul_one, Subspace.dual_finrank_eq] at h

/-- The reverse characteristic polynomial of `G` is determined by the characteristic polynomial
of `F`: it is `det (1 - t • G) = (-1) ^ dim V * det (c * t - F) / det F`. -/
theorem C_det_mul_charpolyRev_of_similitude :
    C (LinearMap.det F) * G.charpolyRev
      = C ((-1) ^ finrank L V) * F.charpoly.comp (C c * X) := by
  have h := LinearMap.C_det_mul_charpolyRev (dualMap_mul_conj_of_similitude hFG)
  rwa [det_dualMap, charpoly_dualMap, charpolyRev_def, LinearEquiv.charpoly_conj,
    ← charpolyRev_def, Subspace.dual_finrank_eq] at h

include hc in
/-- **The reciprocal root identity along a field embedding.** After mapping the reverse
characteristic polynomials into an algebraically closed extension field `M` along a ring
homomorphism `ι`, the roots of `det (1 - t • G)` are the images of the roots of
`det (1 - t • F)` under `z ↦ (ι c * z)⁻¹`. Unlike `charpolyRev_roots_of_similitude`, the base
field `L` is not assumed algebraically closed.

With `M = ℂ`, `c = qᵈ` and `G` the endomorphism dual to `F`, this is literally the shape of
`AlgebraicGeometry.WeilFunctionalEquation`. -/
theorem roots_map_charpolyRev_of_similitude {M : Type*} [Field M] [IsAlgClosed M] (ι : L →+* M) :
    (G.charpolyRev.map ι).roots = (F.charpolyRev.map ι).roots.map fun z ↦ (ι c * z)⁻¹ := by
  have hdet : IsUnit (LinearMap.det F) := isUnit_det_of_similitude hc hFG
  have hι : Function.Injective ι := ι.injective
  have hc0 : ι c ≠ 0 := fun h ↦ hc (hι (by simpa using h))
  have hcoeff : F.charpoly.coeff 0 ≠ 0 := by
    intro h
    rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero] at hdet
    exact not_isUnit_zero hdet
  have hcoeff' : (F.charpoly.map ι).coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact fun h ↦ hcoeff (hι (by simpa using h))
  have hkey : C (ι (LinearMap.det F)) * G.charpolyRev.map ι
      = C ((-1 : M) ^ finrank L V) * (F.charpoly.map ι).comp (C (ι c) * X) := by
    have h := congrArg (Polynomial.map ι) (C_det_mul_charpolyRev_of_similitude hFG)
    rwa [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      map_pow, map_neg, map_one] at h
  have hroots := congrArg Polynomial.roots hkey
  rw [roots_C_mul _ (fun h ↦ hdet.ne_zero (hι (by simpa using h))),
    roots_C_mul _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))] at hroots
  rw [show (C (ι c) * X : M[X]) = C (ι c) * X + C 0 by simp,
    roots_comp_C_mul_X_add_C _ _ _ hc0.isUnit] at hroots
  rw [hroots, charpolyRev_def, ← reverse_map hι,
    roots_reverse_of_monic ((charpoly_monic F).map ι) (IsAlgClosed.splits _) hcoeff',
    Multiset.map_map]
  refine Multiset.map_congr rfl fun a _ ↦ ?_
  simp [Ring.inverse_eq_inv', mul_inv_rev, mul_comm]

include hc in
/-- **The reciprocal eigenvalues along a field embedding.** After mapping the characteristic
polynomials into an algebraically closed extension field `M` along a ring homomorphism `ι`,
the eigenvalues of `G`, with multiplicity, are the images of the eigenvalues of `F` under
`α ↦ ι c / α`. Unlike `charpoly_roots_of_similitude`, the base field `L` is not assumed
algebraically closed. -/
theorem roots_map_charpoly_of_similitude {M : Type*} [Field M] [IsAlgClosed M] (ι : L →+* M) :
    (G.charpoly.map ι).roots = (F.charpoly.map ι).roots.map fun z ↦ ι c / z := by
  have h := roots_map_charpolyRev_of_similitude hc hFG ι
  rw [roots_map_charpolyRev_eq_map_inv ι G (isUnit_det_right_of_similitude hc hFG),
    roots_map_charpolyRev_eq_map_inv ι F (isUnit_det_of_similitude hc hFG),
    Multiset.map_map] at h
  have h' := congrArg (Multiset.map (·⁻¹ : M → M)) h
  rw [Multiset.map_map, Multiset.map_map] at h'
  simp only [Function.comp_def, inv_inv, Multiset.map_id'] at h'
  rw [h']
  exact Multiset.map_congr rfl fun z _ ↦ (div_eq_mul_inv _ _).symm

include hc in
/-- **The degrees along a field embedding.** Both members of a similitude pair are invertible,
so their reverse characteristic polynomials keep the full degree `dim V = dim W` after their
coefficients are mapped into an extension field `M` along a ring homomorphism `ι`.

Together with `LinearMap.roots_map_charpolyRev_of_similitude` (the reciprocal root identity) and
`LinearMap.coeff_zero_charpolyRev` (the constant coefficient is `1`, so neither polynomial
vanishes at `0`), this is the whole of the blueprint's `cor:zla-reciprocal-roots-embedding`. -/
theorem natDegree_map_charpolyRev_of_similitude {M : Type*} [Field M] (ι : L →+* M) :
    (F.charpolyRev.map ι).natDegree = finrank L V ∧
      (G.charpolyRev.map ι).natDegree = finrank L V :=
  ⟨natDegree_map_charpolyRev (isUnit_det_of_similitude hc hFG) ι,
    (natDegree_map_charpolyRev (isUnit_det_right_of_similitude hc hFG) ι).trans
      (Module.finrank_of_isPerfPair p).symm⟩

variable [IsAlgClosed L]
include hc

/-- The reverse characteristic polynomial of `G`, factored into linear factors indexed by the
eigenvalues of `F`. -/
theorem charpolyRev_eq_prod_of_similitude :
    G.charpolyRev = (F.charpoly.roots.map fun a ↦ 1 - C (c / a) * X).prod := by
  have hdet : IsUnit (LinearMap.det F) := isUnit_det_of_similitude hc hFG
  have h0 : (0 : L) ∉ F.charpoly.roots := zero_notMem_roots_charpoly hdet
  have hcomp : F.charpoly.comp (C c * X)
      = (F.charpoly.roots.map fun a ↦ C c * X - C a).prod := by
    conv_lhs => rw [charpoly_eq_prod_roots F]
    have heval : ((F.charpoly.roots.map fun a ↦ X - C a).prod).comp (C c * X)
        = eval₂RingHom C (C c * X) ((F.charpoly.roots.map fun a ↦ X - C a).prod) := rfl
    rw [heval, map_multiset_prod, Multiset.map_map]
    simp
  have hneg : C ((-1) ^ finrank L V) * (F.charpoly.roots.map fun a ↦ C c * X - C a).prod
      = (F.charpoly.roots.map fun a ↦ C a - C c * X).prod := by
    rw [← card_roots_charpoly F,
      ← Multiset.card_map (fun a : L ↦ C c * X - C a) F.charpoly.roots,
      map_pow, map_neg, map_one, ← Multiset.prod_map_neg, Multiset.map_map]
    simp
  have hfac : (F.charpoly.roots.map fun a ↦ C a - C c * X).prod
      = C (LinearMap.det F) * (F.charpoly.roots.map fun a ↦ 1 - C (c / a) * X).prod := by
    have hmap : (F.charpoly.roots.map fun a ↦ C a - C c * X)
        = F.charpoly.roots.map fun a ↦ C a * (1 - C (c / a) * X) := by
      refine Multiset.map_congr rfl fun a ha ↦ ?_
      have ha0 : a ≠ 0 := fun h ↦ h0 (h ▸ ha)
      rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ ha0]
    rw [hmap, Multiset.prod_map_mul, ← map_multiset_prod, det_eq_prod_roots_charpoly]
  have hkey := C_det_mul_charpolyRev_of_similitude hFG
  rw [hcomp, hneg, hfac] at hkey
  exact mul_left_cancel₀ (fun h ↦ hdet.ne_zero (C_eq_zero.mp h)) hkey

/-- The roots of `det (1 - t • G)`, that is, the inverse eigenvalues of `G`, are the
eigenvalues of `F` divided by `c`. -/
theorem charpolyRev_roots_eq_of_similitude :
    G.charpolyRev.roots = F.charpoly.roots.map fun z ↦ z / c := by
  have h0 : (0 : L) ∉ F.charpoly.roots :=
    zero_notMem_roots_charpoly (isUnit_det_of_similitude hc hFG)
  have h0' : (0 : L) ∉ F.charpoly.roots.map fun z ↦ c / z := by
    simp only [Multiset.mem_map, not_exists, not_and]
    exact fun a ha ↦ div_ne_zero hc fun h ↦ h0 (h ▸ ha)
  have hsplit : (F.charpoly.roots.map fun a ↦ 1 - C (c / a) * X)
      = (F.charpoly.roots.map fun z ↦ c / z).map fun b ↦ 1 - C b * X := by
    rw [Multiset.map_map]; rfl
  rw [charpolyRev_eq_prod_of_similitude hc hFG, hsplit,
    roots_multiset_prod_one_sub_C_mul_X h0', Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ ↦ by simp [inv_div]

/-- **The reciprocal eigenvalue pairing.** The eigenvalues of `G`, with multiplicity, are the
images of the eigenvalues of `F` under `λ ↦ c / λ`. -/
theorem charpoly_roots_of_similitude :
    G.charpoly.roots = F.charpoly.roots.map fun z ↦ c / z := by
  have h0G : (0 : L) ∉ G.charpoly.roots :=
    zero_notMem_roots_charpoly (isUnit_det_right_of_similitude hc hFG)
  have h1 : G.charpoly.roots.map (·⁻¹) = F.charpoly.roots.map fun z ↦ z / c := by
    rw [← roots_multiset_prod_one_sub_C_mul_X h0G, ← charpolyRev_eq_prod_roots G]
    exact charpolyRev_roots_eq_of_similitude hc hFG
  simpa [Multiset.map_map, inv_div] using congrArg (Multiset.map (·⁻¹ : L → L)) h1

/-- **The reciprocal eigenvalue pairing, reciprocal form.** The roots of `det (1 - t • G)` are
the images of the roots of `det (1 - t • F)` under `z ↦ (c * z)⁻¹`. This is the shape of
`AlgebraicGeometry.WeilFunctionalEquation`. -/
theorem charpolyRev_roots_of_similitude :
    G.charpolyRev.roots = F.charpolyRev.roots.map fun z ↦ (c * z)⁻¹ := by
  have h0 : (0 : L) ∉ F.charpoly.roots :=
    zero_notMem_roots_charpoly (isUnit_det_of_similitude hc hFG)
  rw [charpolyRev_roots_eq_of_similitude hc hFG, charpolyRev_eq_prod_roots F,
    roots_multiset_prod_one_sub_C_mul_X h0, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ ↦ by simp [div_eq_mul_inv, mul_comm]

end Similitude

section IsField

/-! The statements above for a commutative ring `L` that is a field (`IsField L`) rather than
for a `Field L`: they then apply to modules whose scalar action is built from the ring
structure of `L` alone, without comparing two `Field`-derived instance paths. -/

variable {L V W : Type*} [CommRing L] [AddCommGroup V] [Module L V] [AddCommGroup W]
  [Module L W] {p : V →ₗ[L] W →ₗ[L] L} [p.IsPerfPair] {F : Module.End L V}
  {G : Module.End L W} {c : L}

/-- `LinearMap.conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude` over a commutative ring
that is a field. -/
theorem conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude_of_isField (hL : IsField L)
    (hc : c ≠ 0) (hFG : ∀ v w, p (F v) (G w) = c * p v w) :
    p.flip.toPerfPair.conj G = c • Ring.inverse F.dualMap := by
  let := hL.toField
  have := Module.IsReflexive.of_isPerfPair p
  exact conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude hc hFG

/-- `LinearMap.roots_map_charpoly_of_similitude` over a commutative ring that is a field. -/
theorem roots_map_charpoly_of_similitude_of_isField (hL : IsField L) [Module.Free L V]
    [Module.Finite L V] [Module.Free L W] [Module.Finite L W] (hc : c ≠ 0)
    (hFG : ∀ v w, p (F v) (G w) = c * p v w) {M : Type*} [Field M] [IsAlgClosed M]
    (ι : L →+* M) :
    (G.charpoly.map ι).roots = (F.charpoly.map ι).roots.map fun z ↦ ι c / z := by
  let := hL.toField
  exact roots_map_charpoly_of_similitude hc hFG ι

end IsField

end LinearMap
