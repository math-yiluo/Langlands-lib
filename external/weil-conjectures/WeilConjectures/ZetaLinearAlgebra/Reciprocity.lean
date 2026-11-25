/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Polynomial.BigOperators
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.BilinearForm
public import WeilConjectures.ZetaLinearAlgebra.Pairing
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Duality reciprocity of the Frobenius factors

Let `D` be a trace datum of length `2 * d` which is self-dual for the similitude factor `qᵈ`,
the linear algebra shadow of Poincaré duality used in
`WeilConjectures.ZetaLinearAlgebra.FunctionalEquation`. Writing `b i` for the dimension of
`D.V i` and `Dᵢ = det (D.F i)` for the determinant constant of degree `i`, duality gives the
reciprocity of the factors themselves,

`Dᵢ · P_{2d-i}(T) = (-1)^{b i} · charpoly (F i) (qᵈ T)`,

the product rule `Dᵢ · D_{2d-i} = q ^ (d · b i)`, and the parity of `d · χ`, where
`χ = ∑ᵢ (-1)ⁱ b i` is `Polynomial.alternatingNatDegreeSum D.P`. The parity is what makes the
constant `q ^ (d χ / 2)` of the classical functional equation an integer power of `q`.

The Betti number `b i` is measured here both as `dim (D.V i)` and as `deg (D.P i)`; the two
agree because the similitude hypothesis makes `D.F i` invertible, which is
`TraceDatum.natDegree_P_of_pairing`.

For odd `d` the parity rests on the middle Betti number `b d` being even. The Poincaré duality
sign rule `⟨y, x⟩_{2d-i} = (-1)ⁱ ⟨x, y⟩_i` makes the middle pairing alternating, and a
nondegenerate alternating form has even rank by
`LinearMap.BilinForm.even_finrank_of_isAlt`. A `TraceDatum` carries no identification of
`D.V i.rev` with `D.V i` at the middle degree, so the middle pairing is taken here as a
separate hypothesis: a nondegenerate alternating form on `D.V m`, where `m` is the middle
index, characterised by `m.rev = m`.

This file formalises the statements of the reciprocity subsection of the blueprint block on
zeta functions and the Weil conjectures.

## Main statements

- `TraceDatum.C_det_mul_P_rev_of_pairing`: reciprocity of the factors themselves.
- `TraceDatum.natDegree_P_of_pairing`: the degree of `D.P i` is the dimension of `D.V i`.
- `TraceDatum.det_mul_det_rev_of_pairing`: the product rule for the determinant constants.
- `TraceDatum.even_mul_alternatingNatDegreeSum_of_pairing`: `d · χ` is even, given a
  nondegenerate alternating middle pairing for odd `d`.

## References

- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

@[expose] public section

universe u v

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))
  {p : ∀ i : Fin (2 * d + 1), D.V i →ₗ[K] D.V i.rev →ₗ[K] K}

omit [CharZero K] in
/-- **Reciprocity of the factors.** For a trace datum that is self-dual for the similitude
factor `qᵈ`, the reciprocal characteristic polynomial in degree `2 * d - i` is determined by
the characteristic polynomial in degree `i`: it is
`(-1)^{b i} · det (F i)⁻¹ · charpoly (F i) (qᵈ T)`. -/
theorem C_det_mul_P_rev_of_pairing (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (i : Fin (2 * d + 1)) :
    Polynomial.C (LinearMap.det (D.F i)) * D.P i.rev =
      Polynomial.C ((-1) ^ Module.finrank K (D.V i)) *
        (D.F i).charpoly.comp (Polynomial.C ((q : K) ^ d) * Polynomial.X) :=
  have := hp i
  LinearMap.C_det_mul_charpolyRev_of_similitude (hFG i)

/-- **The Betti number of a self-dual trace datum is a degree.** Both members of a similitude
pair are invertible, so the reciprocal characteristic polynomial in degree `i` has the full
degree `dim (D.V i)`. This identifies the two ways of measuring the `i`-th Betti number. -/
theorem natDegree_P_of_pairing (hq : 1 < q) (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (i : Fin (2 * d + 1)) :
    (D.P i).natDegree = Module.finrank K (D.V i) := by
  have := hp i
  have hc : ((q : K) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have h := (LinearMap.natDegree_map_charpolyRev_of_similitude hc (hFG i) (RingHom.id K)).1
  rw [P_def]
  rwa [Polynomial.map_id] at h

omit [CharZero K] in
/-- **The determinant product rule.** For a trace datum that is self-dual for the similitude
factor `qᵈ`, the determinant constants `Dᵢ = det (D.F i)` satisfy
`Dᵢ · D_{2d-i} = q ^ (d · b i)`, where `b i = dim (D.V i)`. -/
theorem det_mul_det_rev_of_pairing (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (i : Fin (2 * d + 1)) :
    LinearMap.det (D.F i) * LinearMap.det (D.F i.rev) =
      (q : K) ^ (d * Module.finrank K (D.V i)) := by
  have := hp i
  rw [LinearMap.det_mul_det_of_similitude (hFG i), ← pow_mul, mul_comm d]

/-- **The parity of `d · χ`.** For a trace datum that is self-dual for the similitude factor
`qᵈ`, the Betti numbers are symmetric, so the Euler characteristic `χ = ∑ᵢ (-1)ⁱ b i` has the
same parity as the middle Betti number `b d`, where the middle index `m` is characterised by
`m.rev = m`. For odd `d` the Poincaré duality sign rule makes the middle pairing alternating,
which is the hypothesis `halt`, and a nondegenerate alternating form has even rank, so `d · χ`
is even. This is what makes the constant `q ^ (d χ / 2)` of the classical functional equation
an integer power of `q`. -/
theorem even_mul_alternatingNatDegreeSum_of_pairing (hq : 1 < q) (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    {m : Fin (2 * d + 1)} (hm : m.rev = m)
    (halt : Odd d → ∃ B : LinearMap.BilinForm K (D.V m), B.IsAlt ∧ B.Nondegenerate) :
    Even ((d : ℤ) * Polynomial.alternatingNatDegreeSum D.P) := by
  have hmid : Odd d → Even (Module.finrank K (D.V m)) := fun hd ↦
    let ⟨B, hB1, hB2⟩ := halt hd
    LinearMap.BilinForm.even_finrank_of_isAlt hB1 hB2
  have hrev : ∀ i : Fin (2 * d + 1), (D.P i.rev).natDegree = (D.P i).natDegree := by
    intro i
    have := hp i
    rw [D.natDegree_P_of_pairing hq hp hFG, D.natDegree_P_of_pairing hq hp hFG,
      Module.finrank_of_isPerfPair (p i)]
  obtain ⟨k, hk⟩ := Polynomial.even_alternatingNatDegreeSum_sub_of_natDegree_rev hrev hm
  rcases Nat.even_or_odd d with hd | hd
  · obtain ⟨e, he⟩ := hd
    refine ⟨(e : ℤ) * Polynomial.alternatingNatDegreeSum D.P, ?_⟩
    have hd' : (d : ℤ) = (e : ℤ) + e := by omega
    rw [hd']
    ring
  · obtain ⟨b, hb⟩ := hmid hd
    have hbP : (D.P m).natDegree = b + b := by rw [D.natDegree_P_of_pairing hq hp hFG, hb]
    refine ⟨(d : ℤ) * k + (d : ℤ) * b, ?_⟩
    have hchi : Polynomial.alternatingNatDegreeSum D.P = k + k + ((D.P m).natDegree : ℤ) := by
      omega
    have hb' : ((D.P m).natDegree : ℤ) = (b : ℤ) + b := by rw [hbP]; push_cast; ring
    rw [hchi, hb']
    ring

end TraceDatum

end
