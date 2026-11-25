/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Ideal

/-! # Flatness of polynomial local quotients over finite coefficient subrings

Source: Stacks Project, Algebra, Tag 00SV, second paragraph of the proof, and Tag 05UU (2).
(blueprint: lem-weil-pbc-polynomial-local-flat-quotient-descent).
-/

@[expose] public section

universe u

namespace RingTheory

-- Adjoin the requested scalars and polynomial coefficients to R₀.
private theorem finite_polynomials_stage
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n : ℕ}
    (s : Finset (MvPolynomial (Fin n) R)) (rs : Finset R) :
    ∃ (B : Subring R), R₀ ≤ B ∧ Algebra.FiniteType ℤ B ∧
      (∀ r ∈ rs, r ∈ B) ∧
      ∀ p ∈ s, p ∈ Set.range (MvPolynomial.map B.subtype) := by
  classical
  let : Algebra R₀ R := R₀.subtype.toAlgebra
  let cs : Set R := (rs : Set R) ∪
    ⋃ p ∈ (s : Set (MvPolynomial (Fin n) R)), (p.coeffs : Set R)
  have hcs : cs.Finite :=
    rs.finite_toSet.union (s.finite_toSet.biUnion fun p _ ↦ p.coeffs.finite_toSet)
  let A := Algebra.adjoin R₀ cs
  let B := A.toSubring
  have hB : R₀ ≤ B := by
    intro x hx
    exact A.algebraMap_mem ⟨x, hx⟩
  have hfg : A.FG := Subalgebra.fg_def.mpr ⟨cs, hcs, rfl⟩
  have hft : Algebra.FiniteType R₀ A := A.fg_iff_finiteType.mp hfg
  have hftZ : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans hR₀ hft
  refine ⟨B, hB, hftZ, ?_, ?_⟩
  · intro r hr
    exact Algebra.subset_adjoin (Set.mem_union_left _ hr)
  · intro p hp
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin
      (Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩))⟩, rfl⟩

-- Stacks 00SV: a finite relation modulo the equations is detected at a finite stage.
private theorem finite_relation_stage
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n l : ℕ}
    (ps : List (MvPolynomial (Fin n) R₀))
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (r : Fin l → R) (x : Fin l → Localization.AtPrime Q)
    (hx : ∑ j, r j • x j ∈ Ideal.ofList (ps.map (fun p ↦
      algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q)
        (MvPolynomial.map R₀.subtype p)))) :
    ∃ (B : Subring R) (hB : R₀ ≤ B), Algebra.FiniteType ℤ B ∧
      ∃ (φ : Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)) →+*
          Localization.AtPrime Q),
        (∀ p : MvPolynomial (Fin n) B,
          φ (algebraMap (MvPolynomial (Fin n) B)
              (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))) p) =
            algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q)
              (MvPolynomial.map B.subtype p)) ∧
        ∃ (a : Fin l → B)
          (y : Fin l → Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))),
          (∀ j, (a j : R) = r j) ∧ (∀ j, φ (y j) = x j) ∧
          ∑ j, a j • y j ∈ Ideal.ofList (ps.map (fun p ↦
            algebraMap (MvPolynomial (Fin n) B)
              (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)))
              (MvPolynomial.map (Subring.inclusion hB) p))) := by
  classical
  let P := MvPolynomial (Fin n) R
  let L := Localization.AtPrime Q
  let e := MvPolynomial.map (σ := Fin n) R₀.subtype
  let f := algebraMap P L
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite Q.primeCompl x
  choose z hz using hd
  have hz' (j : Fin l) : f (z j) = f d * x j := by
    simpa only [Algebra.smul_def] using hz j
  let v : P := ∑ j, MvPolynomial.C (r j) * z j
  have hv : f v = f d * ∑ j, r j • x j := by
    dsimp only [v]
    simp only [map_sum, map_mul, hz', Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change f (MvPolynomial.C (r j)) * (f d * x j) =
      f d * ((algebraMap R L) (r j) * x j)
    change (algebraMap R L) (r j) * (f d * x j) = _
    ring
  have hlist : Ideal.ofList (ps.map (fun p ↦ f (e p))) =
      (Ideal.ofList (ps.map e)).map f := by
    simpa only [List.map_map, Function.comp_def] using
      (Ideal.map_ofList f (ps.map e)).symm
  have hmem : f v ∈ (Ideal.ofList (ps.map e)).map f := by
    rw [hv, ← hlist]
    exact Ideal.mul_mem_left _ _ hx
  obtain ⟨t, ht, htv⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl L
      (Ideal.ofList (ps.map e)) v).mp hmem
  have hspan : Ideal.ofList (ps.map e) =
      Ideal.span (Set.range (fun j : Fin ps.length ↦ e (ps.get j))) := by
    apply congrArg Ideal.span
    ext p
    change (p ∈ ps.map e) ↔ ∃ j : Fin ps.length, e (ps.get j) = p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hp
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hq
      exact ⟨j, hqp⟩
    · rintro ⟨j, rfl⟩
      exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
  rw [hspan] at htv
  obtain ⟨cs, hcs⟩ := Ideal.mem_span_range_iff_exists_fun.mp htv
  obtain ⟨B, hB, hft, hrs, hpoly⟩ := finite_polynomials_stage R₀ hR₀
    ({d.1, t} ∪ Finset.univ.image z ∪ Finset.univ.image cs) (Finset.univ.image r)
  obtain ⟨dB, hdB⟩ := hpoly d.1 (by simp)
  obtain ⟨tB, htB⟩ := hpoly t (by simp)
  have hzB (j : Fin l) : z j ∈ Set.range (MvPolynomial.map B.subtype) :=
    hpoly (z j) (by simp)
  choose zB hzB using hzB
  have hcsB (j : Fin ps.length) : cs j ∈ Set.range (MvPolynomial.map B.subtype) :=
    hpoly (cs j) (by simp)
  choose csB hcsB using hcsB
  let a (j : Fin l) : B := ⟨r j, hrs _ (by simp)⟩
  let eB := MvPolynomial.map (σ := Fin n) B.subtype
  let gB := MvPolynomial.map (σ := Fin n) (Subring.inclusion hB)
  let QB := Q.comap eB
  let LB := Localization.AtPrime QB
  let fB := algebraMap (MvPolynomial (Fin n) B) LB
  have hg (p : MvPolynomial (Fin n) R₀) : eB (gB p) = e p := by
    rw [MvPolynomial.map_map]
    rfl
  have hdB' : dB ∈ QB.primeCompl := by
    change eB dB ∉ Q
    rw [hdB]
    exact d.2
  have htB' : tB ∈ QB.primeCompl := by
    change eB tB ∉ Q
    rw [htB]
    exact ht
  let φ : LB →+* L :=
    IsLocalization.map (M := QB.primeCompl) (S := LB) (T := Q.primeCompl) L eB
      (by intro s hs; exact hs)
  let y (j : Fin l) := IsLocalization.mk' LB (zB j) ⟨dB, hdB'⟩
  refine ⟨B, hB, hft, φ, ?_, a, y, (fun _ ↦ rfl), ?_, ?_⟩
  · intro p
    exact IsLocalization.map_eq _ p
  · intro j
    dsimp only [φ, y]
    rw [IsLocalization.map_mk', hzB]
    have he : (⟨eB dB, hdB'⟩ : Q.primeCompl) = d := Subtype.ext hdB
    rw [he]
    apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
    simpa only [mul_comm] using hz' j
  · let vB : MvPolynomial (Fin n) B := ∑ j, MvPolynomial.C (a j) * zB j
    have heq : ∑ j, csB j * gB (ps.get j) = tB * vB := by
      apply MvPolynomial.map_injective B.subtype Subtype.val_injective
      change eB (∑ j, csB j * gB (ps.get j)) = eB (tB * vB)
      simp only [map_sum, map_mul, hg]
      dsimp only [eB, vB]
      simp only [map_sum, map_mul, MvPolynomial.map_C, hzB, hcsB, htB]
      exact hcs
    have hm : tB * vB ∈ Ideal.ofList (ps.map gB) := by
      rw [← heq]
      apply Ideal.sum_mem
      intro j _
      apply Ideal.mul_mem_left
      exact Ideal.subset_span (List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩)
    have hm' : IsLocalization.mk' LB vB ⟨dB, hdB'⟩ ∈
        (Ideal.ofList (ps.map gB)).map fB := by
      apply (IsLocalization.mk'_mem_map_algebraMap_iff QB.primeCompl LB _ _ _).mpr
      exact ⟨tB, htB', hm⟩
    rw [Ideal.map_ofList, List.map_map] at hm'
    have hvB : ∑ j, a j • y j = IsLocalization.mk' LB vB ⟨dB, hdB'⟩ := by
      symm
      apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
      dsimp only [vB]
      simp only [map_sum, map_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [y]
      rw [Algebra.smul_def, mul_assoc, IsLocalization.mk'_spec]
      rfl
    rw [hvB]
    exact hm'

/-- Flatness of a fixed prefix quotient passes from finite type coefficient subrings to
an arbitrary coefficient ring. No complete-intersection or regularity assumption is used.
Source: Stacks Project, Algebra, Tag 00SV, second paragraph of the proof; Tag 05UU (2).
(blueprint: lem-weil-pbc-polynomial-local-flat-quotient-descent).

Proof: Apply the equational criterion of flatness (Stacks Tag 00HK). Lift the elements
of a finite relation in the full quotient to the localized polynomial ring and clear
a common denominator `d` outside `Q`, obtaining polynomial numerators `zⱼ`. If
`v = ∑ C(rⱼ) * zⱼ`, the relation says its localization belongs to the prefix ideal.
Localized ideal membership supplies `t` outside `Q` with `t * v` in the polynomial
prefix ideal; write this as a finite sum of polynomial multiples of the equations.
Adjoin the relation scalars and the coefficients of `d`, `t`, the numerators and
these multiples to `R₀`. This constructs a subring `B` finite type over the integers.
Injectivity of the polynomial coefficient inclusion transfers the identity to `B`;
no injectivity of its localization is needed. The lifted denominators remain outside
the contracted prime, so the lifted fractions satisfy the relation in the stage quotient.
The localization map carries the equations to their full-ring images and induces a
quotient map compatible with scalar inclusion. By `hstage`, the stage quotient is flat;
the forward equational criterion trivializes its relation. Map those element expansions
and coefficient equations to the full quotient to trivialize the original relation.
The backward equational criterion gives flatness. Empty relations and equation lists,
`i=0`, `i≥c`, and zero quotients are covered by the same finite sums and list operations.
The subring is an explicit adjoin, and all existence theorems used here are proved.
-/
theorem flat_polynomial_local_quotient_of_finiteType_subrings
    {R : Type u} [CommRing R] (R₀ : Subring R)
    (hR₀ : Algebra.FiniteType ℤ R₀) {n c : ℕ}
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime] (i : ℕ)
    (hstage : ∀ (B : Subring R) (hB : R₀ ≤ B), Algebra.FiniteType ℤ B →
      Module.Flat B
        (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype)) ⧸
          Ideal.ofList (((List.ofFn
            (fun j ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ j))).map
              (algebraMap (MvPolynomial (Fin n) B)
                (Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))))).take i))) :
    Module.Flat R (Localization.AtPrime Q ⧸
      Ideal.ofList (((List.ofFn (fun j ↦ MvPolynomial.map R₀.subtype (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))).take i)) := by
  -- Use the equational criterion (Stacks 00HK), directly implementing 05UU (2).
  classical
  let L := Localization.AtPrime Q
  let ps := (List.ofFn f₀).take i
  let I : Ideal L := Ideal.ofList (ps.map (fun p ↦
    algebraMap (MvPolynomial (Fin n) R) L (MvPolynomial.map R₀.subtype p)))
  suffices Module.Flat R (L ⧸ I) by
    have heq : I = Ideal.ofList (((List.ofFn
        (fun j ↦ MvPolynomial.map R₀.subtype (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) R) L)).take i) := by
      dsimp only [I, ps]
      rw [List.map_take, List.map_ofFn, List.map_ofFn]
      rfl
    rw [← heq]
    exact this
  refine Module.Flat.of_forall_isTrivialRelation fun {l r m} hm ↦ ?_
  choose x hx using fun j : Fin l ↦ Ideal.Quotient.mk_surjective (m j)
  have hrel : ∑ j, r j • x j ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hmk (r : R) (x : L) :
        Ideal.Quotient.mk I (r • x) = r • Ideal.Quotient.mk I x := by
      simp only [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
    simpa only [map_sum, hmk, hx] using hm
  obtain ⟨B, hB, hft, φ, hφ, a, y, ha, hy, hrelB⟩ :=
    finite_relation_stage R₀ hR₀ ps Q r x hrel
  let LB := Localization.AtPrime (Q.comap (MvPolynomial.map B.subtype))
  let IB : Ideal LB := Ideal.ofList (ps.map (fun p ↦
    algebraMap (MvPolynomial (Fin n) B) LB (MvPolynomial.map (Subring.inclusion hB) p)))
  have hmaps : (ps.map (fun p ↦ algebraMap (MvPolynomial (Fin n) B) LB
      (MvPolynomial.map (Subring.inclusion hB) p))).map φ =
      ps.map (fun p ↦ algebraMap (MvPolynomial (Fin n) R) L
        (MvPolynomial.map R₀.subtype p)) := by
    simp only [List.map_map]
    congr 1
    funext p
    dsimp only [Function.comp_def, LB, L]
    rw [hφ, MvPolynomial.map_map]
    rfl
  have hIJ : IB ≤ I.comap φ := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_ofList, hmaps]
  let ψ : LB ⧸ IB →+* L ⧸ I := Ideal.quotientMap I φ hIJ
  have hconst (b : B) : φ (algebraMap B LB b) = algebraMap R L (b : R) := by
    change φ ((algebraMap (MvPolynomial (Fin n) B) LB) (MvPolynomial.C b)) =
      (algebraMap (MvPolynomial (Fin n) R) L) (MvPolynomial.C (b : R))
    rw [hφ, MvPolynomial.map_C]
    rfl
  have hsmul (b : B) (z : LB ⧸ IB) : ψ (b • z) = (b : R) • ψ z := by
    simp only [Algebra.smul_def, map_mul]
    congr 1
    change Ideal.Quotient.mk I (φ (algebraMap B LB b)) = _
    rw [hconst, Ideal.Quotient.mk_algebraMap]
  have hz : ∑ j, a j • Ideal.Quotient.mk IB (y j) = 0 := by
    have hmk (b : B) (z : LB) :
        Ideal.Quotient.mk IB (b • z) = b • Ideal.Quotient.mk IB z := by
      simp only [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
    have he : Ideal.Quotient.mk IB (∑ j, a j • y j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrelB
    simpa only [map_sum, hmk] using he
  have hflat : Module.Flat B (LB ⧸ IB) := by
    have heq : IB = Ideal.ofList (((List.ofFn
        (fun j ↦ MvPolynomial.map (Subring.inclusion hB) (f₀ j))).map
        (algebraMap (MvPolynomial (Fin n) B) LB)).take i) := by
      dsimp only [IB, ps]
      rw [List.map_take, List.map_ofFn, List.map_ofFn]
      rfl
    rw [heq]
    exact hstage B hB hft
  obtain ⟨k, d, z, hdz, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  refine ⟨k, fun j s ↦ (d j s : R), fun s ↦ ψ (z s), ?_, ?_⟩
  · intro j
    calc
      m j = ψ (Ideal.Quotient.mk IB (y j)) := by
        change m j = Ideal.Quotient.mk I (φ (y j))
        rw [hy, hx]
      _ = ψ (∑ s, d j s • z s) := congrArg ψ (hdz j)
      _ = ∑ s, (d j s : R) • ψ (z s) := by simp only [map_sum, hsmul]
  · intro s
    have he := congrArg B.subtype (hd s)
    simpa only [map_sum, map_mul, map_zero, Subring.coe_subtype, ha] using he

end RingTheory
