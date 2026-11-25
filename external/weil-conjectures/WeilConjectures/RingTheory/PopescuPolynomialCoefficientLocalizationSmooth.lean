/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness after eliminating the auxiliary variables

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Eliminating the variables in column `j` identifies the localization with a polynomial
algebra over the base change of the coefficient localization. -/
private theorem coefficientLocalization_equiv
    {k : Type u} {A : Type v} [CommRing k] [CommRing A] [Algebra k A]
    (d n : ℕ) {m : ℕ} (a : Fin m → A) (j : Fin m) :
    let P := MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A
    let B := P ⧸ Ideal.span (Set.range (fun i : Fin d ↦
      MvPolynomial.X (Sum.inl i) ^ n -
        ∑ l : Fin m, MvPolynomial.X (Sum.inr (i, l)) * MvPolynomial.C (a l)))
    let f : MvPolynomial (Fin d) k →ₐ[k] B :=
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))
    letI := f.toRingHom.toAlgebra
    Nonempty (MvPolynomial (Fin d × {l : Fin m // l ≠ j})
      (_root_.TensorProduct k (MvPolynomial (Fin d) k) (Localization.Away (a j)))
        ≃ₐ[MvPolynomial (Fin d) k] Localization.Away (algebraMap A B (a j))) := by
  classical
  dsimp only
  let R := MvPolynomial (Fin d) k
  let P := MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A
  let rel : Fin d → P := fun i ↦ MvPolynomial.X (Sum.inl i) ^ n -
    ∑ l : Fin m, MvPolynomial.X (Sum.inr (i, l)) * MvPolynomial.C (a l)
  let I : Ideal P := Ideal.span (Set.range rel)
  let B := P ⧸ I
  let f : R →ₐ[k] B :=
    MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl i)))
  let : Algebra R B := f.toRingHom.toAlgebra
  have : IsScalarTower k R B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let L := Localization.Away (algebraMap A B (a j))
  let A' := Localization.Away (a j)
  let T := _root_.TensorProduct k R A'
  let D := MvPolynomial (Fin d × {l : Fin m // l ≠ j}) T
  let ca' : A' →+* D := MvPolynomial.C.comp TensorProduct.includeRight.toRingHom
  let ca : A →+* D := ca'.comp (algebraMap A A')
  have hu : IsUnit (ca (a j)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := A') (a j)).map ca'
  let inv : D := ↑hu.unit⁻¹
  have hinv : inv * ca (a j) = 1 := by
    simpa only [inv, hu.unit_spec] using Units.inv_mul hu.unit
  let x : Fin d → D := fun i ↦ algebraMap R D (MvPolynomial.X i)
  -- Set the eliminated column to zero before adding its solved value.
  let z₀ : Fin d → Fin m → D := fun i l ↦
    if h : l = j then 0 else MvPolynomial.X (i, ⟨l, h⟩)
  let w : Fin d → D := fun i ↦ inv * (x i ^ n - ∑ l, z₀ i l * ca (a l))
  let z : Fin d → Fin m → D := fun i l ↦ z₀ i l + if l = j then w i else 0
  let v : Fin d ⊕ (Fin d × Fin m) → D := Sum.elim x (fun p ↦ z p.1 p.2)
  -- Substitution kills every relation, so it descends to the localized quotient.
  let ev : P →+* D := MvPolynomial.eval₂Hom ca v
  have hevC (c : A) : ev (MvPolynomial.C c) = ca c :=
    MvPolynomial.eval₂Hom_C (σ := Fin d ⊕ (Fin d × Fin m)) ca v c
  have hevX (i : Fin d ⊕ (Fin d × Fin m)) :
      ev (MvPolynomial.X i) = v i :=
    MvPolynomial.eval₂Hom_X' ca v i
  have hev : ∀ i, ev (rel i) = 0 := by
    intro i
    have hsum : ∑ l, z i l * ca (a l) =
        (∑ l, z₀ i l * ca (a l)) + w i * ca (a j) := by
      simp [z, add_mul, Finset.sum_add_distrib, ite_mul]
    dsimp only [rel]
    simp only [map_sub, map_pow, map_sum, map_mul, hevC, hevX,
      v, Sum.elim_inl, Sum.elim_inr]
    rw [hsum]
    dsimp only [w]
    rw [mul_right_comm inv, hinv, one_mul]
    ring
  have hI : ∀ p, p ∈ I → ev p = 0 := by
    intro p hp
    exact (Ideal.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hev i) hp : p ∈ RingHom.ker ev)
  let q : B →+* D := Ideal.Quotient.lift I ev hI
  have hq : IsUnit (q (algebraMap A B (a j))) := by
    change IsUnit (q (Ideal.Quotient.mk I (MvPolynomial.C (a j))))
    rw [show q (Ideal.Quotient.mk I (MvPolynomial.C (a j))) =
      ev (MvPolynomial.C (a j)) from rfl, hevC]
    exact hu
  let s : L →+* D := IsLocalization.Away.lift (algebraMap A B (a j)) hq
  have hs (p : P) : s (algebraMap B L (Ideal.Quotient.mk I p)) = ev p := by
    dsimp only [s]
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk I ev hI
  -- In the reverse direction, include the coefficients and the remaining variables.
  let caL : A' →ₐ[k] L := IsLocalization.Away.liftAlgHom (a j)
    (f := IsScalarTower.toAlgHom k A L)
    (by
      simpa only [IsScalarTower.toAlgHom_apply,
        IsScalarTower.algebraMap_apply A B L] using
        IsLocalization.Away.algebraMap_isUnit (S := L) (algebraMap A B (a j)))
  let ct : T →ₐ[R] L := TensorProduct.lift (Algebra.ofId R L) caL
    (fun _ _ ↦ Commute.all _ _)
  let vL : Fin d × {l : Fin m // l ≠ j} → L := fun p ↦
    algebraMap B L (Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr (p.1, p.2.1))))
  let t : D →+* L := MvPolynomial.eval₂Hom ct.toRingHom vL
  have htR (r : R) : t (algebraMap R D r) = algebraMap R L r := by
    rw [IsScalarTower.algebraMap_apply R T D]
    change t (MvPolynomial.C (algebraMap R T r)) = _
    dsimp only [t]
    rw [MvPolynomial.eval₂Hom_C]
    exact ct.commutes r
  have hsR : s.comp (algebraMap R L) = algebraMap R D := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change s (algebraMap B L (f (MvPolynomial.C c))) = _
      rw [MvPolynomial.aeval_C]
      change s (algebraMap B L (Ideal.Quotient.mk I
        (MvPolynomial.C (algebraMap k A c)))) = _
      rw [hs, hevC]
      change ca (algebraMap k A c) = algebraMap R D (MvPolynomial.C c)
      change MvPolynomial.C (TensorProduct.includeRight
        (algebraMap A A' (algebraMap k A c))) = _
      rw [← IsScalarTower.algebraMap_apply k A A']
      rw [TensorProduct.includeRight.commutes]
      change algebraMap k D c = algebraMap R D (algebraMap k R c)
      exact IsScalarTower.algebraMap_apply k R D c
    · intro i
      change s (algebraMap B L (f (MvPolynomial.X i))) = _
      rw [MvPolynomial.aeval_X]
      rw [hs]
      exact hevX (Sum.inl i)
  have hsca : s.comp caL.toRingHom = ca' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (a j))
    apply RingHom.ext
    intro c
    change s (caL (algebraMap A A' c)) = ca' (algebraMap A A' c)
    dsimp only [caL]
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
    change s (algebraMap B L (Ideal.Quotient.mk I (MvPolynomial.C c))) = ca c
    rw [hs]
    exact hevC c
  have hsR' (r : R) : s (algebraMap R L r) = algebraMap R D r :=
    DFunLike.congr_fun hsR r
  have hsca' (b : A') : s (caL b) = ca' b := DFunLike.congr_fun hsca b
  -- The composite on the free algebra fixes coefficients and variables.
  have hst : s.comp t = RingHom.id D := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change s (t (MvPolynomial.C c)) = MvPolynomial.C c
      dsimp only [t]
      rw [MvPolynomial.eval₂Hom_C]
      induction c using _root_.TensorProduct.inductionOn with
      | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul r b =>
        change s (ct (_root_.TensorProduct.tmul k r b)) =
          MvPolynomial.C (_root_.TensorProduct.tmul k r b)
        dsimp only [ct]
        rw [TensorProduct.lift_tmul, map_mul]
        change s (algebraMap R L r) * s (caL b) = _
        rw [hsR', hsca']
        change MvPolynomial.C (_root_.TensorProduct.tmul k r (1 : A')) *
          MvPolynomial.C (_root_.TensorProduct.tmul k (1 : R) b) = _
        rw [← map_mul, TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rintro ⟨i, l⟩
      change s (t (MvPolynomial.X (i, l))) = MvPolynomial.X (i, l)
      dsimp only [t]
      rw [MvPolynomial.eval₂Hom_X', hs, hevX]
      change z i l = MvPolynomial.X (i, l)
      simp [z, z₀, l.property]
  have htca (c : A) : t (ca c) = algebraMap A L c := by
    change t (MvPolynomial.C (TensorProduct.includeRight (algebraMap A A' c))) = _
    dsimp only [t]
    rw [MvPolynomial.eval₂Hom_C]
    change ct (TensorProduct.includeRight (algebraMap A A' c)) = _
    dsimp only [ct]
    rw [TensorProduct.includeRight_apply, TensorProduct.lift_tmul, map_one, one_mul]
    dsimp only [caL]
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
    rfl
  have htx (i : Fin d) : t (x i) =
      algebraMap B L (Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl i))) := by
    rw [htR]
    change algebraMap B L (f (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  let y : Fin d → Fin m → L := fun i l ↦
    algebraMap B L (Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr (i, l))))
  have htz₀ (i : Fin d) (l : Fin m) : t (z₀ i l) = if l = j then 0 else y i l := by
    dsimp only [z₀]
    split_ifs with h
    · exact map_zero t
    · exact MvPolynomial.eval₂Hom_X' ct.toRingHom vL (i, ⟨l, h⟩)
  have hrel (i : Fin d) :
      t (x i) ^ n = ∑ l, y i l * algebraMap A L (a l) := by
    have hz : Ideal.Quotient.mk I (rel i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    have hz' := congrArg (algebraMap B L) hz
    dsimp only [rel] at hz'
    simp only [map_sub, map_pow, map_sum, map_mul, map_zero] at hz'
    rw [sub_eq_zero] at hz'
    have hcoeff (c : A) : algebraMap B L (Ideal.Quotient.mk I (MvPolynomial.C c)) =
        algebraMap A L c := by
      change algebraMap B L (algebraMap A B c) = _
      exact (IsScalarTower.algebraMap_apply A B L c).symm
    simp only [hcoeff] at hz'
    rw [htx]
    exact hz'
  -- The quotient relation recovers the eliminated variable after multiplying by the unit.
  have htw (i : Fin d) : t (w i) = y i j := by
    apply (hu.map t).mul_left_injective
    rw [htca]
    dsimp only [w]
    rw [map_mul, map_sub, map_pow, map_sum]
    simp only [map_mul, htca, htz₀, ite_mul, zero_mul]
    have hinv' : t inv * algebraMap A L (a j) = 1 := by
      simpa only [map_mul, htca, map_one] using congrArg t hinv
    rw [mul_right_comm (t inv), hinv', one_mul]
    rw [hrel]
    rw [← Finset.sum_sub_distrib]
    simp only [sub_ite, sub_zero, sub_self]
    simp
  have htEv : t.comp ev = (algebraMap B L).comp (Ideal.Quotient.mk I) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change t (ev (MvPolynomial.C c)) = _
      rw [hevC, htca]
      rfl
    · rintro (i | ⟨i, l⟩)
      · change t (ev (MvPolynomial.X (Sum.inl i))) = _
        rw [hevX]
        exact htx i
      · change t (ev (MvPolynomial.X (Sum.inr (i, l)))) = _
        rw [hevX]
        change t (z i l) = y i l
        dsimp only [z]
        rw [map_add, htz₀]
        split_ifs with h
        · subst l
          rw [htw]
          simp
        · simp
  -- The other composite fixes the original quotient and hence its localization.
  have hts : t.comp s = RingHom.id L := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A B (a j)))
    apply RingHom.ext
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    change t (s (algebraMap B L (Ideal.Quotient.mk I p))) = _
    rw [hs]
    exact DFunLike.congr_fun htEv p
  exact ⟨{ t with
    invFun := s
    left_inv := fun p ↦ DFunLike.congr_fun hst p
    right_inv := fun p ↦ DFunLike.congr_fun hts p
    commutes' := htR }⟩

/-- Inverting one coefficient in the displayed relations yields a smooth algebra over
`k[X_i]`, provided the corresponding coefficient localization of `A` is smooth over `k`.

Source: Stacks Project, proof of Lemma 07FE, first paragraph.
(blueprint: lem-weil-pbc-popescu-polynomial-coefficient-localization-smooth).

Proof: fix `j`. Over `A_(a j)` each relation has an invertible coefficient of `Z_(i,j)`.
Solve it as `Z_(i,j) = (a j)⁻¹ * (X_i^n - Σ_(l ≠ j) Z_(i,l) a_l)`.
The quotient localized at `a j` is therefore canonically isomorphic, as a `k[X_i]`-algebra,
to the polynomial algebra in `Z_(i,l)` for `l ≠ j` over `A_(a j)[X_i]`.
Construct the forward map on all variables by the displayed formula and the inverse on the
remaining variables by their quotient classes. The equations show the two compositions
are identities. The base algebra `A_(a j)[X_i]` is smooth over `k[X_i]` by base change
of the assumed smooth map `k → A_(a j)`. Adjoining the remaining finitely many variables
is smooth, and composition and transport along the algebra equivalence give the result.
If `d = 0`, this is precisely the assumed smoothness. If `a j` is nilpotent, both localized
rings are zero and the same construction applies. The exponent may be zero; elimination
uses the invertibility of `a j`, not any condition on `n`. -/
theorem popescuPolynomialCoefficientLocalization_smooth
    {k : Type u} {A : Type v} [CommRing k] [CommRing A] [Algebra k A]
    (d n : ℕ) {m : ℕ} (a : Fin m → A) (j : Fin m)
    (hj : Smooth k (Localization.Away (a j))) :
    let P := MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A
    let B := P ⧸ Ideal.span (Set.range (fun i : Fin d ↦
      MvPolynomial.X (Sum.inl i) ^ n -
        ∑ l : Fin m, MvPolynomial.X (Sum.inr (i, l)) * MvPolynomial.C (a l)))
    let f : MvPolynomial (Fin d) k →ₐ[k] B :=
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))
    letI := f.toRingHom.toAlgebra
    Smooth (MvPolynomial (Fin d) k) (Localization.Away (algebraMap A B (a j))) := by
  classical
  dsimp only
  let P := MvPolynomial (Fin d ⊕ (Fin d × Fin m)) A
  let I : Ideal P := Ideal.span (Set.range (fun i : Fin d ↦
    MvPolynomial.X (Sum.inl i) ^ n -
      ∑ l : Fin m, MvPolynomial.X (Sum.inr (i, l)) * MvPolynomial.C (a l)))
  let B := P ⧸ I
  let f : MvPolynomial (Fin d) k →ₐ[k] B :=
    MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl i)))
  let : Algebra (MvPolynomial (Fin d) k) B := f.toRingHom.toAlgebra
  let T := _root_.TensorProduct k (MvPolynomial (Fin d) k) (Localization.Away (a j))
  have : Smooth k (Localization.Away (a j)) := hj
  have : Smooth (MvPolynomial (Fin d) k) T := inferInstance
  have : Smooth T (MvPolynomial (Fin d × {l : Fin m // l ≠ j}) T) := ⟨inferInstance, inferInstance⟩
  have : Smooth (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d × {l : Fin m // l ≠ j}) T) :=
    Smooth.comp (MvPolynomial (Fin d) k) T _
  obtain ⟨e⟩ := coefficientLocalization_equiv (k := k) d n a j
  exact Smooth.of_equiv e

end Algebra
