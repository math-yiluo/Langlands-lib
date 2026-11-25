/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.PopescuAuxiliaryAlgebraLocalizations
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Smooth principal localizations of the explicit Popescu auxiliary quotient

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA (lemma-delocalize-height-zero),
the auxiliary quotient and its two localizations.
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/

@[expose] public section

universe u v w

open scoped BigOperators TensorProduct
open MvPolynomial

namespace Algebra

/-- Variable indices `x,y,z,t` for the auxiliary quotient. The lift of `z` fixes the
carrier universe without choosing any algebra from an existence theorem.
Source: Stacks Project, Lemma 07FA. 
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/
abbrev PopescuAuxVars (ι : Type v) (k m : ℕ) :=
  Fin k ⊕ (ι ⊕ (ULift.{u} Unit ⊕ (ι × Fin m)))

/-- The explicit polynomial ring in the auxiliary variables of Lemma 07FA. 
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/
abbrev PopescuAuxPoly (A : Type v) [CommRing A] (ι : Type w) (k m : ℕ) :=
  MvPolynomial (PopescuAuxVars.{u} ι k m) A

/-- Include the original polynomial variables into the auxiliary polynomial ring.
Source: Stacks Project, Lemma 07FA. 
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/
noncomputable def popescuAuxIncl (A : Type v) [CommRing A] (ι : Type w) (k m : ℕ) :
    MvPolynomial (Fin k) A →ₐ[A] PopescuAuxPoly.{u} A ι k m :=
  MvPolynomial.aeval fun j ↦ MvPolynomial.X (Sum.inl j)

/-- The relations are `f_j - ∑ y_i t_ij` and `z y_i`.
Source: Stacks Project, Lemma 07FA. 
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/
noncomputable def popescuAuxIdeal (A : Type v) [CommRing A] (ι : Type w) [Fintype ι]
    (k m : ℕ) (f : Fin m → MvPolynomial (Fin k) A) :
    Ideal (PopescuAuxPoly.{u} A ι k m) := by
  classical
  exact Ideal.span
    (Set.range (fun j ↦ popescuAuxIncl A ι k m (f j) -
      ∑ i : ι, MvPolynomial.X (Sum.inr (Sum.inl i)) *
        MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
     Set.range (fun i : ι ↦
      MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ⟨()⟩))) *
        MvPolynomial.X (Sum.inr (Sum.inl i))))

/-- The actual auxiliary algebra, a quotient by the displayed relations.
Source: Stacks Project, Lemma 07FA. 
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)
-/
abbrev PopescuAuxQuot (A : Type v) [CommRing A] (ι : Type w) [Fintype ι]
    (k m : ℕ) (f : Fin m → MvPolynomial (Fin k) A) :=
  PopescuAuxPoly.{u} A ι k m ⧸ popescuAuxIdeal A ι k m f

noncomputable section
variable (A : Type v) [CommRing A] (ι : Type v) [Fintype ι] (k m : ℕ)
variable (f : Fin m → MvPolynomial (Fin k) A)
private abbrev StdVars := Fin k ⊕ (Fin (Fintype.card ι) ⊕ (Unit ⊕ (Fin (Fintype.card ι) × Fin m)))
private def stdIncl : MvPolynomial (Fin k) A →ₐ[A] MvPolynomial (StdVars ι k m) A :=
  aeval fun j ↦ X (Sum.inl j)
private def stdIdeal : Ideal (MvPolynomial (StdVars ι k m) A) := by
  classical
  exact Ideal.span
    (Set.range (fun j ↦ stdIncl A ι k m (f j) -
      ∑ i : Fin (Fintype.card ι), X (Sum.inr (Sum.inl i)) *
        X (Sum.inr (Sum.inr (Sum.inr (i, j))))) ∪
     Set.range (fun i : Fin (Fintype.card ι) ↦
      X (Sum.inr (Sum.inr (Sum.inl ()))) * X (Sum.inr (Sum.inl i))))
private def varsEquiv : StdVars ι k m ≃ PopescuAuxVars.{u} ι k m :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Fintype.equivFin ι).symm
    (Equiv.sumCongr Equiv.ulift.symm
      (Equiv.prodCongr (Fintype.equivFin ι).symm (Equiv.refl _))))
private def polyEquiv : MvPolynomial (StdVars ι k m) A ≃ₐ[A] PopescuAuxPoly.{u} A ι k m :=
  renameEquiv A (varsEquiv ι k m)
private theorem polyEquiv_incl (p : MvPolynomial (Fin k) A) :
    polyEquiv.{u} A ι k m (stdIncl A ι k m p) = popescuAuxIncl A ι k m p := by
  have h : (polyEquiv.{u} A ι k m).toAlgHom.comp (stdIncl A ι k m) =
      popescuAuxIncl A ι k m := by
    ext j
    simp [polyEquiv, varsEquiv, stdIncl, popescuAuxIncl]
  exact AlgHom.congr_fun h p
private theorem map_stdIdeal :
    Ideal.map (polyEquiv.{u} A ι k m).toRingEquiv.toRingHom (stdIdeal A ι k m f) =
      popescuAuxIdeal A ι k m f := by
  classical
  rw [stdIdeal, popescuAuxIdeal, Ideal.map_span, Set.image_union]
  congr 1
  apply congrArg₂ (· ∪ ·)
  · rw [← Set.range_comp]
    congr 1
    funext j
    change polyEquiv.{u} A ι k m (stdIncl A ι k m (f j) - _) = _
    rw [map_sub, polyEquiv_incl, map_sum]
    congr 1
    apply Fintype.sum_equiv (Fintype.equivFin ι).symm
    intro i
    simp [polyEquiv, varsEquiv]
  · rw [← Set.range_comp]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨(Fintype.equivFin ι).symm i, ?_⟩
      simp [polyEquiv, varsEquiv]
    · rintro ⟨i, rfl⟩
      refine ⟨Fintype.equivFin ι i, ?_⟩
      simp [polyEquiv, varsEquiv]
end
private theorem smooth_image_localization
    (R : Type u) (A : Type v) (D : Type*)
    [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra R D] [Algebra A D] [IsScalarTower R A D]
    [Smooth A D] (a : A) [Smooth R (Localization.Away a)] :
    Smooth R (Localization.Away (algebraMap A D a)) := by
  let T := Localization.Away a ⊗[A] D
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R D T := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away a),
      IsScalarTower.algebraMap_apply R A D]
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul]
  have : Smooth (Localization.Away a) T := inferInstance
  have : Smooth R T := Smooth.comp R (Localization.Away a) T
  exact Smooth.of_equiv
    ((IsLocalization.Away.tensorRightEquiv (r := a) (A := Localization.Away a) D).restrictScalars R)
private theorem std_smooth
    (R : Type u) (A : Type v) (C : Type (max u v))
    [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (ι : Type v) [Fintype ι] [Nonempty ι] (k m : ℕ)
    (f : Fin m → MvPolynomial (Fin k) A)
    (q : MvPolynomial (Fin k) A →ₐ[A] C) (hq : Function.Surjective q)
    (hker : Ideal.span (Set.range f) = RingHom.ker q.toRingHom)
    (p : MvPolynomial (Fin k) A) (hp : Smooth R (Localization.Away (q p)))
    (a : ι → A) (ha : ∀ i, Smooth R (Localization.Away (a i))) :
    Smooth R (Localization.Away
      (Ideal.Quotient.mkₐ A (stdIdeal A ι k m f)
        (X (Sum.inr (Sum.inr (Sum.inl ())))) *
       Ideal.Quotient.mkₐ A (stdIdeal A ι k m f) (stdIncl A ι k m p))) ∧
    (∀ i : Fin (Fintype.card ι), Smooth R (Localization.Away
      (algebraMap A (MvPolynomial (StdVars ι k m) A ⧸ stdIdeal A ι k m f)
          (a ((Fintype.equivFin ι).symm i)) *
       Ideal.Quotient.mkₐ A (stdIdeal A ι k m f) (X (Sum.inr (Sum.inl i)))))) := by
  classical
  let J := stdIdeal A ι k m f
  let B := MvPolynomial (StdVars ι k m) A ⧸ J
  let mk : MvPolynomial (StdVars ι k m) A →ₐ[A] B := Ideal.Quotient.mkₐ A J
  let z : B := mk (X (Sum.inr (Sum.inr (Sum.inl ()))))
  let cp : B := mk (stdIncl A ι k m p)
  let Cp := MvPolynomial (Fin k) A ⧸ Ideal.span (Set.range f)
  let c : Cp := Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)) p
  let ec : Cp ≃ₐ[A] C := (Ideal.quotientEquivAlgOfEq A hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hq)
  have hec : ec c = q p := by
    dsimp only [ec, c, AlgEquiv.trans_apply]
    exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective hq)
      (Ideal.quotientEquivAlgOfEq_mk A hker p)).trans
        (Ideal.quotientKerAlgEquivOfSurjective_mk hq p)
  let : Smooth R (Localization.Away (q p)) := hp
  let el : Localization.Away c ≃ₐ[R] Localization.Away (q p) :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers c)
      (T := Submonoid.powers (q p)) _ _ (ec.restrictScalars R)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hec)
  have : Smooth R (Localization.Away c) := Smooth.of_equiv el.symm
  let T := MvPolynomial ((Fin (Fintype.card ι) × Fin m) ⊕ Unit) Cp
  let tz : T := X (Sum.inr ())
  let Tz := Localization.Away tz
  have hlocal := popescu_auxiliaryAlgebra_localizations A k m (Fintype.card ι)
    (Fintype.card_pos_iff.mpr inferInstance) f
  obtain ⟨⟨phi, hphiX, hphiY, hphiZ, hphiT, e, he⟩, hY⟩ := hlocal
  let e' : Localization.Away z ≃ₐ[A] Tz := e
  have hphiP : phi cp = algebraMap T Tz (MvPolynomial.C c) := by
    have h : phi.comp ((Ideal.Quotient.mkₐ A J).comp (stdIncl A ι k m)) =
        (IsScalarTower.toAlgHom A T Tz).comp
          ((IsScalarTower.toAlgHom A Cp T).comp
            (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)))) := by
      ext j
      change phi (mk (stdIncl A ι k m (X j))) =
        algebraMap T Tz
          (MvPolynomial.C (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)) (X j)))
      rw [show stdIncl A ι k m (X j) = X (Sum.inl j) from MvPolynomial.aeval_X _ j]
      exact hphiX j
    exact AlgHom.congr_fun h p
  have hcp : e' (algebraMap B (Localization.Away z) cp) =
      algebraMap Cp Tz c := by
    change e (algebraMap B (Localization.Away z) cp) = algebraMap T Tz (MvPolynomial.C c)
    exact (he cp).trans hphiP
  have : Smooth Cp T := {}
  have : Smooth T Tz := Smooth.of_isLocalization_Away tz
  have : Smooth Cp Tz := Smooth.comp Cp T Tz
  have : Smooth R (Localization.Away (algebraMap Cp Tz c)) :=
    smooth_image_localization R Cp Tz c
  let ep : Localization.Away (algebraMap B (Localization.Away z) cp) ≃ₐ[R]
      Localization.Away (algebraMap Cp Tz c) :=
    IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers (algebraMap B (Localization.Away z) cp))
      (T := Submonoid.powers (algebraMap Cp Tz c)) _ _ (e'.restrictScalars R)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hcp)
  have : Smooth R (Localization.Away (algebraMap B (Localization.Away z) cp)) :=
    Smooth.of_equiv ep.symm
  constructor
  · exact Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (z * cp))
      (Localization.Away (algebraMap B (Localization.Away z) cp))
      (Localization.Away (z * cp))).restrictScalars R)
  · intro i
    let ai := a ((Fintype.equivFin ι).symm i)
    have : Smooth R (Localization.Away ai) := ha _
    let y : B := mk (X (Sum.inr (Sum.inl i)))
    let Q := MvPolynomial (Fin k ⊕ (Fin (Fintype.card ι) ⊕
      ({j : Fin (Fintype.card ι) // j ≠ i} × Fin m))) A
    let qy : Q := X (Sum.inr (Sum.inl i))
    obtain ⟨ey, hey, _⟩ := hY i
    have : Smooth A Q := {}
    have : Smooth Q (Localization.Away qy) := Smooth.of_isLocalization_Away qy
    have : Smooth A (Localization.Away qy) := Smooth.comp A Q (Localization.Away qy)
    have : Smooth A (Localization.Away y) := Smooth.of_equiv ey
    have : Smooth R (Localization.Away (algebraMap A (Localization.Away y) ai)) :=
      smooth_image_localization R A (Localization.Away y) ai
    have hmap : algebraMap A (Localization.Away y) ai =
        algebraMap B (Localization.Away y) (algebraMap A B ai) := by
      exact IsScalarTower.algebraMap_apply A B (Localization.Away y) ai
    rw [hmap] at this
    exact Smooth.of_equiv ((IsLocalization.algEquiv
      (Submonoid.powers (algebraMap A B ai * y))
      (Localization.Away (algebraMap B (Localization.Away y) (algebraMap A B ai)))
      (Localization.Away (algebraMap A B ai * y))).restrictScalars R)

/-- The two smoothness calculations for the explicit quotient. Neither the evaluation
into a target algebra nor any annihilator is part of this geometric assertion.

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA (lemma-delocalize-height-zero),
last paragraph, with the polynomial variables in the first localization corrected to `t`.
(blueprint: lem-weil-pbc-popescu-auxiliary-quotient-smooth)

Proof: Invert z. The relations z*y_i = 0 force all y_i to vanish, and the other
relations become f_j = 0. The presentation q therefore identifies this localization
with C[t_ij,z]_z. The class of p corresponds to q(p). Inverting it as well gives a
localization of a polynomial algebra over C_(q(p)), smooth over R by hypothesis,
polynomial smoothness, localization smoothness, and composition. Iterated localization
identifies this with the localization at z*p. For a fixed i, invert y_i. Then z = 0,
and each relation uniquely eliminates t_ij in row i as
(f_j - sum_{h != i} y_h*t_hj)/y_i. The resulting ring is a localization of a polynomial
algebra over A. Inverting a_i too gives a localization of a polynomial algebra over
A_(a_i), smooth over R by the same argument. This is the localization at a_i*y_i.
The index type is nonempty. These identifications are the auxiliary localization calculations in
lem-weil-pbc-popescu-height-zero-auxiliary-algebra-localizations, reindexed along a
finite equivalence. Empty generator and relation lists and zero rings are allowed;
localization at zero gives the zero ring and the same universal properties apply.
-/
theorem popescuAuxQuot_smooth_localizations
    (R : Type u) (A : Type v) (C : Type (max u v))
    [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (ι : Type v) [Fintype ι] [Nonempty ι] (k m : ℕ)
    (f : Fin m → MvPolynomial (Fin k) A)
    (q : MvPolynomial (Fin k) A →ₐ[A] C) (hq : Function.Surjective q)
    (hker : Ideal.span (Set.range f) = RingHom.ker q.toRingHom)
    (p : MvPolynomial (Fin k) A) (hp : Smooth R (Localization.Away (q p)))
    (a : ι → A) (ha : ∀ i, Smooth R (Localization.Away (a i))) :
    Smooth R (Localization.Away
      (Ideal.Quotient.mkₐ A (popescuAuxIdeal.{u} A ι k m f)
        (MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ⟨()⟩)))) *
       Ideal.Quotient.mkₐ A (popescuAuxIdeal.{u} A ι k m f)
        (popescuAuxIncl.{u} A ι k m p))) ∧
    (∀ i : ι, Smooth R (Localization.Away
      (algebraMap A (PopescuAuxQuot.{u} A ι k m f) (a i) *
       Ideal.Quotient.mkₐ A (popescuAuxIdeal.{u} A ι k m f)
        (MvPolynomial.X (Sum.inr (Sum.inl i)))))) := by
  classical
  have hs := std_smooth R A C ι k m f q hq hker p hp a ha
  let B₀ := MvPolynomial (StdVars ι k m) A ⧸ stdIdeal A ι k m f
  let B := PopescuAuxQuot.{u} A ι k m f
  let mk₀ : MvPolynomial (StdVars ι k m) A →ₐ[A] B₀ :=
    Ideal.Quotient.mkₐ A (stdIdeal A ι k m f)
  let mk : PopescuAuxPoly.{u} A ι k m →ₐ[A] B :=
    Ideal.Quotient.mkₐ A (popescuAuxIdeal.{u} A ι k m f)
  let eb : B₀ ≃ₐ[A] B := Ideal.quotientEquivAlg _ _ (polyEquiv.{u} A ι k m)
    (map_stdIdeal A ι k m f).symm
  have heb (x : MvPolynomial (StdVars ι k m) A) :
      eb (mk₀ x) = mk (polyEquiv A ι k m x) :=
    Ideal.quotientEquivAlg_mk _ _ _ x
  have hX (j : StdVars ι k m) : eb (mk₀ (X j)) = mk (X (varsEquiv ι k m j)) := by
    rw [heb]
    simp [polyEquiv]
  have hz : eb (mk₀ (X (Sum.inr (Sum.inr (Sum.inl ()))))) =
      mk (X (Sum.inr (Sum.inr (Sum.inl ⟨()⟩)))) := by
    rw [hX]
    rfl
  have hp' : eb (mk₀ (stdIncl A ι k m p)) = mk (popescuAuxIncl.{u} A ι k m p) := by
    rw [heb, polyEquiv_incl]
  have transport (b : B₀) (hb : Smooth R (Localization.Away b)) :
      Smooth R (Localization.Away (eb b)) := by
    let : Smooth R (Localization.Away b) := hb
    exact Smooth.of_equiv (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers b) (T := Submonoid.powers (eb b))
      (Localization.Away b) (Localization.Away (eb b)) (eb.restrictScalars R)
      (Submonoid.map_powers _ _))
  constructor
  · have h := transport _ hs.1
    rw [map_mul, hz, hp'] at h
    exact h
  · intro i
    have h := transport _ (hs.2 (Fintype.equivFin ι i))
    rw [map_mul, eb.commutes, hX] at h
    have hi : (Fintype.equivFin ι).symm (Fintype.equivFin ι i) = i :=
      Equiv.symm_apply_apply _ _
    have hv : varsEquiv.{u} ι k m (Sum.inr (Sum.inl (Fintype.equivFin ι i))) =
        Sum.inr (Sum.inl i) := by
      change Sum.inr (Sum.inl ((Fintype.equivFin ι).symm (Fintype.equivFin ι i))) = _
      rw [hi]
    rw [hi, hv] at h
    exact h


end Algebra
