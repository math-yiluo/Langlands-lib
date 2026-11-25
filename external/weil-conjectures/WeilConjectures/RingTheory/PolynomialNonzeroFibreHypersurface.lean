/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import Mathlib.FieldTheory.Separable

/-!
# A hypersurface presentation of a nonzero polynomial fibre

Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph,
with the characteristic-zero separability argument in the proof of Proposition 07PV.
(blueprint: lem-weil-pbc-polynomial-nonzero-fibre-hypersurface)
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Choose a denominator-cleared generator using Mathlib's residue-field polynomial PID lemma.
The extended ideal is nonzero by injectivity and prime by disjointness from base constants. -/
private theorem exists_irreducible_fibre_generator
    (A : Type u) [CommRing A] [IsDomain A]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (hrA : r.comap (C : A →+* Polynomial A) = ⊥) :
    ∃ f ∈ r,
      Ideal.span {f.map (algebraMap A (⊥ : Ideal A).ResidueField)} =
        r.map (mapRingHom (algebraMap A (⊥ : Ideal A).ResidueField)) ∧
      Irreducible (f.map (algebraMap A (⊥ : Ideal A).ResidueField)) := by
  let K := (⊥ : Ideal A).ResidueField
  let : Algebra (Polynomial A) (Polynomial K) := Polynomial.algebra A K
  have : IsLocalization ((nonZeroDivisors A).map C) (Polynomial K) :=
    Polynomial.isLocalization _ _
  have hdisj : Disjoint (((nonZeroDivisors A).map C : Submonoid (Polynomial A)) :
      Set (Polynomial A)) (r : Set (Polynomial A)) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have hz : a = 0 := by
      have : a ∈ r.comap C := hmem
      simpa [hrA] using this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) hz
  have hprime : (r.map (mapRingHom (algebraMap A K))).IsPrime := by
    change (r.map (algebraMap (Polynomial A) (Polynomial K))).IsPrime
    exact IsLocalization.isPrime_of_isPrime_disjoint _ _ r inferInstance hdisj
  have hne : r.map (mapRingHom (algebraMap A K)) ≠ ⊥ := by
    exact (Ideal.map_eq_bot_iff_of_injective
      (Polynomial.map_injective _ (IsFractionRing.injective A K))).not.mpr hr
  obtain ⟨f, hfr, hf⟩ := Ideal.exists_mem_span_singleton_map_residueField_eq (⊥ : Ideal A) r
  refine ⟨f, hfr, hf, ?_⟩
  have hf0 : f.map (algebraMap A K) ≠ 0 := by
    intro h
    apply hne
    rw [← hf, h, Ideal.span_singleton_zero]
  exact ((Ideal.span_singleton_prime hf0).mp (hf.symm ▸ hprime)).irreducible

/-- Evaluate the fraction-field Bezout identity in the localization quotient.
The coefficient map exists because every nonzero base constant is inverted. -/
private theorem isUnit_derivative_of_separable_fraction
    (A : Type u) [CommRing A] [IsDomain A]
    (S : Type v) [CommRing S] [Algebra (Polynomial A) S]
    (f : Polynomial A)
    (hf : (f.map (algebraMap A (⊥ : Ideal A).ResidueField)).Separable) :
    let M := Submonoid.map
      ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
    let R := Localization M
    IsUnit (Ideal.Quotient.mk (Ideal.span ({algebraMap (Polynomial A) R f} : Set R))
      (algebraMap (Polynomial A) R (derivative f))) := by
  let K := (⊥ : Ideal A).ResidueField
  let M := Submonoid.map
    ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
  let R := Localization M
  let J := Ideal.span ({algebraMap (Polynomial A) R f} : Set R)
  let Q := R ⧸ J
  let φ : Polynomial A →+* Q := (Ideal.Quotient.mk J).comp (algebraMap _ R)
  have hconst : ∀ a : nonZeroDivisors A, IsUnit ((φ.comp C) a) := by
    intro a
    exact (IsLocalization.map_units (M := M) R
      ⟨algebraMap (Polynomial A) S (C a), ⟨a, a.property, rfl⟩⟩).map
      (Ideal.Quotient.mk J)
  let ψ : K →+* Q := IsLocalization.lift hconst
  let e : Polynomial K →+* Q := eval₂RingHom ψ (φ X)
  have he : e.comp (mapRingHom (algebraMap A K)) = φ := by
    ext a
    · simp [e, ψ, IsLocalization.lift_eq]
    · simp [e]
  have heval (p : Polynomial A) : e (p.map (algebraMap A K)) = φ p :=
    DFunLike.congr_fun he p
  have hz : φ f = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hcop := ((separable_def _).mp hf).map e
  rw [derivative_map, heval, heval, hz] at hcop
  exact isCoprime_zero_left.mp hcop

/-- Construct the fibre presentation from a specified irreducible fraction-field generator.
The field K[X]/rK[X] shows that every polynomial outside r maps to a unit in the quotient.
The residue-field, tensor-product, localization and quotient universal properties give
maps in both directions. Their composites agree with the identity on the generating maps. -/
private theorem fibre_equiv_of_fraction_generator
    (A : Type u) [CommRing A] [IsDomain A]
    (S : Type v) [CommRing S] [Algebra (Polynomial A) S]
    (r : Ideal (Polynomial A)) [r.IsPrime]
    (hrA : r.comap (C : A →+* Polynomial A) = ⊥)
    (f : Polynomial A) (hfr : f ∈ r)
    (hf : Ideal.span {f.map (algebraMap A (⊥ : Ideal A).ResidueField)} =
      r.map (mapRingHom (algebraMap A (⊥ : Ideal A).ResidueField)))
    (hirr : Irreducible (f.map (algebraMap A (⊥ : Ideal A).ResidueField))) :
    let M := Submonoid.map
      ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
    let R := Localization M
    Nonempty (r.Fiber S ≃+* R ⧸ Ideal.span ({algebraMap (Polynomial A) R f} : Set R)) := by
  let K := (⊥ : Ideal A).ResidueField
  let M := Submonoid.map
    ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
  let R := Localization M
  let J := Ideal.span ({algebraMap (Polynomial A) R f} : Set R)
  let Q := R ⧸ J
  let φ : Polynomial A →+* Q := (Ideal.Quotient.mk J).comp (algebraMap _ R)
  have hconst : ∀ a : nonZeroDivisors A, IsUnit ((φ.comp C) a) := by
    intro a
    exact (IsLocalization.map_units (M := M) R
      ⟨algebraMap (Polynomial A) S (C a), ⟨a, a.property, rfl⟩⟩).map
      (Ideal.Quotient.mk J)
  let ψ : K →+* Q := IsLocalization.lift hconst
  let e : Polynomial K →+* Q := eval₂RingHom ψ (φ X)
  have he : e.comp (mapRingHom (algebraMap A K)) = φ := by
    ext a
    · simp [e, ψ, IsLocalization.lift_eq]
    · simp [e]
  have heval (p : Polynomial A) : e (p.map (algebraMap A K)) = φ p :=
    DFunLike.congr_fun he p
  have hz : φ f = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let P := r.map (mapRingHom (algebraMap A K))
  have hPe : P ≤ RingHom.ker e := by
    change r.map (mapRingHom (algebraMap A K)) ≤ RingHom.ker e
    rw [← hf, Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr (by rw [heval, hz])
  have hrφ : r ≤ RingHom.ker φ := by
    intro p hp
    exact RingHom.mem_ker.mpr (by
      rw [← heval]
      exact hPe (Ideal.mem_map_of_mem _ hp))
  have hdisj : Disjoint (((nonZeroDivisors A).map C : Submonoid (Polynomial A)) :
      Set (Polynomial A)) (r : Set (Polynomial A)) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have hz : a = 0 := by
      have : a ∈ r.comap C := hmem
      simpa [hrA] using this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) hz
  let : Algebra (Polynomial A) (Polynomial K) := Polynomial.algebra A K
  have : IsLocalization ((nonZeroDivisors A).map C) (Polynomial K) :=
    Polynomial.isLocalization _ _
  have hcomap : P.comap (mapRingHom (algebraMap A K)) = r :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ inferInstance hdisj
  have : P.IsMaximal := by
    dsimp [P]
    rw [← hf]
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  let := Ideal.Quotient.field P
  let ē : Polynomial K ⧸ P →+* Q := Ideal.Quotient.lift P e hPe
  have hrunit : r.primeCompl ≤ (IsUnit.submonoid Q).comap φ := by
    intro p hp
    have hn : Ideal.Quotient.mk P (p.map (algebraMap A K)) ≠ 0 := by
      intro hz
      have hm : p.map (algebraMap A K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hz
      change p ∈ P.comap (mapRingHom (algebraMap A K)) at hm
      exact hp (hcomap ▸ hm)
    have hu := (isUnit_iff_ne_zero.mpr hn).map ē
    change IsUnit (φ p)
    simpa [ē, heval] using hu
  let κ : r.ResidueField →ₐ[Polynomial A] Q :=
    ⟨Ideal.ResidueField.lift r φ hrφ hrunit, by
      intro p
      exact Ideal.ResidueField.lift_algebraMap _ _ _ _ p⟩
  let β : S →ₐ[Polynomial A] Q := IsScalarTower.toAlgHom _ _ _
  let F := r.Fiber S
  let forward : F →+* Q :=
    (Algebra.TensorProduct.lift κ β fun _ _ ↦ .all _ _).toRingHom
  let τ : S →+* F := Algebra.TensorProduct.includeRight.toRingHom
  let ι : r.ResidueField →+* F :=
    Algebra.TensorProduct.includeLeftRingHom (R := Polynomial A) (B := S)
  have hιτ (p : Polynomial A) :
      ι (algebraMap (Polynomial A) r.ResidueField p) = τ (algebraMap (Polynomial A) S p) :=
    DFunLike.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap p
  have hτ : ∀ m : M, IsUnit (τ m) := by
    rintro ⟨m, a, ha, rfl⟩
    have hn : algebraMap (Polynomial A) r.ResidueField (C a) ≠ 0 := by
      rw [ne_eq, Ideal.algebraMap_residueField_eq_zero]
      intro h
      have : a ∈ r.comap C := h
      have hz : a = 0 := by simpa [hrA] using this
      exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) hz
    have hu := (isUnit_iff_ne_zero.mpr hn).map ι
    rwa [hιτ] at hu
  let backR : R →+* F := IsLocalization.lift hτ
  have hback : J ≤ RingHom.ker backR := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change backR (algebraMap (Polynomial A) R f) = 0
    rw [IsScalarTower.algebraMap_apply (Polynomial A) S R, IsLocalization.lift_eq]
    have hzκ : algebraMap (Polynomial A) r.ResidueField f = 0 := by
      exact Ideal.algebraMap_residueField_eq_zero.mpr hfr
    exact (hιτ f).symm.trans (by simpa only [map_zero] using congrArg ι hzκ)
  let backward : Q →+* F := Ideal.Quotient.lift J backR hback
  have hbackS (s : S) : backward (β s) = τ s := by
    change backR (algebraMap S R s) = τ s
    exact IsLocalization.lift_eq hτ s
  have hforwardS (s : S) : forward (τ s) = β s := by
    exact AlgHom.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight' κ β (fun _ _ ↦ .all _ _)) s
  have hforwardκ (x : r.ResidueField) : forward (ι x) = κ x := by
    exact AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft κ β (fun _ _ ↦ .all _ _)) x
  have hbackκ : backward.comp κ.toRingHom = ι := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    change backward (κ (algebraMap (Polynomial A) r.ResidueField p)) =
      ι (algebraMap (Polynomial A) r.ResidueField p)
    rw [κ.commutes]
    change backward (β (algebraMap (Polynomial A) S p)) = _
    rw [hbackS, hιτ]
  refine ⟨{ __ := forward, invFun := backward, left_inv := ?_, right_inv := ?_ }⟩
  · have h : backward.comp forward = RingHom.id F := by
      apply Algebra.TensorProduct.ringHom_ext
      · apply RingHom.ext
        intro x
        change backward (forward (ι x)) = ι x
        rw [hforwardκ]
        exact DFunLike.congr_fun hbackκ x
      · apply RingHom.ext
        intro s
        change backward (forward (τ s)) = τ s
        rw [hforwardS, hbackS]
    exact fun x ↦ DFunLike.congr_fun h x
  · have h : forward.comp backward = RingHom.id Q := by
      apply Ideal.Quotient.ringHom_ext
      apply IsLocalization.ringHom_ext M
      apply RingHom.ext
      intro s
      change forward (backward (β s)) = β s
      rw [hbackS, hforwardS]
    exact fun x ↦ DFunLike.congr_fun h x

/-- A nonzero polynomial prime over zero gives a hypersurface after inverting the
nonzero base elements, and its equation has invertible derivative in that quotient.
Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph,
and proof of Proposition 07PV, regular-base characteristic-zero case.
(blueprint: lem-weil-pbc-polynomial-nonzero-fibre-hypersurface)

Proof:
Let K be the fraction field of A. Since r contracts to zero, its extension to K[X]
is prime; since localization of the domain A[X] is injective, it is nonzero.
The principal ideal domain K[X] gives an irreducible generator g. Clear its finitely
many coefficient denominators and the denominator expressing g in the extended ideal
to obtain f in r whose image generates r K[X]. Multiplication by the resulting
nonzero scalar does not change this ideal. The contraction of (g) is r.
The quotient K[X]/(g) is a field and is the residue field of r: localizing A[X]/r
at nonzero constants already gives this field, so inverting all other nonzero
classes changes nothing. Thus, for any A[X]-algebra S, tensoring with this field
identifies r.Fiber S with R/(image f), where R inverts the nonzero constants in S.
In characteristic zero the irreducible g is separable, hence g and g' are coprime.
The scalar multiple representing f is also coprime to its derivative. A Bezout
identity in K[X] descends to R/(image f) and supplies an inverse for image(f').
These statements also hold for the zero S-algebra: all rings in the presentation
are zero, and zero is a unit in the zero ring. No choice of a ring construction is
made from this existence statement; R is the explicit localization below. -/
theorem nonzero_fibre_hypersurface_presentation
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    (S : Type v) [CommRing S] [Algebra (Polynomial A) S]
    (r : Ideal (Polynomial A)) [r.IsPrime] (hr : r ≠ ⊥)
    (hrA : r.comap (C : A →+* Polynomial A) = ⊥) :
    let M := Submonoid.map
      ((algebraMap (Polynomial A) S).comp C).toMonoidHom (nonZeroDivisors A)
    let R := Localization M
    ∃ f : Polynomial A,
      Nonempty (r.Fiber S ≃+* R ⧸ Ideal.span ({algebraMap (Polynomial A) R f} : Set R)) ∧
      IsUnit (Ideal.Quotient.mk (Ideal.span ({algebraMap (Polynomial A) R f} : Set R))
        (algebraMap (Polynomial A) R (derivative f))) := by
  obtain ⟨f, hfr, hf, hirr⟩ := exists_irreducible_fibre_generator A r hr hrA
  have : CharZero (⊥ : Ideal A).ResidueField :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (⊥ : Ideal A).ResidueField)
  exact ⟨f, fibre_equiv_of_fraction_generator A S r hrA f hfr hf hirr,
    isUnit_derivative_of_separable_fraction A S f hirr.separable⟩

end Polynomial
