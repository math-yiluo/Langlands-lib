/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AsSubring
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.FiniteOverNagata

/-! # A principal localization of a fractional monogenic algebra
Source: Stacks Project, Algebra, Tag 0334, Step 5, and Tag 032U.
(blueprint: lem-weil-pbc-monogenic-principal-localization-model). -/

@[expose] public section

universe u v

open scoped nonZeroDivisors

/-- Localizing coefficients and a monogenic algebra at the same nonzero coefficient
produces a monogenic presentation, with explicit compatibility on coefficients and generator.
Source: Stacks Project, Algebra, Tag 0334, Step 5, and Tag 032U.
(blueprint: lem-weil-pbc-monogenic-principal-localization-model).

Proof: Let B = R_a. Since a is nonzero, B is a normal domain, is Nagata by
Tag 032U, and embeds in K. Extend R -> K across B using localization; K is
still a fraction field of B. Let A = ULift B in Type(max u v). Transport the
fraction-field and normality properties through ULift.ringEquiv. The map B -> A
is finite and bijective, so finite Nagata ascent proves A Nagata. Set L = Frac(A),
and use uniqueness of fraction fields to identify K and L over A. Let y be the
image of x. Restrict this field embedding to g : S -> A[y]. The image g(a) is a
unit, so g extends to e₀ : S_a -> A[y]. Injectivity follows from the injective
maps S -> S_a and S -> A[y]. For surjectivity, map B into S_a by coefficient
localization and hence A into S_a by ULift.down. The composite with e₀ is the
coefficient inclusion A -> A[y], checked on R by localization extensionality.
Also y is the image of x. Induction on the adjoin therefore shows every element
of A[y] belongs to the range of e₀. Bundle the bijective homomorphism as e;
localization's lift equations give its coefficient and generator equations. -/
theorem exists_monogenic_principal_localization_model
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (a : R) (ha : a ≠ 0) :
    ∃ (A L : Type (max u v)) (_ : CommRing A) (_ : IsDomain A)
      (_ : IsIntegrallyClosed A) (_ : Field L) (_ : Algebra A L)
      (_ : IsFractionRing A L),
      IsNagataRing A ∧ ∃ (y : L) (c : R →+* A), Function.Injective c ∧ IsUnit (c a) ∧
        ∃ e : Localization.Away
          (algebraMap R (Algebra.adjoin R ({x} : Set K)) a) ≃+*
            Algebra.adjoin A ({y} : Set L),
          (∀ r : R,
            e (algebraMap _ _ (algebraMap R (Algebra.adjoin R ({x} : Set K)) r)) =
              algebraMap A _ (c r)) ∧
          e (algebraMap _ _
            (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
              Algebra.adjoin R ({x} : Set K))) =
            (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
              Algebra.adjoin A ({y} : Set L))  := by
  classical
  let B := Localization.Away a
  have hp : Submonoid.powers a ≤ R⁰ := by
    rintro r ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ ha)
  let : IsDomain B := IsLocalization.Away.isDomain _ ha
  let : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B
    (Submonoid.powers a) hp
  have hB : IsNagataRing B := (isNagataRing_localization R (Submonoid.powers a) hR).1
  let : Algebra B K :=
    (Localization.mapToFractionRing K (Submonoid.powers a) B hp).toRingHom.toAlgebra
  let : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq'
    (Localization.mapToFractionRing K (Submonoid.powers a) B hp).comp_algebraMap.symm
  let : IsFractionRing B K := IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers a) B K hp
  let A := ULift.{v} B
  let : IsDomain A := (ULift.ringEquiv : A ≃+* B).injective.isDomain _
  let : Algebra A K := ULift.algebra' B K
  let : IsFractionRing A K := IsFractionRing.of_ringEquiv_left
    (ULift.ringEquiv : A ≃+* B) (fun _ ↦ rfl)
  let : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv
    (ULift.ringEquiv : A ≃+* B).symm
  let : Module.Finite B A := Module.Finite.of_surjective
    (Algebra.linearMap B A) (fun b ↦ ⟨b.down, rfl⟩)
  have hA : IsNagataRing A := (finite_over_nagata_is_nagata B A hB).1
  let L := FractionRing A
  let φ : K ≃ₐ[A] L := IsLocalization.algEquiv A⁰ K L
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R K r = algebraMap B K (algebraMap R B r)
    exact IsScalarTower.algebraMap_apply R B K r)
  let φR : K →ₐ[R] L := φ.toAlgHom.restrictScalars R
  let y : L := φ x
  let S := Algebra.adjoin R ({x} : Set K)
  let T := Algebra.adjoin A ({y} : Set L)
  have hsub : S ≤ (T.restrictScalars R).comap φR := by
    apply Algebra.adjoin_le
    intro z hz
    obtain rfl : z = x := Set.mem_singleton_iff.mp hz
    exact Algebra.subset_adjoin (Set.mem_singleton y)
  let g : S →ₐ[R] T := (φR.comp S.val).codRestrict (T.restrictScalars R)
    (fun z ↦ hsub z.property)
  let s := algebraMap R S a
  let Q := Localization.Away s
  have hgcoef (r : R) : g (algebraMap R S r) = algebraMap A T (algebraMap R A r) := by
    exact g.commutes r
  have hunit : IsUnit (algebraMap R A a) :=
    (IsLocalization.Away.algebraMap_isUnit (S := B) a).map (algebraMap B A)
  have hgs : IsUnit (g s) := by
    rw [hgcoef]
    exact hunit.map (algebraMap A T)
  let e₀ : Q →+* T := IsLocalization.Away.lift s hgs
  have hsne : s ≠ 0 := by
    intro hzero
    have hz : algebraMap R K a = 0 := congrArg Subtype.val hzero
    exact ha ((IsFractionRing.injective R K) (hz.trans (map_zero _).symm))
  have hsp : Submonoid.powers s ≤ S⁰ := by
    rintro t ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hsne)
  have heinj : Function.Injective e₀ := by
    apply (IsLocalization.lift_injective_iff _).2
    intro b c
    constructor
    · intro h
      exact congrArg g ((IsLocalization.injective Q hsp) h)
    · intro h
      have heq : b = c := by
        apply Subtype.ext
        exact φ.injective (congrArg Subtype.val h)
      exact congrArg (algebraMap S Q) heq
  let kB : B →+* Q := IsLocalization.Away.map B Q (algebraMap R S) a
  let kA : A →+* Q := kB.comp ULift.ringEquiv.toRingHom
  have hekB : e₀.comp kB = (algebraMap A T).comp (algebraMap B A) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    simp only [RingHom.comp_apply]
    rw [show kB (algebraMap R B r) = algebraMap S Q (algebraMap R S r) from
      IsLocalization.map_eq _ r, IsLocalization.Away.lift_eq]
    exact congrArg Subtype.val (hgcoef r)
  have hekA (b : A) : e₀ (kA b) = algebraMap A T b := by
    exact RingHom.congr_fun hekB b.down
  have hesurj : Function.Surjective e₀ := by
    rintro ⟨t, ht⟩
    have hm : (⟨t, ht⟩ : T) ∈ e₀.range := by
      induction ht using Algebra.adjoin_induction with
      | mem z hz =>
        obtain rfl : z = y := Set.mem_singleton_iff.mp hz
        exact ⟨algebraMap S Q ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩,
          by rw [IsLocalization.Away.lift_eq]; rfl⟩
      | algebraMap b => exact ⟨kA b, hekA b⟩
      | add z w hz hw hzi hwi => exact e₀.range.add_mem hzi hwi
      | mul z w hz hw hzi hwi => exact e₀.range.mul_mem hzi hwi
    exact hm
  let e : Q ≃+* T := RingEquiv.ofBijective e₀ ⟨heinj, hesurj⟩
  refine ⟨A, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hA, y, algebraMap R A, ?_, hunit, e, ?_, ?_⟩
  · exact (ULift.ringEquiv : A ≃+* B).symm.injective.comp (IsLocalization.injective B hp)
  · intro r
    change e₀ (algebraMap S Q (algebraMap R S r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact hgcoef r
  · change e₀ (algebraMap S Q _) = _
    rw [IsLocalization.Away.lift_eq]
    rfl

