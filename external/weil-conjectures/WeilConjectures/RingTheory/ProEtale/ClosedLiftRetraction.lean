/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction

/-!
# Retractions and clopen subsets of the ind-étale closed lift

For an ind-étale `A ⧸ I`-algebra `C̄`, the lift `H_A(C̄)` of `Algebra.ClosedLift` is the
coreflection of `C̄` into ind-étale `A`-algebras: for every ind-étale `A`-algebra `D`, composition
with `H_A(C̄) ⟶ C̄` is a bijection `Hom_A(D, H_A(C̄)) ≃ Hom_A(D, C̄)`
(`Algebra.ClosedLift.homEquiv`, a reformulation of the adjunction
`Algebra.ClosedLift.exists_natural_homEquiv`, blueprint
`proposition-extension-zero-restriction-closed-subscheme`).

Consequences: retractions of faithfully flat ind-étale covers of `C̄` lift to `H_A(C̄)`
(`Algebra.ClosedLift.exists_retraction`), and every nonempty clopen subset of `Spec H_A(C̄)` meets
`Spec C̄` (`Algebra.ClosedLift.exists_comap_mem_of_isClopen`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

section HomEquiv

variable (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
  [Algebra.IndEtale (A ⧸ I) C]

include I

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` is a bijection
`Hom_A(D, H_A(C̄)) → Hom_A(D, C̄)`: this is the Hom equivalence of
`Algebra.ClosedLift.exists_natural_homEquiv` composed with
`Hom_{A ⧸ I}(D ⧸ I D, C̄) ≃ Hom_A(D, C̄)`. -/
theorem bijective_comp_toAlgHom (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    Function.Bijective (fun ψ : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp ψ) := by
  obtain ⟨β, hβ⟩ := exists_natural_homEquiv A I
  have h := hβ (CommAlgCat.of A D) (CommAlgCat.of A C)
  let : Algebra (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  refine ⟨fun f g hfg ↦ ?_, fun q ↦ ?_⟩
  · refine (β (CommAlgCat.of A D) (CommAlgCat.of A C)).injective (AlgHom.ext fun x ↦ ?_)
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [h.2.1 f d, h.2.1 g d]
    exact DFunLike.congr_fun hfg d
  · have hker : I.map (algebraMap A D) ≤ RingHom.ker q.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change q (algebraMap A D a) = 0
      rw [q.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    let q' : D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C :=
      { __ := Ideal.Quotient.lift _ q.toRingHom hker
        commutes' := by
          intro a
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact (q.commutes a).trans (IsScalarTower.algebraMap_apply A (A ⧸ I) C a) }
    refine ⟨(β (CommAlgCat.of A D) (CommAlgCat.of A C)).symm q', AlgHom.ext fun d ↦ ?_⟩
    have := h.2.1 ((β (CommAlgCat.of A D) (CommAlgCat.of A C)).symm q') d
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- For an ind-étale `A`-algebra `D`, composition with `H_A(C̄) ⟶ C̄` identifies
`Hom_A(D, H_A(C̄))` with `Hom_A(D, C̄)`. -/
noncomputable def homEquiv (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃ (D →ₐ[A] C) :=
  Equiv.ofBijective _ (bijective_comp_toAlgHom I D)

@[simp]
lemma homEquiv_apply (D : Type u) [CommRing D] [Algebra A D] [Algebra.IndEtale A D]
    (ψ : D →ₐ[A] ClosedLift A C) : homEquiv I D ψ = (toAlgHom A C).comp ψ :=
  rfl

end HomEquiv

/-! ### Retractions of faithfully flat ind-étale covers -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Base change of an ind-étale algebra is ind-étale. -/
lemma indEtale_tensorProduct (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.IndEtale R T] :
    Algebra.IndEtale S (TensorProduct R S T) :=
  (RingHom.IndEtale.algebraMap_iff _ _).mp (RingHom.IndEtale.isStableUnderBaseChange R T S
    (TensorProduct R S T) ((RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance))

/-- If every faithfully flat ind-étale `C̄`-algebra has a retraction (e.g. `C̄` is
w-contractible), then every faithfully flat ind-étale `H_A(C̄)`-algebra `T` has a retraction:
reduce `T` along `H_A(C̄) ⟶ C̄`, retract there, and lift the resulting map `T ⟶ C̄` to `H_A(C̄)`
by the universal property `Algebra.ClosedLift.homEquiv`; it is a retraction by uniqueness. -/
theorem exists_retraction (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    (T : Type u) [CommRing T] [Algebra (ClosedLift A C) T] [Algebra.IndEtale (ClosedLift A C) T]
    [Module.FaithfullyFlat (ClosedLift A C) T] :
    ∃ f : T →+* ClosedLift A C, f.comp (algebraMap (ClosedLift A C) T) = RingHom.id _ := by
  let H := ClosedLift A C
  let : Algebra H C := (toAlgHom A C).toRingHom.toAlgebra
  have : Algebra.IndEtale C (TensorProduct H C T) := indEtale_tensorProduct H C T
  obtain ⟨r, hr⟩ := hC (TensorProduct H C T)
  let : Algebra A T := Algebra.compHom T (algebraMap A H)
  have : IsScalarTower A H T := .of_algebraMap_eq' rfl
  have : Algebra.IndEtale A T := Algebra.IndEtale.trans A H T
  have key : ∀ h : H, r ((1 : C) ⊗ₜ[H] algebraMap H T h) = toAlgHom A C h := by
    intro h
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    exact RingHom.congr_fun hr (toAlgHom A C h)
  let f₀ : T →ₐ[A] C :=
    { toRingHom := r.comp (Algebra.TensorProduct.includeRight : T →ₐ[H] TensorProduct H C T)
      commutes' := fun a ↦ by
        change r ((1 : C) ⊗ₜ[H] algebraMap H T (algebraMap A H a)) = _
        rw [key, AlgHom.commutes] }
  refine ⟨((homEquiv I T).symm f₀).toRingHom, ?_⟩
  have : ((homEquiv I T).symm f₀).comp (IsScalarTower.toAlgHom A H T) = AlgHom.id A H := by
    apply (homEquiv I H).injective
    ext h
    simp only [homEquiv_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    have := DFunLike.congr_fun ((homEquiv I T).apply_symm_apply f₀) (algebraMap H T h)
    rw [homEquiv_apply, AlgHom.comp_apply] at this
    rw [this]
    exact key h
  exact congrArg AlgHom.toRingHom this

/-- Every nonempty clopen subset of `Spec H_A(C̄)` meets the closed fibre `Spec C̄`: a nonzero
idempotent `e` of `H_A(C̄)` has nonzero image in `C̄`, since otherwise `1 - e` would be a unit
(`Algebra.ClosedLift.isUnit_of_isUnit_image`). -/
theorem exists_comap_mem_of_isClopen {s : Set (PrimeSpectrum (ClosedLift A C))} (hs : IsClopen s)
    (hne : s.Nonempty) :
    ∃ q : PrimeSpectrum C, PrimeSpectrum.comap (toAlgHom A C : ClosedLift A C →+* C) q ∈ s := by
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hs
  have hē : ¬ IsNilpotent (toAlgHom A C e) := by
    intro hn
    have h0 : toAlgHom A C e = 0 := (he.map (toAlgHom A C)).eq_zero_of_isNilpotent hn
    have hu : IsUnit (1 - e) := isUnit_of_isUnit_image A C _ (by simp [h0])
    have : e = 0 := by
      have h : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      simpa using hu.mul_left_eq_zero.1 h
    obtain ⟨p, hp⟩ := hne
    simp [this] at hp
  have : (PrimeSpectrum.basicOpen (toAlgHom A C e)) ≠ ⊥ := by
    rwa [Ne, PrimeSpectrum.basicOpen_eq_bot_iff]
  obtain ⟨q, hq⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 this
  exact ⟨q, hq⟩
end Algebra.ClosedLift
