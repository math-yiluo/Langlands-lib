/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.EtaleStrictlyHenselianSplitting

/-!
# Idempotents of the ind-étale closed lift

Let `H = H_A(C̄)` be the ind-étale closed lift of `Algebra.ClosedLift`.

- An idempotent of `H` vanishing in `C̄` vanishes
  (`Algebra.ClosedLift.eq_zero_of_isIdempotentElem`).
- For `C̄` ind-étale over `A ⧸ I`, every idempotent of `C̄` lifts to an idempotent of `H`
  (`Algebra.ClosedLift.exists_isIdempotentElem_toAlgHom_eq`).
- If `A` is a strictly henselian local ring and `C̄` is killed by the maximal ideal, then `H` is
  spanned over `A` by its idempotents (`Algebra.ClosedLift.mem_span_isIdempotentElem`): every
  étale `A`-algebra `B` is `Aⁿ × B''` with `B'' = m B''`, and `B''` dies in `C̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- An idempotent of `H_A(C̄)` with vanishing image in `C̄` vanishes: `1 - e` is a unit by
`Algebra.ClosedLift.isUnit_of_isUnit_image`. -/
theorem eq_zero_of_isIdempotentElem {e : ClosedLift A C} (he : IsIdempotentElem e)
    (h0 : toAlgHom A C e = 0) : e = 0 := by
  have hu : IsUnit (1 - e) := isUnit_of_isUnit_image A C _ (by simp [h0])
  have h : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  simpa using hu.mul_left_eq_zero.1 h

/-- The `A`-algebra map `A × A → C` sending `(1, 0)` to an idempotent `c`. -/
noncomputable def prodAlgHomOfIsIdempotentElem {c : C} (hc : IsIdempotentElem c) :
    A × A →ₐ[A] C where
  toFun x := algebraMap A C x.1 * c + algebraMap A C x.2 * (1 - c)
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have h1 : c * c = c := hc.eq
    linear_combination (algebraMap A C x.1 * algebraMap A C y.2 +
      algebraMap A C x.2 * algebraMap A C y.1 - algebraMap A C x.1 * algebraMap A C y.1 -
      algebraMap A C x.2 * algebraMap A C y.2) * h1
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  commutes' a := by
    simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring

/-- Every idempotent of an ind-étale `A ⧸ I`-algebra `C̄` lifts to an idempotent of `H_A(C̄)`:
lift the map `A × A → C̄` given by the idempotent along the universal property
`Algebra.ClosedLift.homEquiv`. -/
theorem exists_isIdempotentElem_toAlgHom_eq (I : Ideal A) [Algebra (A ⧸ I) C]
    [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale (A ⧸ I) C] {c : C} (hc : IsIdempotentElem c) :
    ∃ e : ClosedLift A C, IsIdempotentElem e ∧ toAlgHom A C e = c := by
  let φ := (homEquiv I (A × A)).symm (prodAlgHomOfIsIdempotentElem hc)
  have hφ : (toAlgHom A C).comp φ = prodAlgHomOfIsIdempotentElem hc :=
    (homEquiv I (A × A)).apply_symm_apply _
  have hidem : IsIdempotentElem ((1, 0) : A × A) := by
    simp [IsIdempotentElem]
  refine ⟨φ (1, 0), hidem.map φ, ?_⟩
  rw [← AlgHom.comp_apply, hφ]
  simp [prodAlgHomOfIsIdempotentElem]

/-- If `A` is a strictly henselian local ring and the maximal ideal of `A` acts by zero on `C̄`,
then `H_A(C̄)` is spanned over `A` by its idempotents. An element of `H_A(C̄)` comes from an étale
`A`-algebra `B`, which splits as `Aⁿ × B''` with `B''` spanned by an idempotent `f ∈ m B`
(`Algebra.Etale.exists_isIdempotentElem_mem_map_maximalIdeal`); the image of `f` in `H_A(C̄)` is
an idempotent vanishing in `C̄`, hence zero. -/
theorem mem_span_isIdempotentElem [IsStrictlyHenselianLocalRing A]
    (hC : ∀ a ∈ maximalIdeal A, algebraMap A C a = 0) (x : ClosedLift A C) :
    x ∈ Submodule.span A {e : ClosedLift A C | IsIdempotentElem e} := by
  obtain ⟨X, (b : X.alg), rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat A)) (colimit.isColimit (diagram A C))) x
  let ι : X.alg →ₐ[A] ClosedLift A C := (colimit.ι (diagram A C) X).hom
  change ι b ∈ _
  obtain ⟨f, hf, hfm, hspan⟩ := Algebra.Etale.exists_isIdempotentElem_mem_map_maximalIdeal
    (A := A) X.alg
  have hf0 : ι f = 0 := by
    refine eq_zero_of_isIdempotentElem (hf.map ι) ?_
    refine (toAlgHom_ι A C X f).trans ?_
    have hle : (maximalIdeal A).map (algebraMap A X.alg) ≤ RingHom.ker X.toC.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp [hC a ha]
    exact hle hfm
  have hb : ι b = ι (b * (1 - f)) := by
    rw [map_mul, map_sub, hf0, map_one, sub_zero, mul_one]
  rw [hb]
  have h := Submodule.mem_map_of_mem (f := ι.toLinearMap) (hspan b)
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨e, he, rfl⟩
  exact he.map ι

end Algebra.ClosedLift
