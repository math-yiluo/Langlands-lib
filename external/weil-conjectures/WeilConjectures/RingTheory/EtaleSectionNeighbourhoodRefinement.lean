/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting

/-! # Lifting a section at an étale algebra to a pair neighbourhood

Source: Stacks Project, More on Algebra, Tag 0A02, verification of condition (2)
of Tag 09XI (blueprint: lem-weil-pbc-etale-section-neighbourhood-refinement).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

/-- An étale algebra equipped with a section to B/J admits a refinement which is
itself an étale neighbourhood of (B,J).
Source: Stacks Project, Tag 0A02, paragraph verifying condition (2) of Tag 09XI
(blueprint: lem-weil-pbc-etale-section-neighbourhood-refinement).

Proof: Give D its B-algebra structure by composition. It is étale over B because
both B to C and C to D are étale. Put K=JD. The section kills K and is a
B-algebra map, so its quotient lift extends scalars along the surjection B to
B/J to give a B/J-algebra section of D/K. The tensor-quotient equivalence and
étale base change show that D/K is étale over B/J. Apply idempotent splitting
to obtain e with section image 1 and localization isomorphic to B/J. Lift e to
a in D, and put L=D[1/a]. The section extends to L since it sends a to 1.
Localization is étale, so L is étale over B. Its quotient by JL is the
localization of D/K at e: use the quotient-localization instance and the
identity (JD)L=JL. Thus this quotient is B/J as a B/J-algebra, proving that
the canonical quotient map is bijective. The localization map D to L and
C to L give k and j; scalar-tower identities prove their compatibility.
The localization lift equation proves r k=s, and the given B-linearity proves
r fixes B. When J is the unit ideal the quotient rings are zero rings;
localization and quotient still commute, and this proof needs no nontriviality. -/
theorem etale_section_neighbourhood_refinement (B : Type u) [CommRing B] (J : Ideal B)
    (i : ObjectProperty.FullSubcategory (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            Ideal.le_comap_map)))
    (D : Type u) [CommRing D] (g : i.obj.right →+* D)
    (hd : let : Algebra i.obj.right D := g.toAlgebra
      Algebra.Etale i.obj.right D)
    (s : D →+* B ⧸ J)
    (hs : (s.comp g).comp i.obj.hom.hom = Ideal.Quotient.mk J) :
    ∃ (N : ObjectProperty.FullSubcategory (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            Ideal.le_comap_map)))
      (j : i ⟶ N) (k : D →+* N.obj.right) (r : N.obj.right →+* B ⧸ J),
      k.comp g = j.hom.right.hom ∧
        r.comp N.obj.hom.hom = Ideal.Quotient.mk J ∧ r.comp k = s := by
  classical
  let C := i.obj.right
  let : Algebra B C := i.obj.hom.hom.toAlgebra
  let : Algebra C D := g.toAlgebra
  let : Algebra B D := (g.comp i.obj.hom.hom).toAlgebra
  have : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale B C :=
    ((AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp i.property.1).toAlgebra
  have : Algebra.Etale C D := hd
  have : Algebra.Etale B D := Algebra.Etale.comp B C D
  let K : Ideal D := J.map (algebraMap B D)
  let sB : D →ₐ[B] B ⧸ J :=
    { toRingHom := s
      commutes' := fun b ↦ DFunLike.congr_fun hs b }
  have hK : K ≤ RingHom.ker s := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change s ((g.comp i.obj.hom.hom) b) = 0
    have h := DFunLike.congr_fun hs b
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hb] using h
  let S := D ⧸ K
  let sS : S →ₐ[B ⧸ J] B ⧸ J :=
    (Ideal.Quotient.liftₐ K sB hK).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have : Algebra.Etale (B ⧸ J) S :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D J).symm
  obtain ⟨e, he, hse, _, _, ⟨ψ, hψ⟩⟩ :=
    Algebra.Etale.exists_idempotent_splitting_of_algHom sS
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  let L := Localization.Away a
  have hsa : s a = 1 := by
    change sS (Ideal.Quotient.mk K a) = 1
    rw [ha, hse]
  let r : L →+* B ⧸ J := IsLocalization.Away.lift a (hsa ▸ isUnit_one)
  have hrk : r.comp (algebraMap D L) = s := IsLocalization.Away.lift_comp _ _
  let f : B →+* L := algebraMap B L
  let M : Under (CommRingCat.of B) := Under.mk (CommRingCat.ofHom f)
  have hM : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map M.hom) := by
    apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mpr
    exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale B L)
  have hmap : K.map (algebraMap D L) = J.map f := by
    dsimp only [K]
    rw [Ideal.map_map]
    congr 1
  let Q := L ⧸ K.map (algebraMap D L)
  let : Algebra (B ⧸ J) Q := Algebra.compHom Q (algebraMap (B ⧸ J) S)
  have : IsScalarTower (B ⧸ J) S Q := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalization.Away e Q := by
    have h : IsLocalization
        (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) Q := inferInstance
    rw [Algebra.algebraMapSubmonoid_powers] at h
    change IsLocalization.Away (Ideal.Quotient.mk K a) Q at h
    rwa [ha] at h
  let : IsLocalization.Away e Q := hloc
  let eq : Q ≃ₐ[B ⧸ J] B ⧸ J :=
    ((IsLocalization.algEquiv (Submonoid.powers e) Q (Localization.Away e)).restrictScalars
      (B ⧸ J)).trans ψ
  have halg : Function.Bijective (algebraMap (B ⧸ J) Q) := by
    have hh : (eq.symm : B ⧸ J → Q) = algebraMap (B ⧸ J) Q := by
      funext b
      simpa using eq.symm.commutes b
    rw [← hh]
    exact eq.symm.bijective
  have hq : Function.Bijective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) := by
    let hle : J ≤ (K.map (algebraMap D L)).comap f := by
      rw [hmap]
      exact Ideal.le_comap_map
    have hh : Ideal.quotientMap (K.map (algebraMap D L)) f hle =
        algebraMap (B ⧸ J) Q := by
      apply RingHom.ext
      intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.quotientMap_mk]
      rfl
    have hhq : Function.Bijective
        (Ideal.quotientMap (K.map (algebraMap D L)) f hle) := by
      rw [hh]
      exact halg
    let ec := Ideal.quotEquivOfEq hmap
    have hcomp : Ideal.quotientMap (J.map f) f Ideal.le_comap_map =
        ec.toRingHom.comp (Ideal.quotientMap (K.map (algebraMap D L)) f hle) := by
      apply RingHom.ext
      intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk, ec,
        RingEquiv.toRingHom_eq_coe]
      exact (Ideal.quotEquivOfEq_mk hmap (f b)).symm
    rw [hcomp]
    exact ec.bijective.comp hhq
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        Ideal.le_comap_map)
  let N : P.FullSubcategory := ⟨M, hM, hq⟩
  let j : i ⟶ N := ObjectProperty.homMk
    (Under.homMk (CommRingCat.ofHom (algebraMap C L)) (by
      ext b
      exact (IsScalarTower.algebraMap_apply B C L b).symm))
  refine ⟨N, j, algebraMap D L, r, ?_, ?_, hrk⟩
  · exact (IsScalarTower.algebraMap_eq C D L).symm
  · change r.comp (algebraMap B L) = Ideal.Quotient.mk J
    rw [IsScalarTower.algebraMap_eq B D L, ← RingHom.comp_assoc, hrk]
    exact hs

end RingTheory
