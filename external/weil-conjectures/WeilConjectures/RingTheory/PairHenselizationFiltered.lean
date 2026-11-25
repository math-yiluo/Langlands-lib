/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.RingTheory.Etale.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Tensor products preserve the canonical quotient isomorphism. -/
private theorem quotient_tensor_bijective (R A D : Type u)
    [CommRing R] [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (I : Ideal R)
    (hA : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R A))
      (algebraMap R A) Ideal.le_comap_map))
    (hD : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R D))
      (algebraMap R D) Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap R (TensorProduct R A D)))
      (algebraMap R (TensorProduct R A D)) Ideal.le_comap_map) := by
  open scoped TensorProduct in
  let IA := I.map (algebraMap R A)
  let ID := I.map (algebraMap R D)
  let IT := I.map (algebraMap R (A ⊗[R] D))
  let qA : R ⧸ I →ₐ[R] A ⧸ IA :=
    Ideal.quotientMapₐ IA (Algebra.ofId R A) Ideal.le_comap_map
  let qD : R ⧸ I →ₐ[R] D ⧸ ID :=
    Ideal.quotientMapₐ ID (Algebra.ofId R D) Ideal.le_comap_map
  let qT : R ⧸ I →ₐ[R] (A ⊗[R] D) ⧸ IT :=
    Ideal.quotientMapₐ IT (Algebra.ofId R (A ⊗[R] D)) Ideal.le_comap_map
  let eA := AlgEquiv.ofBijective qA hA
  let eD := AlgEquiv.ofBijective qD hD
  let fA := eA.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R IA)
  let fD := eD.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R ID)
  let f : A ⊗[R] D →ₐ[R] R ⧸ I :=
    Algebra.TensorProduct.lift fA fD (fun _ _ ↦ .all _ _)
  have hf : ∀ t ∈ IT, f t = 0 := by
    change IT ≤ RingHom.ker f
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change f (algebraMap R (A ⊗[R] D) r) = 0
    rw [f.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  let fT := Ideal.Quotient.liftₐ IT f hf
  have hleft : fT.comp qT = AlgHom.id R (R ⧸ I) := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hiA : IA ≤ IT.comap
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] D) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change Algebra.TensorProduct.includeLeft (algebraMap R A r) ∈ IT
    rw [AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr
  have hiD : ID ≤ IT.comap
      (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change Algebra.TensorProduct.includeRight (algebraMap R D r) ∈ IT
    rw [AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hr
  let iA := Ideal.quotientMapₐ IT
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] D) hiA
  let iD := Ideal.quotientMapₐ IT
    (Algebra.TensorProduct.includeRight : D →ₐ[R] A ⊗[R] D) hiD
  have hqA : iA.comp qA = qT := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hqD : iD.comp qD = qT := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hright : qT.comp fT = AlgHom.id R ((A ⊗[R] D) ⧸ IT) := by
    apply Ideal.Quotient.algHom_ext
    apply Algebra.TensorProduct.ext
    · ext a
      change qT (f (a ⊗ₜ[R] 1)) = Ideal.Quotient.mk IT (a ⊗ₜ[R] 1)
      simp only [f, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rw [← hqA]
      change iA (eA (eA.symm (Ideal.Quotient.mk IA a))) = _
      rw [eA.apply_symm_apply]
      rfl
    · ext d
      change qT (f (1 ⊗ₜ[R] d)) = Ideal.Quotient.mk IT (1 ⊗ₜ[R] d)
      simp only [f, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [← hqD]
      change iD (eD (eD.symm (Ideal.Quotient.mk ID d))) = _
      rw [eD.apply_symm_apply]
      rfl
  exact ⟨Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hleft x),
    Function.RightInverse.surjective (fun x ↦ DFunLike.congr_fun hright x)⟩

/-- Cancel a canonical quotient isomorphism in a tower of algebras. -/
private theorem quotient_tower_bijective_iff (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (I : Ideal R)
    (hS : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap R S)).map (algebraMap S T))
      (algebraMap S T) Ideal.le_comap_map) ↔
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap R T))
      (algebraMap R T) Ideal.le_comap_map) := by
  have hmap : (I.map (algebraMap R S)).map (algebraMap S T) =
      I.map (algebraMap R T) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S T]
  let qR := Ideal.quotientMap (I.map (algebraMap R S))
    (algebraMap R S) Ideal.le_comap_map
  let qS := Ideal.quotientMap ((I.map (algebraMap R S)).map (algebraMap S T))
    (algebraMap S T) Ideal.le_comap_map
  let e := Ideal.quotEquivOfEq hmap
  have hcomp : e.toRingHom.comp (qS.comp qR) =
      Ideal.quotientMap (I.map (algebraMap R T)) (algebraMap R T)
        Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    change Ideal.Quotient.mk _ ((algebraMap S T) ((algebraMap R S) r)) = _
    rw [← IsScalarTower.algebraMap_apply R S T]
  rw [← hcomp]
  exact ((Function.Bijective.of_comp_iff' e.bijective qS).symm.trans
    (Function.Bijective.of_comp_iff (e ∘ qS) hS).symm)

/-- Filteredness of the category of etale algebras trivial modulo the ideal.
Source: Stacks Project, Tag 0A02, directedness paragraph.
(blueprint: lem-weil-pbc-pair-henselization-filtered).

Proof: Write R = B/J. The identity B-algebra is an object, so the category is nonempty.
For two objects C and D use C tensor_B D. Base change and composition preserve etaleness,
and its reduction is (C/JC) tensor_R (D/JD), canonically R. The two factor maps give
common successors. Every map between etale B-algebras is etale by cancellation.
For parallel maps f,g : C to D put E = D tensor_(f,C,g) D and
T = E tensor_(D tensor_B D) D, using multiplication for the last map to D.
The right factor D to E is a base change of f. The multiplication D tensor_B D to D
is etale by cancellation, so its base change E to T is etale as well. Thus T is etale
over B. Reduction of this entire diagram modulo J replaces each algebra by R and each
map by its identity, whence T/JT is R with the required structure map.
The map D to T identifies the images of d tensor 1 and 1 tensor d, since both become d
under multiplication. In E, f(c) tensor 1 equals 1 tensor g(c), so this map coequalizes
f and g. These three constructions establish all the filteredness axioms. -/
theorem pair_henselization_filtered (B : Type u) [CommRing B] (J : Ideal B) :
    IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) := by
  open scoped TensorProduct in
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        Ideal.le_comap_map)
  change IsFiltered P.FullSubcategory
  have hne : Nonempty P.FullSubcategory := by
    refine ⟨⟨Under.mk (𝟙 (CommRingCat.of B)), ?_, ?_⟩⟩
    · change AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (𝟙 _))
      rw [AlgebraicGeometry.Spec.map_id]
      infer_instance
    · change Function.Bijective
        (Ideal.quotientMap (J.map (RingHom.id B)) (RingHom.id B) Ideal.le_comap_map)
      constructor
      · apply Ideal.quotientMap_injective'
        simp
      · exact Ideal.quotientMap_surjective Function.surjective_id
  refine { nonempty := hne, cocone_objs := ?_, cocone_maps := ?_ }
  · intro C D
    let A := C.obj.right
    let E := D.obj.right
    let : Algebra B A := C.obj.hom.hom.toAlgebra
    let : Algebra B E := D.obj.hom.hom.toAlgebra
    have hA : Algebra.Etale B A :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp C.property.1
    have hE : Algebra.Etale B E :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp D.property.1
    let T := A ⊗[B] E
    let t : Under (CommRingCat.of B) :=
      Under.mk (CommRingCat.ofHom (algebraMap B T))
    have ht : P t := by
      constructor
      · apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.Etale)).mpr
        exact (RingHom.etale_algebraMap (R := B) (S := T)).mpr
          (inferInstance : Algebra.Etale B T)
      · exact quotient_tensor_bijective B A E J C.property.2 D.property.2
    let Z : P.FullSubcategory := ⟨t, ht⟩
    refine ⟨Z, ObjectProperty.homMk (Under.homMk
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[B] T).toRingHom) ?_),
      ObjectProperty.homMk (Under.homMk
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : E →ₐ[B] T).toRingHom) ?_), trivial⟩
    · apply CommRingCat.hom_ext
      exact (Algebra.TensorProduct.includeLeft : A →ₐ[B] T).comp_algebraMap
    · apply CommRingCat.hom_ext
      exact (Algebra.TensorProduct.includeRight : E →ₐ[B] T).comp_algebraMap
  · intro C D f g
    let A := C.obj.right
    let E := D.obj.right
    let : Algebra B A := C.obj.hom.hom.toAlgebra
    let : Algebra B E := D.obj.hom.hom.toAlgebra
    let f' : A →ₐ[B] E :=
      { f.hom.right.hom with
        commutes' := fun b ↦ congrArg (fun h ↦ h.hom b) (Under.w f.hom) }
    let g' : A →ₐ[B] E :=
      { g.hom.right.hom with
        commutes' := fun b ↦ congrArg (fun h ↦ h.hom b) (Under.w g.hom) }
    have hA : Algebra.Etale B A :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp C.property.1
    have hE : Algebra.Etale B E :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp D.property.1
    -- Pull back the diagonal along the pair of maps f and g.
    let S := A ⊗[B] A
    let m : S →ₐ[B] A := Algebra.TensorProduct.lmul' B
    let k : S →ₐ[B] E := Algebra.TensorProduct.lift f' g' (fun _ _ ↦ .all _ _)
    let : Algebra S A := m.toRingHom.toAlgebra
    let : Algebra S E := k.toRingHom.toAlgebra
    have hm : Algebra.Etale S A := by
      have hs : AlgebraicGeometry.Etale
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B S))) :=
        (AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.Etale)).mpr
          ((RingHom.etale_algebraMap (R := B) (S := S)).mpr inferInstance)
      have hc : AlgebraicGeometry.Spec.map (CommRingCat.ofHom m.toRingHom) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B S)) =
          AlgebraicGeometry.Spec.map C.obj.hom := by
        rw [← AlgebraicGeometry.Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact m.comp_algebraMap
      have hcomp : AlgebraicGeometry.Etale
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom m.toRingHom) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B S))) :=
        hc.symm ▸ C.property.1
      exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.Etale)).mp
        (AlgebraicGeometry.Etale.of_comp
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom m.toRingHom))
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B S))))
    let T := E ⊗[S] A
    have hT : Algebra.Etale B T := Algebra.Etale.comp B E T
    let t : Under (CommRingCat.of B) :=
      Under.mk (CommRingCat.ofHom (algebraMap B T))
    have ht : P t := by
      constructor
      · apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.Etale)).mpr
        exact (RingHom.etale_algebraMap (R := B) (S := T)).mpr hT
      · have hS := quotient_tensor_bijective B A A J C.property.2 C.property.2
        have hSE := (quotient_tower_bijective_iff B S E J hS).mpr D.property.2
        have hSA := (quotient_tower_bijective_iff B S A J hS).mpr C.property.2
        have hST := quotient_tensor_bijective S E A (J.map (algebraMap B S)) hSE hSA
        exact (quotient_tower_bijective_iff B S T J hS).mp hST
    let Z : P.FullSubcategory := ⟨t, ht⟩
    let h : D ⟶ Z := ObjectProperty.homMk (Under.homMk
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : E →ₐ[B] T).toRingHom)
      (by
        apply CommRingCat.hom_ext
        exact (Algebra.TensorProduct.includeLeft : E →ₐ[B] T).comp_algebraMap))
    refine ⟨Z, h, ?_⟩
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext a
    change (f' a) ⊗ₜ[S] (1 : A) = (g' a) ⊗ₜ[S] (1 : A)
    have hf := Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := S) (A := E) (B := A) (a ⊗ₜ[B] (1 : A))
    have hg := Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := S) (A := E) (B := A) ((1 : A) ⊗ₜ[B] a)
    change (k (a ⊗ₜ[B] 1)) ⊗ₜ[S] 1 = 1 ⊗ₜ[S] (m (a ⊗ₜ[B] 1)) at hf
    change (k (1 ⊗ₜ[B] a)) ⊗ₜ[S] 1 = 1 ⊗ₜ[S] (m (1 ⊗ₜ[B] a)) at hg
    change (f' a * g' 1) ⊗ₜ[S] 1 = 1 ⊗ₜ[S] (a * 1) at hf
    change (f' 1 * g' a) ⊗ₜ[S] 1 = 1 ⊗ₜ[S] (1 * a) at hg
    simp only [map_one, mul_one, one_mul] at hf hg
    exact hf.trans hg.symm

end RingTheory
