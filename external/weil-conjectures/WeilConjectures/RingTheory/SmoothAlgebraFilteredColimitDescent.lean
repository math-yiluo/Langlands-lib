/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Smooth algebras over a filtered colimit descend to a finite stage

Source: Stacks Project, Algebra, Lemma Tag 0CAQ
(blueprint: lem-weil-pbc-smooth-algebra-filtered-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Source: Stacks Project, Algebra, Lemma Tag 0CAQ
(blueprint: lem-weil-pbc-smooth-algebra-filtered-colimit-descent).

Proof, following the node:
1. By lem-weil-pbc-smooth-algebra-finite-type-model choose a finitely generated
   subring A₀ of A and a smooth A₀-algebra B₀ whose base change is B.
2. By lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit, the inclusion
   A₀ → A factors through a stage Aᵢ: finitely many generators and relations
   lift to a common stage of the filtered category.
3. Set Bᵢ = Aᵢ ⊗[A₀] B₀. It is smooth over Aᵢ by
   lem-weil-pbc-smooth-ring-map-base-change-composition.
4. By lem-weil-pbc-tensor-cancel-base-change, the further base change of Bᵢ
   to A is A ⊗[A₀] B₀. Compose the inverse of this cancellation isomorphism
   with the model isomorphism from step 1 to obtain the asserted A-algebra isomorphism.
-/
theorem exists_smooth_algebra_of_filteredColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (B : Type u) [CommRing B]
    (f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B)
    (hf : letI := f.hom.toAlgebra; Smooth (colimit F : CommRingCat.{u}) B) :
    ∃ (i : I) (Bi : Type u) (_ : CommRing Bi)
      (g : F.obj i ⟶ CommRingCat.of Bi),
      letI := g.hom.toAlgebra
      letI := (colimit.ι F i).hom.toAlgebra
      letI := f.hom.toAlgebra
      Smooth (F.obj i) Bi ∧
        Nonempty (B ≃ₐ[(colimit F : CommRingCat.{u})]
          ((colimit F : CommRingCat.{u}) ⊗[F.obj i] Bi)) := by
  -- Work over a copy of the integers in the diagram's universe.
  let A := (colimit F : CommRingCat.{u})
  let Z := ULift.{u} ℤ
  let : Algebra Z A := ULift.algebra' ℤ _
  let (i : I) : Algebra Z (F.obj i) := ULift.algebra' ℤ _
  let := f.hom.toAlgebra
  have : Smooth A B := hf
  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Smooth.exists_subalgebra_fg Z A B
  have : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  -- Finite type over the Noetherian base gives finite presentation.
  have : FiniteType Z A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  let α : (Functor.const I).obj (CommRingCat.of Z) ⟶ F :=
    { app i := CommRingCat.ofHom (algebraMap Z (F.obj i))
      naturality := by
        intro i j k
        ext x
        rcases x with ⟨x⟩
        change (x : F.obj j) = (F.map k).hom (x : F.obj i)
        simp }
  let j : CommRingCat.of Z ⟶ CommRingCat.of A₀ :=
    CommRingCat.ofHom (algebraMap Z A₀)
  have hj : j.hom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr
      (FinitePresentation.of_finiteType.mp inferInstance)
  -- Lift the model ring, including its finitely many relations, to a stage.
  obtain ⟨i, g, _, hg⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of Z) F α j (colimit.cocone F) (colimit.isColimit F) hj
    (CommRingCat.ofHom (algebraMap A₀ A)) (by
      intro i
      ext x
      rcases x with ⟨x⟩
      change (algebraMap A₀ A) ((algebraMap Z A₀) (x : Z)) =
        (colimit.ι F i).hom (x : F.obj i)
      rw [← IsScalarTower.algebraMap_apply Z A₀ A]
      change (x : A) = (colimit.ι F i).hom (x : F.obj i)
      simp)
  let := g.hom.toAlgebra
  let := (colimit.ι F i).hom.toAlgebra
  have : IsScalarTower A₀ (F.obj i) A := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom hg
  -- Base change is smooth; cancellation identifies its further base change with B.
  let Bi := (F.obj i) ⊗[A₀] B₀
  let gi : F.obj i ⟶ CommRingCat.of Bi :=
    CommRingCat.ofHom (algebraMap (F.obj i) Bi)
  refine ⟨i, Bi, Algebra.TensorProduct.instCommRing, gi, ?_⟩
  have hgi : gi.hom.toAlgebra = (inferInstance : Algebra (F.obj i) Bi) :=
    toAlgebra_algebraMap
  rw [hgi]
  change Smooth (F.obj i) Bi ∧ Nonempty (B ≃ₐ[A] A ⊗[F.obj i] Bi)
  exact ⟨inferInstance,
    ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) A A B₀).symm⟩⟩

end Algebra
