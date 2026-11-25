/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftRetraction
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-!
# The universal property of `H_A(C)` for weakly étale algebras

For an `A`-algebra `C`, let `H = H_A(C)` be the colimit of the étale `A`-algebras with an
`A`-algebra map to `C` (`Algebra.ClosedLift`), with its map `H ⟶ C`.

- `Algebra.ClosedLift.existsUnique_comp_toAlgHom_eq_of_indEtale`: every `A`-algebra map
  `D ⟶ C` from an ind-étale `A`-algebra `D` factors uniquely through `H ⟶ C`.
- `Algebra.ClosedLift.exists_comp_toAlgHom_eq_of_weaklyEtale`: if every faithfully flat
  ind-étale `C`-algebra has a retraction (e.g. `C` is w-contractible), every `A`-algebra map
  `D ⟶ C` from a weakly étale `A`-algebra `D` factors through `H ⟶ C`. Indeed `D` has a
  faithfully flat ind-étale cover `T` which is ind-étale over `A` (Stacks 097Z), and
  `D ⟶ C` extends to `T` by splitting the faithfully flat ind-étale `C`-algebra `C ⊗_D T`.

(Uniqueness for weakly étale `D` also holds; it is proved geometrically in
`WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.Hull`.)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Algebra.ClosedLift

-- A finite-presentation source factors through a stage; compatibility is an indexing morphism.
private theorem index_hom_unique' {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (X : Index A C) (f : X.alg →ₐ[A] ClosedLift A C)
    (hf : (toAlgHom A C).comp f = X.toC) :
    f = (Limits.colimit.ι (diagram A C) X).hom := by
  have : IsFinitelyPresentable.{u} (CommAlgCat.of A X.alg) :=
    CommAlgCat.finitePresentation_le_isFinitelyPresentable A _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨Y, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (Limits.colimit.isColimit (diagram A C)) (CommAlgCat.ofHom f)
  have hgf : (Limits.colimit.ι (diagram A C) Y).hom.comp g.hom = f :=
    congrArg CommAlgCat.Hom.hom hg
  let r : X ⟶ Y := ⟨g.hom, by rw [← ι_toAlgHom Y, AlgHom.comp_assoc, hgf, hf]⟩
  have hw := Limits.colimit.w (diagram A C) r
  exact hgf.symm.trans (congrArg CommAlgCat.Hom.hom hw)

set_option backward.isDefEq.respectTransparency false in
private theorem etale_lift_unique' {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra A D] [Algebra.Etale A D]
    (q : D →ₐ[A] C) : ∃! f : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp f = q := by
  obtain ⟨n, J, e, _⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation A D)
  have he : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ J) :=
    Algebra.Etale.of_equiv e.symm
  let X : Index A C := ⟨n, J, he, q.comp e.toAlgHom⟩
  refine ⟨(Limits.colimit.ι (diagram A C) X).hom.comp e.symm.toAlgHom, ?_, ?_⟩
  · change (toAlgHom A C).comp
      ((Limits.colimit.ι (diagram A C) X).hom.comp e.symm.toAlgHom) = q
    rw [← AlgHom.comp_assoc, ι_toAlgHom]
    ext d
    exact congrArg q (e.apply_symm_apply d)
  · intro f hf
    have h := index_hom_unique' X (f.comp e.toAlgHom) (by
      rw [← AlgHom.comp_assoc, hf])
    ext d
    have hd := DFunLike.congr_fun h (e.symm d)
    change f (e (e.symm d)) = _ at hd
    change f d = (Limits.colimit.ι (diagram A C) X).hom (e.symm d)
    exact (congrArg f (e.apply_symm_apply d)).symm.trans hd

/-- **Universal property of `H_A(C)`**: every `A`-algebra map `D ⟶ C` from an ind-étale
`A`-algebra `D` factors uniquely through `H_A(C) ⟶ C`. Lift each étale stage of a colimit
presentation of `D` uniquely, and use uniqueness to make the lifts a cocone. -/
theorem existsUnique_comp_toAlgHom_eq_of_indEtale {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra A D] [Algebra.IndEtale A D]
    (q : D →ₐ[A] C) : ∃! f : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp f = q := by
  classical
  obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D)
  have (j : J) : Algebra.Etale A (P.diag.obj j) := hP j
  have h (j : J) := etale_lift_unique' (q.comp (P.ι.app j).hom)
  let l (j : J) := (h j).choose
  have hl (j : J) : (toAlgHom A C).comp (l j) = q.comp (P.ι.app j).hom :=
    (h j).choose_spec.1
  have hu (j : J) (f : P.diag.obj j →ₐ[A] ClosedLift A C)
      (hf : (toAlgHom A C).comp f = q.comp (P.ι.app j).hom) : f = l j :=
    (h j).choose_spec.2 f hf
  let c : Limits.Cocone P.diag :=
    { pt := CommAlgCat.of A (ClosedLift A C)
      ι :=
        { app j := CommAlgCat.ofHom (l j)
          naturality {i j} r := by
            apply CommAlgCat.hom_ext
            change (l j).comp (P.diag.map r).hom = (l i).comp (AlgHom.id A _)
            rw [AlgHom.comp_id]
            apply hu
            rw [← AlgHom.comp_assoc, hl, AlgHom.comp_assoc]
            exact congrArg (q.comp ·) (congrArg CommAlgCat.Hom.hom (P.cocone.w r)) } }
  let f : D →ₐ[A] ClosedLift A C := (P.isColimit.desc c).hom
  have hf (j : J) : f.comp (P.ι.app j).hom = l j :=
    congrArg CommAlgCat.Hom.hom (P.isColimit.fac c j)
  have he : (toAlgHom A C).comp f = q := by
    suffices hh : CommAlgCat.ofHom ((toAlgHom A C).comp f) = CommAlgCat.ofHom q from
      congrArg CommAlgCat.Hom.hom hh
    apply P.isColimit.hom_ext
    intro j
    apply CommAlgCat.hom_ext
    change ((toAlgHom A C).comp f).comp (P.ι.app j).hom = q.comp (P.ι.app j).hom
    rw [AlgHom.comp_assoc, hf, hl]
  refine ⟨f, he, ?_⟩
  intro g hg
  suffices hh : CommAlgCat.ofHom g = CommAlgCat.ofHom f from
    congrArg CommAlgCat.Hom.hom hh
  apply P.isColimit.hom_ext
  intro j
  apply CommAlgCat.hom_ext
  change g.comp (P.ι.app j).hom = f.comp (P.ι.app j).hom
  rw [hf]
  apply hu
  rw [← AlgHom.comp_assoc, hg]

/-- An `A`-algebra endomorphism of `H_A(C)` over `C` is the identity. -/
theorem eq_id_of_toAlgHom_comp_eq {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (f : ClosedLift A C →ₐ[A] ClosedLift A C) (hf : (toAlgHom A C).comp f = toAlgHom A C) :
    f = AlgHom.id A _ :=
  (existsUnique_comp_toAlgHom_eq_of_indEtale (toAlgHom A C)).unique hf (AlgHom.comp_id _)

/-- **Lifting weakly étale algebras to `H_A(C)`.** If every faithfully flat ind-étale
`C`-algebra has a retraction (e.g. `C` is w-contractible), every `A`-algebra map `D ⟶ C` from a
weakly étale `A`-algebra `D` factors through `H_A(C) ⟶ C`.

Choose a faithfully flat ind-étale `D`-algebra `T` which is ind-étale over `A` (Stacks 097Z).
The `C`-algebra `C ⊗_D T` is faithfully flat and ind-étale, so it has a retraction, which
extends `D ⟶ C` to `T ⟶ C`; this factors through `H_A(C)` since `T` is ind-étale over `A`. -/
theorem exists_comp_toAlgHom_eq_of_weaklyEtale {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    {D : Type u} [CommRing D] [Algebra A D] [Algebra.WeaklyEtale A D] (q : D →ₐ[A] C) :
    ∃ f : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp f = q := by
  obtain ⟨T, _, _, _, _, hDT, hff, hAT⟩ := Algebra.WeaklyEtale.exists_indEtale A D
  let : Algebra D C := q.toRingHom.toAlgebra
  have : Algebra.IndEtale C (C ⊗[D] T) := indEtale_tensorProduct D C T
  obtain ⟨r, hr⟩ := hC (C ⊗[D] T)
  have key (d : D) : r ((1 : C) ⊗ₜ[D] algebraMap D T d) = q d := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    exact RingHom.congr_fun hr (q d)
  let q' : T →ₐ[A] C :=
    { toRingHom := r.comp (Algebra.TensorProduct.includeRight : T →ₐ[D] C ⊗[D] T)
      commutes' := fun a ↦ by
        change r ((1 : C) ⊗ₜ[D] algebraMap A T a) = _
        rw [IsScalarTower.algebraMap_apply A D T, key, AlgHom.commutes] }
  obtain ⟨f', hf', -⟩ := existsUnique_comp_toAlgHom_eq_of_indEtale q'
  refine ⟨f'.comp (IsScalarTower.toAlgHom A D T), AlgHom.ext fun d ↦ ?_⟩
  rw [← AlgHom.comp_assoc, hf']
  exact key d

end Algebra.ClosedLift
