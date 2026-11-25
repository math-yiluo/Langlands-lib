/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-! # Finite presentation and ind-smooth factorizations

Source: Stacks Project, Algebra, Lemma 00QO and Lemma 07C3.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- A finitely presented algebra mapping into an ind-smooth algebra factors through a
smooth algebra. The source and base can be smaller than the target universe.

Source: Stacks Project, Algebra, Lemma 00QO and Lemma 07C3, (1) implies (2).
(blueprint: lem-weil-pbc-ind-smooth-finite-presentation-factorization).

Proof: Raise the base and source to the universe of the target using ULift.
The category of algebras over the base is equivalent to commutative rings under
that lifted base. Its forgetful functor preserves filtered colimits, since these
are connected colimits. Apply the finite-presentation factorization lemma to the
underlying ring diagram with its compatible structure maps from the lifted base.
The factorization map commutes with those structure maps and hence is an algebra
map over the original base. Compose with the inverse ULift equivalence on the source.
The chosen stage is smooth by the hypothesis defining the ind-smooth presentation.
The composite equality is the equality supplied by the factorization lemma. -/
theorem exists_smooth_factorization_of_ind_smooth
    {R : Type u} {A : Type v} {L : Type (max u v w)}
    [CommRing R] [CommRing A] [CommRing L] [Algebra R A] [Algebra R L]
    [FinitePresentation R A] (f : A →ₐ[R] L)
    (hind : CategoryTheory.ObjectProperty.ind.{max u v w}
      (fun B : CommAlgCat.{max u v w} R ↦ Smooth R B) (CommAlgCat.of R L)) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (β : A →ₐ[R] B) (δ : B →ₐ[R] L), δ.comp β = f := by
  classical
  let R' := ULift.{max v w} R
  let E : CommAlgCat.{max u v w} R ⥤ Under (CommRingCat.of R') :=
    { obj := fun B ↦ Under.mk (CommRingCat.ofHom
        ((algebraMap R B).comp ULift.ringEquiv.toRingHom))
      map := fun g ↦ Under.homMk (CommRingCat.ofHom g.hom.toRingHom)
        (by ext r; exact g.hom.commutes r.down)
      map_id := by intro B; ext x; rfl
      map_comp := by intros; ext x; rfl }
  let G : Under (CommRingCat.of R') ⥤ CommAlgCat.{max u v w} R :=
    { obj := fun B ↦ let := (B.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
                    CommAlgCat.of R B.right
      map := fun {X Y} g ↦ by
        let := (X.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        let := (Y.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.ofHom
          { toRingHom := g.right.hom
            commutes' := fun r ↦ congrArg (fun h ↦ h.hom (ULift.up r)) g.w }
      map_id := by intro B; rfl
      map_comp := by intros; rfl }
  have hE : E.IsEquivalence := by
    apply Functor.IsEquivalence.mk' G
    · exact NatIso.ofComponents (fun B ↦ by
        let := ((E.obj B).hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.isoMk
          { toRingEquiv := RingEquiv.refl B, commutes' := fun _ ↦ rfl })
        (by intros; ext x; rfl)
    · exact NatIso.ofComponents (fun B ↦ Under.isoMk (Iso.refl _)
        (by ext r; rfl)) (by intros; ext x; rfl)
  let := hE
  obtain ⟨J, hcat, hfiltered, pres, hsmooth⟩ := hind
  let := hcat
  let := hfiltered
  have : IsConnected J := IsFiltered.isConnected J
  let F := pres.diag ⋙ E ⋙ Under.forget (CommRingCat.of R')
  have hcol : IsColimit ((E ⋙ Under.forget (CommRingCat.of R')).mapCocone pres.cocone) :=
    isColimitOfPreserves (E ⋙ Under.forget (CommRingCat.of R')) pres.isColimit
  let α : (Functor.const J).obj (CommRingCat.of R') ⟶ F :=
    { app := fun j ↦ CommRingCat.ofHom
        ((algebraMap R (pres.diag.obj j)).comp ULift.ringEquiv.toRingHom)
      naturality := by intro i j g; ext r; exact ((pres.diag.map g).hom.commutes r.down).symm }
  let A' := ULift.{max u w} A
  let : Algebra R' R := ULift.algebra' R _
  let : Algebra R' A' := ULift.algebra' R _
  have : IsScalarTower R' R A' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let eR : R' ≃ₐ[R'] R :=
    { toRingEquiv := ULift.ringEquiv, commutes' := fun _ ↦ rfl }
  have : FinitePresentation R' R := FinitePresentation.equiv eR
  have : FinitePresentation R A' := FinitePresentation.equiv ULift.algEquiv.symm
  have : FinitePresentation R' A' := FinitePresentation.trans R' R A'
  let g := f.comp (ULift.algEquiv (R := R)).toAlgHom
  obtain ⟨j, g', hg'R, hg'⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of R') F α (CommRingCat.ofHom (algebraMap R' A')) _ hcol
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (CommRingCat.ofHom g.toRingHom) (by
        intro j
        ext r
        exact (g.commutes r.down).trans ((pres.ι.app j).hom.commutes r.down).symm)
  let β' : A' →ₐ[R] pres.diag.obj j :=
    { toRingHom := g'.hom
      commutes' := fun r ↦ congrArg (fun h ↦ h.hom (ULift.up r)) hg'R }
  refine ⟨pres.diag.obj j, inferInstance, inferInstance, hsmooth j,
    β'.comp ULift.algEquiv.symm.toAlgHom, (pres.ι.app j).hom, ?_⟩
  ext x
  exact (congrArg (fun h ↦ h.hom (ULift.up x)) hg').symm

end Algebra
