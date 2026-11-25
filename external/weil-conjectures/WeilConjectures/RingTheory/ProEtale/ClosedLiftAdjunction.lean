/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-! # The closed-lift adjunction on ind-etale algebras

Source: Stacks Project, Tag 097P, proof of `lemma-lift-ind-etale`, final two paragraphs;
blueprint, smooth purity, `proposition-extension-zero-restriction-closed-subscheme`
(blueprint: proposition-extension-zero-restriction-closed-subscheme).

The adjunction is expressed by its natural family of Hom equivalences. Naturality is
written on quotient representatives; the quotient maps are surjective, so these are
exactly the two naturality identities on Hom sets. No category or reduction functor is
redefined. The explicit quotient algebra structure is Mathlib's canonical one.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Algebra.ClosedLift

-- A finite-presentation source factors through a stage; compatibility is an indexing morphism.
private theorem index_hom_unique {A C : Type u} [CommRing A] [CommRing C]
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
private theorem etale_lift_unique {A C D : Type u} [CommRing A] [CommRing C]
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
    have h := index_hom_unique X (f.comp e.toAlgHom) (by
      rw [← AlgHom.comp_assoc, hf])
    ext d
    have hd := DFunLike.congr_fun h (e.symm d)
    change f (e (e.symm d)) = _ at hd
    change f d = (Limits.colimit.ι (diagram A C) X).hom (e.symm d)
    exact (congrArg f (e.apply_symm_apply d)).symm.trans hd

-- Lift each etale stage uniquely, and use uniqueness to make the lifts a cocone.
private theorem indEtale_lift_unique {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra A D] [Algebra.IndEtale A D]
    (q : D →ₐ[A] C) : ∃! f : D →ₐ[A] ClosedLift A C, (toAlgHom A C).comp f = q := by
  classical
  obtain ⟨J, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := D)
  have (j : J) : Algebra.Etale A (P.diag.obj j) := hP j
  have h (j : J) := etale_lift_unique (q.comp (P.ι.app j).hom)
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

private noncomputable def quotientHomEquiv (A : Type u) [CommRing A] (I : Ideal A)
    (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C] :
    (D →ₐ[A] C) ≃ @AlgHom (A ⧸ I) (D ⧸ I.map (algebraMap A D)) C _ _ _
      (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) _ := by
  let : Algebra (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let q (f : D →ₐ[A] C) : D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C :=
    { __ := Ideal.Quotient.lift _ f.toRingHom (by
        change I.map (algebraMap A D) ≤ RingHom.ker f.toRingHom
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change f (algebraMap A D a) = 0
        rw [f.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) C,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (f.commutes a).trans (IsScalarTower.algebraMap_apply A (A ⧸ I) C a) }
  let p (g : D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] C) : D →ₐ[A] C :=
    { __ := g.toRingHom.comp (Ideal.Quotient.mk _)
      commutes' := by
        intro a
        exact (g.commutes (Ideal.Quotient.mk I a)).trans
          (IsScalarTower.algebraMap_apply A (A ⧸ I) C a).symm }
  exact
    { toFun := q
      invFun := p
      left_inv f := by ext d; rfl
      right_inv g := by
        ext d
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        rfl }

private noncomputable def closedHomEquiv (A : Type u) [CommRing A] (I : Ideal A)
    (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale A D] :
    (D →ₐ[A] ClosedLift A C) ≃
      @AlgHom (A ⧸ I) (D ⧸ I.map (algebraMap A D)) C _ _ _
        (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) _ :=
  (Equiv.ofBijective (fun f : D →ₐ[A] ClosedLift A C ↦ (toAlgHom A C).comp f)
    ((Function.bijective_iff_existsUnique _).mpr indEtale_lift_unique)).trans
      (quotientHomEquiv A I D C)

private theorem closedHomEquiv_apply (A : Type u) [CommRing A] (I : Ideal A)
    (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale A D] (f : D →ₐ[A] ClosedLift A C) (d : D) :
    closedHomEquiv A I D C f (Ideal.Quotient.mk _ d) = toAlgHom A C (f d) := rfl

/-- The map to the input algebra is natural in the input algebra. -/
theorem toAlgHom_map {A C C' : Type u} [CommRing A] [CommRing C] [CommRing C']
    [Algebra A C] [Algebra A C'] (φ : C →ₐ[A] C') :
    (toAlgHom A C').comp (map φ) = φ.comp (toAlgHom A C) := by
  suffices hh : CommAlgCat.ofHom ((toAlgHom A C').comp (map φ)) =
      CommAlgCat.ofHom (φ.comp (toAlgHom A C)) from congrArg CommAlgCat.Hom.hom hh
  apply Limits.colimit.hom_ext
  intro X
  apply CommAlgCat.hom_ext
  change ((toAlgHom A C').comp (map φ)).comp (Limits.colimit.ι (diagram A C) X).hom =
    (φ.comp (toAlgHom A C)).comp (Limits.colimit.ι (diagram A C) X).hom
  rw [AlgHom.comp_assoc, ι_map, ι_toAlgHom, AlgHom.comp_assoc, ι_toAlgHom]
  rfl

private theorem quotient_indEtale (A : Type u) [CommRing A] (I : Ideal A)
    (D : CommAlgCat.{u} A) [Algebra.IndEtale A D] :
    @Algebra.IndEtale (A ⧸ I) (D ⧸ I.map (algebraMap A D)) _ _
      (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) := by
  let : Algebra (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower A (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsPushout A (A ⧸ I) D (D ⧸ I.map (algebraMap A D)) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (CommRingCat.isPushout_quotient (CommRingCat.ofHom (algebraMap A D)) I)
  have : Algebra.IsPushout A D (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    (inferInstance : Algebra.IsPushout A (A ⧸ I) D _).symm
  exact (RingHom.IndEtale.algebraMap_iff _ _).mp
    (RingHom.IndEtale.isStableUnderBaseChange A D (A ⧸ I)
      (D ⧸ I.map (algebraMap A D))
      ((RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance))

/-- Reduction is left adjoint to the closed lift, expressed as a natural Hom equivalence.
Source: Stacks Project, Tag 097P, final two proof paragraphs
(blueprint: proposition-extension-zero-restriction-closed-subscheme).

The first identity specifies the map on every quotient class. The second is naturality
under precomposition in `D`, and the third is naturality under postcomposition in `C`.
The final two identities say that the specified closed-lift maps preserve identities and
composition. Together with ind-etaleness of the reduction and the existing ind-etaleness
instance for `ClosedLift`, this is the Hom-set definition of the claimed adjunction.

Proof plan:
1. The indexing category is small and filtered
(proposition-extension-zero-restriction-closed-subscheme), with etale finite-presentation terms, so
its colimit is ind-etale. Reduction is quotient base change, so lemma-stability makes it ind-etale.
The composite of any map to the lift with `toAlgHom` kills the extended ideal, hence descends to the
quotient.
2. For etale finite-presentation `D`, choose a finite presentation
(def-weil-pbc-finitely-presented-algebra). A map from its reduction supplies an indexing
object and hence a coprojection to the lift. Compatible presentation isomorphisms in the
indexing category show independence of this choice.
3. For uniqueness, use lem-weil-pbc-filtered-colimit-algebras-elementwise to view the
algebra colimit as a ring colimit. Then
lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit factors a map from `D`
through a stage. Its compatibility with the retained map makes this an indexing morphism;
the cocone relation identifies the map with the coprojection from step 2.
4. Present general ind-etale `D` as a small filtered colimit of etale algebras. The unique
finite-stage lifts commute with transitions by step 3. The universal property
(def-weil-pbc-category-colimit) gives a unique lift from `D`, proving bijectivity.
5. The formula on representatives gives contravariant naturality. For covariance,
`ι_map` gives compatibility of the retained maps on every coprojection; the colimit
universal property gives compatibility globally. The same argument proves identity and
composition for `map`.
6. The inverse Hom equivalences define reduction left adjoint to the closed lift.
The image of the identity is the specified reduction map, so this is the counit;
proposition-extension-zero-restriction-closed-subscheme identifies it as an isomorphism. -/
theorem exists_natural_homEquiv (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ β : ∀ (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale A D]
      [Algebra.IndEtale (A ⧸ I) C],
      (D →ₐ[A] ClosedLift A C) ≃
        @AlgHom (A ⧸ I) (D ⧸ I.map (algebraMap A D)) C _ _ _
          (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) _,
    ∀ (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale A D]
      [Algebra.IndEtale (A ⧸ I) C],
      @Algebra.IndEtale (A ⧸ I) (D ⧸ I.map (algebraMap A D)) _ _
        (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) ∧
      (∀ (f : D →ₐ[A] ClosedLift A C) (d : D),
        β D C f (Ideal.Quotient.mk _ d) = toAlgHom A C (f d)) ∧
      (∀ (D' : CommAlgCat.{u} A) [Algebra.IndEtale A D']
        (r : D' →ₐ[A] D) (f : D →ₐ[A] ClosedLift A C) (d : D'),
        β D' C (f.comp r) (Ideal.Quotient.mk _ d) =
          β D C f (Ideal.Quotient.mk _ (r d))) ∧
      (∀ (C' : CommAlgCat.{u} A) [Algebra (A ⧸ I) C']
        [IsScalarTower A (A ⧸ I) C'] [Algebra.IndEtale (A ⧸ I) C']
        (φ : C →ₐ[A ⧸ I] C') (f : D →ₐ[A] ClosedLift A C) (d : D),
        β D C' ((map (φ.restrictScalars A)).comp f) (Ideal.Quotient.mk _ d) =
          φ (β D C f (Ideal.Quotient.mk _ d))) ∧
      map (AlgHom.id A C) = AlgHom.id A (ClosedLift A C) ∧
      (∀ (C' C'' : CommAlgCat.{u} A) [Algebra (A ⧸ I) C']
        [Algebra (A ⧸ I) C''] [IsScalarTower A (A ⧸ I) C']
        [IsScalarTower A (A ⧸ I) C''] [Algebra.IndEtale (A ⧸ I) C']
        [Algebra.IndEtale (A ⧸ I) C'']
        (φ : C →ₐ[A ⧸ I] C') (ψ : C' →ₐ[A ⧸ I] C''),
        map ((ψ.comp φ).restrictScalars A) =
          (map (ψ.restrictScalars A)).comp (map (φ.restrictScalars A))) := by
  refine ⟨fun D C _ _ _ _ ↦ closedHomEquiv A I D C, ?_⟩
  intro D C _ _ _ _
  refine ⟨quotient_indEtale A I D, closedHomEquiv_apply A I D C, ?_, ?_,
    ClosedLift.map_id, ?_⟩
  · intro D' _ r f d
    rw [closedHomEquiv_apply, closedHomEquiv_apply]
    rfl
  · intro C' _ _ _ φ f d
    rw [closedHomEquiv_apply, closedHomEquiv_apply]
    exact DFunLike.congr_fun (toAlgHom_map (φ.restrictScalars A)) (f d)
  · intro C' C'' _ _ _ _ _ _ φ ψ
    exact ClosedLift.map_comp (φ.restrictScalars A) (ψ.restrictScalars A)

end Algebra.ClosedLift
