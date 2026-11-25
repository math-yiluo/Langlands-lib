/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.FilteredColimitSmoothProduct
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Fin.Tuple.Basic

/-! # Ind-smoothness under finite product decompositions
Source: Stacks Project, Smoothing Ring Maps, Tag 07F3 and the proof of Tag 07F5.
-/

@[expose] public section

open CategoryTheory
universe u v

private def restrictBase {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    CommAlgCat.{max u v} S ⥤ CommAlgCat.{max u v} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom A f
    CommAlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom A f
    letI : Algebra R B := Algebra.compHom B f
    CommAlgCat.ofHom
      { __ := g.hom.toRingHom
        commutes' := fun r ↦ g.hom.commutes (f r) }

set_option backward.isDefEq.respectTransparency false in
private def restrictBaseEquivalence {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) : CommAlgCat.{max u v} S ≌ CommAlgCat.{max u v} R where
  functor := restrictBase e.toRingHom
  inverse := restrictBase e.symm.toRingHom
  unitIso := NatIso.ofComponents (fun A ↦ CommAlgCat.isoMk
    (@AlgEquiv.ofRingEquiv (f := RingEquiv.refl A) _ _ _ _ _ _
      A.algebra
      ((restrictBase e.symm.toRingHom).obj ((restrictBase e.toRingHom).obj A)).algebra
      (fun s ↦ by
        change algebraMap S A s = algebraMap S A (e (e.symm s))
        rw [e.apply_symm_apply]))) (by intros; ext; rfl)
  counitIso := NatIso.ofComponents (fun A ↦ CommAlgCat.isoMk
    (@AlgEquiv.ofRingEquiv (f := RingEquiv.refl A) _ _ _ _ _ _
      ((restrictBase e.toRingHom).obj ((restrictBase e.symm.toRingHom).obj A)).algebra
      A.algebra
      (fun r ↦ by
        change algebraMap R A (e.symm (e r)) = algebraMap R A r
        rw [e.symm_apply_apply]))) (by intros; ext; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem ind_smooth_transport
    {R S : Type u} {A B : Type (max u v)}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (hcompat : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (hB : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} S ↦ Algebra.Smooth S C) (CommAlgCat.of S B)) :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} R ↦ Algebra.Smooth R C) (CommAlgCat.of R A) := by
  let E := restrictBaseEquivalence.{u, v} e
  obtain ⟨J, _, _, pres, hp⟩ := hB
  let fA : CommAlgCat.of R A ≅ E.functor.obj (CommAlgCat.of S B) :=
    CommAlgCat.isoMk
      (@AlgEquiv.ofRingEquiv (f := f) _ _ _ _ _ _ inferInstance
        (E.functor.obj (CommAlgCat.of S B)).algebra hcompat)
  refine ⟨J, inferInstance, inferInstance, (pres.map E.functor).ofIso fA.symm, ?_⟩
  intro j
  apply RingHom.smooth_algebraMap.mp
  change ((algebraMap S (pres.diag.obj j)).comp e.toRingHom).Smooth
  exact (RingHom.Smooth.of_bijective e.bijective).comp
    (RingHom.smooth_algebraMap.mpr (hp j))

private def piSuccRingEquiv {n : ℕ} (K : Fin (n + 1) → Type*)
    [∀ i, CommRing (K i)] : (∀ i, K i) ≃+* K 0 × (∀ i : Fin n, K i.succ) where
  __ := (Fin.consEquiv K).symm
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem ind_smooth_pi (n : ℕ) :
    ∀ (K : Fin n → Type u) (B : Fin n → Type (max u v))
      [∀ i, CommRing (K i)] [∀ i, CommRing (B i)] [∀ i, Algebra (K i) (B i)],
      (∀ i, ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (K i) ↦ Algebra.Smooth (K i) C)
        (CommAlgCat.of (K i) (B i))) →
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (∀ i, K i) ↦ Algebra.Smooth (∀ i, K i) C)
        (CommAlgCat.of (∀ i, K i) (∀ i, B i)) := by
  induction n with
  | zero =>
    intro K B _ _ _ _
    apply ObjectProperty.le_ind
    apply RingHom.smooth_algebraMap.mp
    apply RingHom.Smooth.of_bijective
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n ih =>
    intro K B _ _ _ hB
    have ht := ih (fun i ↦ K i.succ) (fun i ↦ B i.succ) (fun i ↦ hB i.succ)
    have hp := Algebra.ind_smooth_prod (K 0) (∀ i : Fin n, K i.succ)
      (B 0) (∀ i : Fin n, B i.succ) (hB 0) ht
    let : Algebra (K 0 × (∀ i : Fin n, K i.succ))
        (B 0 × (∀ i : Fin n, B i.succ)) :=
      (RingHom.prodMap (algebraMap (K 0) (B 0))
        (algebraMap (∀ i : Fin n, K i.succ) (∀ i : Fin n, B i.succ))).toAlgebra
    exact ind_smooth_transport (piSuccRingEquiv K) (piSuccRingEquiv B)
      (fun _ ↦ rfl) hp

/-- Compatible finite product decompositions of the base and target glue ind-smoothness.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F3, iterated as in the proof of
Lemma Tag 07F5 (third paragraph).
(blueprint: lem-weil-pbc-ind-smooth-finite-product-transport).

Proof: For zero factors both products are zero rings and their structure map is an
isomorphism, hence smooth and ind-smooth. For a successor number of factors, separate
factor zero from the remaining factors, apply induction to the latter, and apply
Algebra.ind_smooth_prod to this binary product. The canonical splitting maps commute
with the componentwise structure maps. Restriction of scalars along a base ring
isomorphism is an equivalence of categories of commutative algebras; it preserves
colimits and takes smooth algebras to smooth algebras, since isomorphisms and composites
of smooth ring maps are smooth. Apply this to the splitting isomorphisms and then to
the given compatible base and target isomorphisms. All diagrams retain their universe. -/
theorem Algebra.ind_smooth_of_finite_product
    (R : Type u) (A : Type (max u v)) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (K : Fin n → Type u) (B : Fin n → Type (max u v))
    [∀ i, CommRing (K i)] [∀ i, CommRing (B i)] [∀ i, Algebra (K i) (B i)]
    (e : R ≃+* ∀ i, K i) (f : A ≃+* ∀ i, B i)
    (hcompat : ∀ r i, f (algebraMap R A r) i = algebraMap (K i) (B i) (e r i))
    (hB : ∀ i, ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (K i) ↦ Algebra.Smooth (K i) C)
      (CommAlgCat.of (K i) (B i))) :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} R ↦ Algebra.Smooth R C) (CommAlgCat.of R A) := by
  apply ind_smooth_transport e f
  · intro r
    funext i
    exact hcompat r i
  · exact ind_smooth_pi n K B hB
