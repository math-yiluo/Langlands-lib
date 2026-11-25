/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.RingTheory.PairHenselizationStageSections

/-!
# Lifting étale sections over the colimit of pair neighbourhoods

Source: Stacks Project, More on Algebra, Tag 0A02, the paragraph verifying
condition (2) of Tag 09XI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem descend_etale
    {B : Type u} [CommRing B]
    (P : ObjectProperty (Under (CommRingCat.of B)))
    [EssentiallySmall.{u} P.FullSubcategory] [IsFiltered P.FullSubcategory]
    (c : Cocone P.ι) (hc : IsColimit c)
    (A : Type u) [CommRing A] [Algebra c.pt.right A] [Algebra.Etale c.pt.right A] :
    ∃ (i : P.FullSubcategory) (D : Type u) (_ : CommRing D)
      (g : i.obj.right →+* D),
      let : Algebra i.obj.right c.pt.right := (c.ι.app i).right.hom.toAlgebra
      let : Algebra i.obj.right D := g.toAlgebra
      Algebra.Etale i.obj.right D ∧
        Nonempty (A ≃ₐ[c.pt.right] TensorProduct i.obj.right c.pt.right D) := by
  classical
  let E := equivSmallModel.{u} P.FullSubcategory
  let : IsFiltered (SmallModel.{u} P.FullSubcategory) := IsFiltered.of_equivalence E
  let F := E.inverse ⋙ P.ι ⋙ Under.forget (CommRingCat.of B)
  let d := (Under.forget (CommRingCat.of B)).mapCocone (c.whisker E.inverse)
  have hd : IsColimit d :=
    isColimitOfPreserves (Under.forget (CommRingCat.of B)) (hc.whiskerEquivalence E.symm)
  let H := c.pt.right
  let : Algebra (ULift.{u} ℤ) H :=
    ((Int.castRingHom H).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : ∀ i, Algebra (ULift.{u} ℤ) (F.obj i) := fun i ↦
    ((Int.castRingHom (F.obj i)).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨R, D₀, instRing, instAlg, hfg, het, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg (ULift.{u} ℤ) H A
  have : Algebra.FiniteType (ULift.{u} ℤ) R := R.fg_iff_finiteType.mp hfg
  let Z := CommRingCat.of (ULift.{u} ℤ)
  let α : (Functor.const (SmallModel.{u} P.FullSubcategory)).obj Z ⟶ F :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (F.obj i))
      naturality := by
        intro i k h
        ext ⟨x⟩
        change (x : F.obj k) = (F.map h).hom (x : F.obj i)
        simp }
  let j : Z ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R)
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hj : j.hom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨i, g, _, hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit Z F α j d hd hj
      (CommRingCat.ofHom R.val.toRingHom) (by
        intro i
        ext ⟨x⟩
        change (x : H) = (d.ι.app i).hom (x : F.obj i)
        exact (map_intCast (d.ι.app i).hom x).symm)
  let : Algebra R (F.obj i) := g.hom.toAlgebra
  let : Algebra (F.obj i) H := (d.ι.app i).hom.toAlgebra
  have : IsScalarTower R (F.obj i) H :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hg)
  let D := TensorProduct R (F.obj i) D₀
  let : CommRing D := inferInstance
  have cancel (R S H D₀ D : Type u) [CommRing R] [CommRing S] [CommRing H]
      [CommRing D₀] [CommRing D] [Algebra R S] [Algebra R H] [Algebra R D₀]
      [Algebra S H] [IsScalarTower R S H] [Algebra S D]
      (e : D ≃ₐ[S] TensorProduct R S D₀) :
      let : Algebra S D := (algebraMap S D).toAlgebra
      Nonempty ((TensorProduct R H D₀) ≃ₐ[H] TensorProduct S H D) := by
    rw [toAlgebra_algebraMap]
    exact ⟨(Algebra.TensorProduct.cancelBaseChange R S H H D₀).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := H)) e.symm)⟩
  have hD : let : Algebra (F.obj i) D := (algebraMap (F.obj i) D).toAlgebra
      Algebra.Etale (F.obj i) D := by
    rw [toAlgebra_algebraMap]
    infer_instance
  obtain ⟨ec⟩ := cancel R (F.obj i) H D₀ D AlgEquiv.refl
  have e' := e.trans ec
  exact ⟨E.inverse.obj i, D, inferInstance, algebraMap (F.obj i) D, hD, ⟨e'⟩⟩

/-- Every étale section modulo the extended ideal lifts over a colimit of all étale
neighbourhoods of a pair whose quotient is the original quotient.
Source: Stacks Project, More on Algebra, Tag 0A02, verification of condition (2)
of Tag 09XI (blueprint: lem-weil-pbc-pair-henselization-sections).

Proof: Pass to a small equivalent filtered category and forget to commutative rings;
forgetting rings under B preserves this connected colimit. The given quotient
bijection identifies H/JH with R = B/J. Descend an étale H-algebra A to an étale
C-algebra D at a stage C, using Tag 00U2 and the colimit comparison isomorphism.
Restrict the given section to D to obtain a C-algebra map s : D to R. It kills JD.
The induced étale R-algebra D/JD has a section to R. Split this section by the
idempotent splitting theorem, obtaining e in D/JD whose image in R is 1 and whose
localization is R. Choose g in D lifting e. Localization at g is étale over D, hence
over B, and its quotient by J is R since localization commutes with quotient.
Consequently D[1/g] is an object of the original neighbourhood category, and C to
D[1/g] is a morphism in that category. Its coprojection to H therefore restricts
to the original coprojection from C. The tensor-product universal property gives
an H-algebra map A = H tensor_C D to H. Its reduction equals the chosen section:
s(g) = 1 makes s extend to D[1/g], and this extension equals the unique B-algebra
map from that object to R. This uniqueness follows by factoring through the
quotient isomorphism B/J to D[1/g]/JD[1/g]. Compare the maps on D and on H and use
the tensor-product universal property once more. Transport along the descent
isomorphism to obtain the required lift of the original section. -/
theorem pair_henselization_sections (B : Type u) [CommRing B] (J : Ideal B)
    [EssentiallySmall.{u} (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map))))]
    [IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map))))]
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c)
    (hq : Function.Bijective (Ideal.quotientMap (J.map c.pt.hom.hom) c.pt.hom.hom
      (Ideal.le_comap_map)))
    (A : Type u) [CommRing A] [Algebra c.pt.right A] [Algebra.Etale c.pt.right A]
    (σ : A →ₐ[c.pt.right] c.pt.right ⧸ J.map c.pt.hom.hom) :
    ∃ τ : A →ₐ[c.pt.right] c.pt.right,
      (Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).comp τ = σ := by
  classical
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        Ideal.le_comap_map)
  obtain ⟨i, D, instD, g, hd, ⟨e⟩⟩ := descend_etale P c hc A
  let : Algebra i.obj.right c.pt.right := (c.ι.app i).right.hom.toAlgebra
  let : Algebra i.obj.right D := g.toAlgebra
  let : Algebra.Etale i.obj.right D := hd
  let σ' := σ.comp e.symm.toAlgHom
  let s := (σ'.restrictScalars i.obj.right).comp Algebra.TensorProduct.includeRight
  obtain ⟨t, ht⟩ := pair_henselization_stage_sections B J c hq i D g hd s
  let τ' := Algebra.TensorProduct.lift (AlgHom.id c.pt.right c.pt.right) t
    (fun _ _ ↦ Commute.all _ _)
  refine ⟨τ'.comp e.toAlgHom, ?_⟩
  have hred : (Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).comp τ' = σ' := by
    apply (Algebra.TensorProduct.liftEquivRight i.obj.right c.pt.right D
      (c.pt.right ⧸ J.map c.pt.hom.hom)).symm.injective
    change (((Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).comp τ').restrictScalars
      i.obj.right).comp Algebra.TensorProduct.includeRight = s
    ext x
    simpa [τ', AlgHom.comp_apply, Algebra.TensorProduct.includeRight] using
      DFunLike.congr_fun ht x
  ext x
  change ((Ideal.Quotient.mkₐ c.pt.right (J.map c.pt.hom.hom)).comp τ') (e x) = σ x
  rw [hred]
  simp [σ']

end RingTheory
