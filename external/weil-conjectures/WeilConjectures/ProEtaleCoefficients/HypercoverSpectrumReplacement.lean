/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-! Transporting a hypercover to spectrum representatives.
(blueprint: det-pe-hypercover-spectrum-replacement) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

private theorem singleton_comp_cover {C : Type*} [Category C]
    (J : Precoverage C) [J.IsStableUnderComposition]
    {A B T : C} (f : A ⟶ B) (g : B ⟶ T)
    (hf : Presieve.singleton f ∈ J B) (hg : Presieve.singleton g ∈ J T) :
    Presieve.singleton (f ≫ g) ∈ J T := by
  have h := Precoverage.comp_mem_coverings (J := J)
    (X := fun _ : PUnit.{1} ↦ B) (fun _ ↦ g)
    (by simpa only [Presieve.ofArrows_pUnit] using hg)
    (Y := fun _ _ : PUnit.{1} ↦ A) (fun _ _ ↦ f)
    (fun _ ↦ by simpa only [Presieve.ofArrows_pUnit] using hf)
  have heq : Presieve.ofArrows (fun _ : Sigma (fun _ : PUnit.{1} ↦ PUnit.{1}) ↦ A)
      (fun _ ↦ f ≫ g) = Presieve.singleton (f ≫ g) := by
    funext Z h
    apply propext
    constructor
    · rintro ⟨i⟩
      exact Presieve.singleton_self _
    · rintro ⟨⟩
      exact ⟨⟨PUnit.unit, PUnit.unit⟩⟩
  exact heq ▸ h

set_option backward.isDefEq.respectTransparency false in
/-- Replace the terms of a hypercover by specified spectra.
Source: Stacks Project, Tag 09A1 (2), final finite-disjoint-union step.
(blueprint: det-pe-hypercover-spectrum-replacement)

Proof: choose the supplied spectrum isomorphisms and give each spectrum the transported
structure map and augmentation. Conjugate every simplicial operator by these isomorphisms.
The inverse pairs cancel, proving the functor laws. Transport each proper-face cone along
the induced isomorphism of diagrams, keeping its vertex. Compose the old matching map with
the source isomorphism. The projection identities follow from naturality; the transported
cone is limiting. Isomorphisms are singleton covers and covers compose, so the matching
and augmentation arrows remain covers. This includes empty spectra and the zero ring.
-/
theorem hypercover_spectrum_replacement (X : Scheme.{u}) (U : X.ProEt)
    (V : SimplicialObject (Over U))
    (hterm : ∀ n : ℕ, ∃ D : CommRingCat.{u},
      IsWContractibleRing D ∧ Nonempty (Spec D ≅ (V _⦋n⦌).left.left))
    (hzero : Presieve.singleton (V _⦋0⦌).hom ∈ Scheme.ProEt.precoverage X U)
    (hmatch : ∀ n : ℕ, ∃ (c : Cone (V.properFaceDiagram (n + 1)))
      (μ : V _⦋n + 1⦌ ⟶ c.pt), Nonempty (IsLimit c) ∧
        Presieve.singleton μ.left ∈ Scheme.ProEt.precoverage X c.pt.left ∧
        ∀ a : SimplicialObject.ProperFaceCategory (n + 1),
          μ ≫ c.π.app (op a) = V.map a.obj.hom.op) :
    ∃ (W : SimplicialObject (Over U)),
      (∀ n : ℕ, ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
        IsWContractibleRing D ∧ (W _⦋n⦌).left = @Scheme.ProEt.mk X _ f hf) ∧
      Presieve.singleton (W _⦋0⦌).hom ∈ Scheme.ProEt.precoverage X U ∧
      (∀ n : ℕ, ∃ (c : Cone (W.properFaceDiagram (n + 1)))
        (μ : W _⦋n + 1⦌ ⟶ c.pt), Nonempty (IsLimit c) ∧
          Presieve.singleton μ.left ∈ Scheme.ProEt.precoverage X c.pt.left ∧
          ∀ a : SimplicialObject.ProperFaceCategory (n + 1),
            μ ≫ c.π.app (op a) = W.map a.obj.hom.op) := by
  classical
  have : (Scheme.ProEt.precoverage X).HasIsos := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  have : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [Scheme.ProEt.precoverage]; infer_instance
  choose D hD he using hterm
  let e (n : ℕ) := (he n).some
  let f (n : ℕ) : Spec (D n) ⟶ X := (e n).hom ≫ (V _⦋n⦌).left.hom
  have hf (n : ℕ) : WeaklyEtale (f n) := by dsimp [f]; infer_instance
  let A (n : ℕ) : X.ProEt := @Scheme.ProEt.mk X _ (f n) (hf n)
  let b (n : ℕ) : A n ≅ (V _⦋n⦌).left :=
    MorphismProperty.Over.isoMk (e n) rfl
  let Q (n : ℕ) : Over U := Over.mk ((b n).hom ≫ (V _⦋n⦌).hom)
  let q (n : ℕ) : Q n ≅ V _⦋n⦌ := Over.isoMk (b n) rfl
  let W : SimplicialObject (Over U) :=
    { obj := fun n ↦ Q n.unop.len
      map := fun {n m} φ ↦ (q n.unop.len).hom ≫ V.map φ ≫ (q m.unop.len).inv
      map_id := by intro n; simp
      map_comp := by intro n m l φ ψ; simp [Category.assoc] }
  let z : W ≅ V := NatIso.ofComponents (fun n ↦ q n.unop.len) (by
    intro n m φ
    simp [W, Category.assoc])
  refine ⟨W, ?_, ?_, ?_⟩
  · intro n
    exact ⟨D n, f n, hf n, hD n, rfl⟩
  · exact singleton_comp_cover (Scheme.ProEt.precoverage X)
      (b 0).hom (V _⦋0⦌).hom (Precoverage.mem_coverings_of_isIso _) hzero
  · intro n
    obtain ⟨c, μ, ⟨hc⟩, hcov, hproj⟩ := hmatch n
    let d : W.properFaceDiagram (n + 1) ≅ V.properFaceDiagram (n + 1) :=
      NatIso.ofComponents (fun a ↦ z.app (op a.unop.obj.left)) (by
        intro a b φ
        exact z.hom.naturality φ.unop.hom.left.op)
    let c' := (Cone.postcompose d.inv).obj c
    let μ' : W _⦋n + 1⦌ ⟶ c'.pt := (z.app (op ⦋n + 1⦌)).hom ≫ μ
    refine ⟨c', μ', ⟨(IsLimit.postcomposeHomEquiv d.symm c).symm hc⟩, ?_, ?_⟩
    · exact singleton_comp_cover (Scheme.ProEt.precoverage X)
        (z.app (op ⦋n + 1⦌)).hom.left μ.left
        (Precoverage.mem_coverings_of_isIso _) hcov
    · intro a
      simpa [μ', c', d, W, z, Category.assoc] using
        congrArg (fun t ↦ (q (n + 1)).hom ≫ t ≫ (q a.obj.left.len).inv) (hproj a)
