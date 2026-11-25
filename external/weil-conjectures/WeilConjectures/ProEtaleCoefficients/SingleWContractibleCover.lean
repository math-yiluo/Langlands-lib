/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! Single w-contractible affine covers in the pro-etale site.
(blueprint: det-pe-hypercover-single-cover) -/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry
open CategoryTheory

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
set_option backward.isDefEq.respectTransparency.types false in
/-- Every quasi-compact pro-etale object has a singleton cover by a w-contractible spectrum.

Source: Stacks Project, Tag 09A1 (2), using the affine-cover theorem of Tag 0F4P and
w-contractible extension theorem of Tags 0983 and 0990.
(blueprint: det-pe-hypercover-single-cover)

Proof: choose an affine singleton cover A of V by the existing qc affine-cover theorem.
Apply the proved w-contractible-extension theorem to the ring of global sections of A.
The resulting ind-etale faithfully flat map gives a weakly etale surjective spectrum map.
Since both spectra are affine, this is a pro-etale singleton cover. Compose it with the
inverse of the canonical affine spectrum isomorphism and then with A to V. Precoverage
composition gives the required cover; weak etaleness composes with A to X. This also works
for the empty target: its affine coordinate ring and its unital extensions are zero.
-/
theorem exists_single_wContractible_affine_cover
    (X : Scheme.{u}) (V : X.ProEt) (hVqc : CompactSpace V.left) :
    ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f)
      (g : @Scheme.ProEt.mk X _ f hf ⟶ V),
      IsWContractibleRing D ∧
        Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V := by
  let : CompactSpace V.left := hVqc
  obtain ⟨A, g, hg, hA, _⟩ :=
    Scheme.ProEt.exists_affine_weaklyContractible_cover X V
  let := hA
  obtain ⟨D, hD, hAlg, hind, hff, hw⟩ := exists_isWContractibleRing Γ(A.left, ⊤)
  let φ : Γ(A.left, ⊤) ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap _ _)
  have hp : WeaklyEtale (Spec.map φ) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 hind)
  have hsurj : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 hff)).2
  let p : Spec (.of D) ⟶ A.left := Spec.map φ ≫ A.left.isoSpec.inv
  have hp' : WeaklyEtale p := by dsimp [p]; infer_instance
  let f : Spec (.of D) ⟶ X := p ≫ A.hom
  have hf : WeaklyEtale f := by dsimp [f]; infer_instance
  let a : @Scheme.ProEt.mk X _ f hf ⟶ A :=
    MorphismProperty.Over.homMk p rfl
  refine ⟨.of D, f, hf, a ≫ g, hw, ?_⟩
  have hmap : Presieve.singleton (Spec.map φ) ∈ Scheme.proetalePrecoverage _ :=
    Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) hp
  have he : Presieve.singleton A.left.isoSpec.inv ∈ Scheme.proetalePrecoverage _ :=
    Precoverage.mem_coverings_of_isIso _
  have hpg : Presieve.singleton g.left ∈ Scheme.proetalePrecoverage V.left := by
    simpa [Scheme.ProEt.precoverage, Presieve.map_singleton, Scheme.ProEt.forget,
      MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      MorphismProperty.Comma.Hom.hom] using hg
  have hpa := singleton_comp_cover Scheme.proetalePrecoverage _ _ hmap he
  have hfinal := singleton_comp_cover Scheme.proetalePrecoverage _ _ hpa hpg
  have hh : Presieve.singleton (a ≫ g).left ∈ Scheme.proetalePrecoverage V.left := by
    rw [MorphismProperty.Comma.comp_left]
    exact hfinal
  simpa [Scheme.ProEt.precoverage, Presieve.map_singleton, Scheme.ProEt.forget,
    MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
    MorphismProperty.Comma.Hom.hom] using hh
