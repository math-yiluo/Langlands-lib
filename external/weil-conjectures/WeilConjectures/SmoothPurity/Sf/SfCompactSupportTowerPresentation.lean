/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportTower
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.CompactSupportProperImageTower.CompactSupportProperImageTower
import WeilConjectures.SmoothPurity.Sf.SfDirectImageTransitionPresentation
import WeilConjectures.SmoothPurity.Sf.SfSupportTransitionPresentation

/-! # Slice and intrinsic presentations of the compact-support tower

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tags 03DI, 0D6E, 0E8I.
(blueprint: lem-sf-compact-support-slice-intrinsic-towers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

private theorem towerIsoOfSteps
    {C : Type*} [Category C] {A B : ℕ → C}
    (a : ∀ n, A (n + 1) ⟶ A n) (b : ∀ n, B (n + 1) ⟶ B n)
    (ι : ∀ n, A n ≅ B n)
    (h : ∀ n, a n ≫ (ι n).hom = (ι (n + 1)).hom ≫ b n) :
    Nonempty (Functor.ofOpSequence a ≅ Functor.ofOpSequence b) := by
  let τ : Functor.ofOpSequence a ⟶ Functor.ofOpSequence b :=
    NatTrans.ofOpSequence (fun n ↦ (ι n).hom) (by
      intro n
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using h n)
  have : ∀ n, IsIso (τ.app n) := fun n ↦ inferInstanceAs (IsIso (ι n.unop).hom)
  have : IsIso τ := (NatTrans.isIso_iff_isIso_app τ).mpr inferInstance
  exact ⟨asIso τ⟩

/-- The concrete slice extension is the intrinsic extension at each finite level.
The proper and support systems are naturally isomorphic to the published ordinary
and compact-support systems, including all quotient maps. This comparison assumes
only the section and resolution normalizations of the operation records; it has no
constructibility conclusion and requires no finite-field hypothesis.

Source: Bhatt--Scholze, Definition 6.7.6; Stacks Tags 03DI, 0D6E, 0E8I and 06YY.
(blueprint: lem-sf-compact-support-slice-intrinsic-towers).

Proof: use sfFiniteOpenPresentation for the ordinary finite comparison and its
coefficient square. The ordinary direct-image terms coincide definitionally;
sfDirectImageTransition_presentation supplies their adjacent transition identity.
The explicit sfSupportPresentationLevel maps are obtained by exact localization of
the finite comparison followed by direct image and restriction. Their adjacent
square is sfSupportTransition_presentation. Finally NatTrans.ofOpSequence extends
both adjacent squares to all arrows of ℕᵒᵖ. The resulting transformations are
isomorphisms because every component is invertible. Thus the categorical assembly
is complete; the three presentation identities are separate named obligations. -/
theorem sfCompactSupportTower_presentation
    (c : Compactification f) (o : IntegralOpenReduction.Operations l E c.i)
    (d : CompactSupportProperImageTower.DirectData l E c.g)
    (e : CompactSupportProperImageTower.OpenData l E c.i o) :
    (∀ n : ℕ, Nonempty (IntegralOpenReduction.finiteExtension l E c.i o n ≅
      sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    ∀ K : (IntegralOpenReduction.complete l E X).FullSubcategory,
      Nonempty (Functor.ofOpSequence
        (sfDirectImageTransition l E c.g ((IntegralOpenReduction.shriek l E c.i o).obj
          K.obj)) ≅ CompactSupportProperImageTower.properTower l E c.i c.g o
            (d := d) K.obj) ∧
      Nonempty (CompactSupportProperImageTower.supportTower l E c.i c.g o
        (d := d) e K.obj ≅
          Functor.ofOpSequence (sfCompactSupportTransition l E c K.obj)) := by
  obtain ⟨ι, hι⟩ := sfFiniteOpenPresentation l E c.i o e
  refine ⟨fun n ↦ ⟨ι n⟩, ?_⟩
  intro K
  constructor
  · apply towerIsoOfSteps
      (sfDirectImageTransition l E c.g ((IntegralOpenReduction.shriek l E c.i o).obj
        K.obj))
      (CompactSupportProperImageTower.properTransition l E c.i c.g o (d := d) K.obj)
      (fun _ ↦ Iso.refl _)
    intro n
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      CompactSupportProperImageTower.properTransition] using
      sfDirectImageTransition_presentation l E c.g d
        ((IntegralOpenReduction.shriek l E c.i o).obj K.obj) n
  · exact towerIsoOfSteps
      (CompactSupportProperImageTower.supportTransition l E c.i c.g o (d := d) e K.obj)
      (sfCompactSupportTransition l E c K.obj)
      (sfSupportPresentationLevel l E c o d ι K.obj)
      (sfSupportTransition_presentation l E c o d e ι hι K.obj)

end WeilConjectures
