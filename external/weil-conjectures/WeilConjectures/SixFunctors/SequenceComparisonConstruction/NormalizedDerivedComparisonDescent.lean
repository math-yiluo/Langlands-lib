/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of normalized derived comparisons

Source: Stacks 06YY and 0D6D; the complete generic proof from
IntegralComparisonSequenceSystems.
(blueprint: lem-sf-normalized-derived-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SequenceComparisonConstruction

private theorem normalizedComparisonDescent
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {E : Type e} [Category.{f} E]
    (L : C ⥤ D) (P : ObjectProperty C)
    (ff : ((whiskeringLeft P.FullSubcategory D E).obj (P.ι ⋙ L)).FullyFaithful)
    (F G : D ⥤ E) (H : C ⥤ E) (α : L ⋙ F ⟶ H) (β : L ⋙ G ⟶ H)
    (hα : ∀ X, P X → IsIso (α.app X)) (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃! a : F ≅ G, ∀ X, P X → α.app X = a.hom.app (L.obj X) ≫ β.app X := by
  let eα : (P.ι ⋙ L) ⋙ F ≅ P.ι ⋙ H := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (α.app X.obj) (hα X.obj X.property))
    (fun g ↦ α.naturality g.hom)
  let eβ : (P.ι ⋙ L) ⋙ G ≅ P.ι ⋙ H := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (β.app X.obj) (hβ X.obj X.property))
    (fun g ↦ β.naturality g.hom)
  let a : F ≅ G := ff.preimageIso (eα ≪≫ eβ.symm)
  have ha (X : C) (hX : P X) :
      α.app X = a.hom.app (L.obj X) ≫ β.app X := by
    have := hβ X hX
    have hh := congrArg (fun t ↦ t.app ⟨X, hX⟩) (ff.map_preimage (eα ≪≫ eβ.symm).hom)
    change a.hom.app (L.obj X) = α.app X ≫ CategoryTheory.inv (β.app X) at hh
    rw [hh, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply ff.map_injective
  ext X
  have := hβ X.obj X.property
  apply (cancel_mono (β.app X.obj)).1
  exact (ha' X.obj X.property).symm.trans (ha X.obj X.property)

private theorem isIso_on_resolution
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {E : Type e} [Category.{f} E]
    (L : C ⥤ D) (F G : D ⥤ E) (H : C ⥤ E)
    (α : L ⋙ F ⟶ H) (β : L ⋙ G ⟶ H)
    {X Y : C} (q : X ⟶ Y) [IsIso (L.map q)]
    [IsIso (α.app X)] [IsIso (β.app X)] [IsIso (β.app Y)] : IsIso (α.app Y) := by
  have : IsIso ((L ⋙ G).map q) := inferInstanceAs (IsIso (G.map (L.map q)))
  have : IsIso (H.map q) := IsIso.of_isIso_fac_left (β.naturality q).symm
  have : IsIso ((L ⋙ F).map q) := inferInstanceAs (IsIso (F.map (L.map q)))
  exact IsIso.of_isIso_fac_left (α.naturality q)

universe g h wA wB wC wD

/-- Unique derived comparison from a normalized comparison on resolving representatives.
Source: Stacks 06YY and 0D6D
(blueprint: lem-sf-normalized-derived-comparison-descent).
Proof: form alpha and beta into the same cochain target using the exact functor
factorizations and the ordinary comparison. The first counit makes beta invertible
on the resolving class. The second makes alpha invertible on the good subclass.
Resolve an arbitrary member of the resolving class by a good member; naturality
and inversion of quasi-isomorphisms give invertibility of alpha there. Their
ratio is an isomorphism after restriction to the resolving subcategory. Lift it
by fully faithful restriction. The lifted hom satisfies the normalization by
map_preimage and cancellation with beta. Injectivity of restriction and the same
cancellation prove uniqueness. -/
theorem derivedComparison
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {C : Type e} [Category.{f} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type g} [Category.{h} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (p : A ⥤ B) [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : C ⥤ D) [q.Additive] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    (s : A ⥤ C) [s.Additive] (t : B ⥤ D) [t.Additive]
    (LS : DerivedCategory A ⥤ DerivedCategory C)
    (LT : DerivedCategory B ⥤ DerivedCategory D)
    (εS : DerivedCategory.Q ⋙ LS ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εT : DerivedCategory.Q ⋙ LT ⟶ t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : p ⋙ t ≅ s ⋙ q) (R good : ObjectProperty (CochainComplex A ℤ))
    (ff : ((whiskeringLeft R.FullSubcategory (DerivedCategory A) (DerivedCategory D)).obj
      (R.ι ⋙ DerivedCategory.Q)).FullyFaithful)
    (hgood : ∀ X, good X → R X)
    (hres : ∀ X, R X → ∃ (Y : CochainComplex A ℤ) (r : Y ⟶ X), good Y ∧ QuasiIso r)
    (hS : ∀ X, R X → IsIso (εS.app X))
    (hT : ∀ X, good X → IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X))) :
    ∃! a : p.mapDerivedCategory ⋙ LT ≅ LS ⋙ q.mapDerivedCategory,
      ∀ X, R X →
        LT.map (p.mapDerivedCategoryFactors.hom.app X) ≫
          εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app X) =
        a.hom.app (DerivedCategory.Q.obj X) ≫ q.mapDerivedCategory.map (εS.app X) ≫
          q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj X) := by
  let F := p.mapDerivedCategory ⋙ LT
  let G := LS ⋙ q.mapDerivedCategory
  let H := s.mapHomologicalComplex (.up ℤ) ⋙ q.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q
  let α : DerivedCategory.Q ⋙ F ⟶ H :=
    whiskerRight p.mapDerivedCategoryFactors.hom LT ≫
      whiskerLeft (p.mapHomologicalComplex (.up ℤ)) εT ≫
        whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q
  let β : DerivedCategory.Q ⋙ G ⟶ H :=
    whiskerRight εS q.mapDerivedCategory ≫
      whiskerLeft (s.mapHomologicalComplex (.up ℤ)) q.mapDerivedCategoryFactors.hom
  have hβ (X) (hX : R X) : IsIso (β.app X) := by
    let : IsIso (εS.app X) := hS X hX
    change IsIso (q.mapDerivedCategory.map (εS.app X) ≫
      q.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj X))
    infer_instance
  have hαgood (X) (hX : good X) : IsIso (α.app X) := by
    let : IsIso (εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X)) := hT X hX
    change IsIso (LT.map (p.mapDerivedCategoryFactors.hom.app X) ≫
      εT.app ((p.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app X))
    exact IsIso.comp_isIso' (by infer_instance)
      (IsIso.comp_isIso' (hT X hX)
        (Iso.isIso_hom (DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex c (.up ℤ)).app X))))
  have hα (X) (hX : R X) : IsIso (α.app X) := by
    obtain ⟨Y, r, hY, hr⟩ := hres X hX
    have := hαgood Y hY
    have := hβ Y (hgood Y hY)
    have := hβ X hX
    have : QuasiIso r := hr
    exact isIso_on_resolution DerivedCategory.Q F G H α β r
  exact normalizedComparisonDescent DerivedCategory.Q R ff F G H α β hα hβ

end SequenceComparisonConstruction
