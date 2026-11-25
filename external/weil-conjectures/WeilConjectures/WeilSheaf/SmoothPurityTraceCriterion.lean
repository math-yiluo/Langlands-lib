/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeResolution
public import WeilConjectures.WeilSheaf.SmoothPurityFreeComparison

/-!
# Testing a trace on free objects

An invertible comparison with the free functor transfers the universal property of
an underlying trace to free Weil objects. The free resolution criterion then extends
that universal property to bounded Weil objects. This avoids choosing a geometric
comparison for a native right adjoint.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- A universal arrow has an invertible adjoint transpose. -/
theorem isIso_homEquiv_of_bijective
    {C D : Type*} [Category C] [Category D] {T : C ⥤ D} {R : D ⥤ C}
    (adj : T ⊣ R) {H : C} {Y : D} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    IsIso (adj.homEquiv H Y d) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  change Function.Bijective (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d)
  have h : (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d) =
      (adj.homEquiv M Y) ∘ (fun u : M ⟶ H ↦ T.map u ≫ d) := by
    funext u
    exact (adj.homEquiv_naturality_left u d).symm
  rw [h]
  exact (adj.homEquiv M Y).bijective.comp (hd M)

/-- A trace which is universal after forgetting is universal on free objects, provided
the comparison of the free functors is invertible and respects the free units. -/
theorem bijective_map_comp_on_free_of_forget
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {I : C ⥤ C'} {U : C' ⥤ C} (adj₁ : I ⊣ U)
    {J : D ⥤ D'} {V : D' ⥤ D} (adj₂ : J ⊣ V)
    (R : C' ⥤ D') (r : C ⥤ D) (e : R ⋙ V ≅ U ⋙ r)
    {A : C'} {B : D'} (d : R.obj A ⟶ B) (X : C)
    (β : J.obj (r.obj X) ≅ R.obj (I.obj X))
    (hβ : adj₂.unit.app (r.obj X) ≫ V.map β.hom =
      r.map (adj₁.unit.app X) ≫ e.inv.app (I.obj X))
    (h : Function.Bijective (fun u : X ⟶ U.obj A ↦
      r.map u ≫ e.inv.app A ≫ V.map d)) :
    Function.Bijective (fun u : I.obj X ⟶ A ↦ R.map u ≫ d) := by
  have he (u : I.obj X ⟶ A) :
      adj₂.homEquiv (r.obj X) B (β.hom ≫ R.map u ≫ d) =
        r.map (adj₁.homEquiv X A u) ≫ e.inv.app A ≫ V.map d := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hβ]
    erw [← e.inv.naturality_assoc u]
    rfl
  constructor
  · intro u u' huu
    change R.map u ≫ d = R.map u' ≫ d at huu
    apply (adj₁.homEquiv X A).injective
    apply h.1
    change r.map (adj₁.homEquiv X A u) ≫ e.inv.app A ≫ V.map d =
      r.map (adj₁.homEquiv X A u') ≫ e.inv.app A ≫ V.map d
    rw [← he u, ← he u', huu]
  · intro y
    obtain ⟨u, hu⟩ := h.2 (adj₂.homEquiv (r.obj X) B (β.hom ≫ y))
    refine ⟨(adj₁.homEquiv X A).symm u, ?_⟩
    apply (cancel_epi β.hom).1
    apply (adj₂.homEquiv (r.obj X) B).injective
    rw [he, Equiv.apply_symm_apply]
    exact hu

end CategoryTheory.Adjunction

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]

/-- A geometric universal trace lifts to a universal trace on derived Weil objects.
The hypotheses concern the given trace and the comparison on free objects; no
comparison of right adjoints is required. -/
theorem bijective_map_comp_of_forget
    (RW : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    [RW.Additive] [RW.CommShift ℤ] [RW.IsTriangulated]
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (e : RW ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ R)
    (PC : ObjectProperty (DerivedCategory C))
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    {H : DerivedCategory (IsoAlgebra F)} {L' : DerivedCategory (IsoAlgebra G)}
    (d : RW.obj H ⟶ L')
    (β : ∀ X, PC X → ((Free.functor G).mapDerivedCategory.obj (R.obj X) ≅
      RW.obj ((Free.functor F).mapDerivedCategory.obj X)))
    (hβ : ∀ X hX,
      (freeWeilDerivedAdjunction G).unit.app (R.obj X) ≫
          (forget G).mapDerivedCategory.map (β X hX).hom =
        R.map ((freeWeilDerivedAdjunction F).unit.app X) ≫
          e.inv.app ((Free.functor F).mapDerivedCategory.obj X))
    (h : ∀ X, PC X → Function.Bijective
      (fun u : X ⟶ (forget F).mapDerivedCategory.obj H ↦
        R.map u ≫ e.inv.app H ≫ (forget G).mapDerivedCategory.map d))
    (M : DerivedCategory (IsoAlgebra F)) (hM : PC ((forget F).mapDerivedCategory.obj M)) :
    Function.Bijective (fun u : M ⟶ H ↦ RW.map u ≫ d) := by
  apply bijective_map_comp_of_free RW PC hPC_shift d (M := M) (hM := hM)
  intro X hX
  exact Adjunction.bijective_map_comp_on_free_of_forget
    (freeWeilDerivedAdjunction F) (freeWeilDerivedAdjunction G)
    RW R e d X (β X hX) (hβ X hX) (h X hX)

/-- For a functor compatible with the cyclic actions and preserving the free
coproducts, the geometric universal property of a trace implies its Weil universal
property. The required free comparisons are constructed from the forgetful square. -/
theorem bijective_map_comp_of_geometric
    (RW : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    [RW.Additive] [RW.CommShift ℤ] [RW.IsTriangulated]
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (e : RW ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ R)
    (χ : R ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ R)
    (hσ : ∀ A : DerivedCategory (IsoAlgebra F),
      (derivedStrIso G).hom.app (RW.obj A) ≫ e.hom.app A =
        G.mapDerivedCategory.map (e.hom.app A) ≫
          χ.hom.app ((forget F).mapDerivedCategory.obj A) ≫
          R.map ((derivedStrIso F).hom.app A))
    (PC : ObjectProperty (DerivedCategory C))
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    (hcolimit : ∀ X, PC X → CategoryTheory.Limits.PreservesColimit
      (Discrete.functor fun n ↦ (Free.objFunctor F n).mapDerivedCategory.obj X) R)
    {H : DerivedCategory (IsoAlgebra F)} {L' : DerivedCategory (IsoAlgebra G)}
    (d : RW.obj H ⟶ L')
    (h : ∀ X, PC X → Function.Bijective
      (fun u : X ⟶ (forget F).mapDerivedCategory.obj H ↦
        R.map u ≫ e.inv.app H ≫ (forget G).mapDerivedCategory.map d))
    (M : DerivedCategory (IsoAlgebra F)) (hM : PC ((forget F).mapDerivedCategory.obj M)) :
    Function.Bijective (fun u : M ⟶ H ↦ RW.map u ≫ d) := by
  have (X : DerivedCategory C) (hX : PC X) : IsIso (forgetFreeComparison RW R e X) := by
    have := hcolimit X hX
    exact isIso_forgetFreeComparison RW R e χ hσ X
  exact bijective_map_comp_of_forget RW R e PC hPC_shift d
    (fun X hX ↦ @asIso _ _ _ _ (forgetFreeComparison RW R e X) (this X hX))
    (fun X _ ↦ unit_app_comp_map_forgetFreeComparison RW R e X) h M hM

end CategoryTheory.Endofunctor.IsoAlgebra
