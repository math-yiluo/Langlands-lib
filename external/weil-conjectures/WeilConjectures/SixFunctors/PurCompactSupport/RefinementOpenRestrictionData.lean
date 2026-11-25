/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! A natural transformation with the specified refinement-restriction components. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

private def counitRestriction
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {L : A ⥤ B} {P : B ⥤ A} (ε : P ⋙ L ⟶ 𝟭 B)
    (F : B ⥤ C) {G : A ⥤ C} (α : G ⟶ L ⋙ F) : P ⋙ G ⟶ F where
  app M := α.app (P.obj M) ≫ F.map (ε.app M)
  naturality {M N} a := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [reassoc_of% α.naturality (P.map a)]
    have hε := ε.naturality a
    dsimp only [Functor.comp_map, Functor.id_map] at hε
    rw [← Functor.map_comp, hε, Functor.map_comp]
    exact (Category.assoc _ _ _).symm

private theorem exists_counitRestriction_of_eq
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {S : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} S]
    {L : A ⥤ B} {P : B ⥤ A} {F : B ⥤ C} {G : A ⥤ C} {K : S ⥤ B}
    {ε : P ⋙ L ⟶ 𝟭 B} {α : G ⟶ L ⋙ F}
    {φ : ∀ M, ((K ⋙ P) ⋙ G).obj M ⟶ (K ⋙ F).obj M}
    (h : ∀ M, φ M = α.app (P.obj (K.obj M)) ≫ F.map (ε.app (K.obj M))) :
    ∃ θ : (K ⋙ P) ⋙ G ⟶ K ⋙ F, ∀ M, θ.app M = φ M := by
  exact ⟨Functor.whiskerLeft K (counitRestriction ε F α), fun M ↦ (h M).symm⟩

/--
Source: Stacks 0F7B and 0F7I, the restriction-to-open and proper-base-change
construction.  The componentwise proper restriction maps are natural in the
unbounded derived module category.  This is the component-construction part of
`lem-sf-refinement-open-restriction`; invertibility and shift compatibility are
recorded separately.
(blueprint: lem-sf-refinement-open-restriction-data).
-/
theorem refinementRestriction_data :
    ∃ θ : ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
        (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i,
      ∀ M, θ.app M = refinementRestriction R r hi M := by
  -- Normalize the open triangle before instantiating the categorical construction;
  -- otherwise conversion unfolds the transported pullback isomorphism extensively.
  revert hi
  rcases c with ⟨Zc, gc, ic, hc, hpc, hoc⟩
  rcases d with ⟨Zd, gd, jd, hd, hpd, hod⟩
  rcases r with ⟨v, hv, hvg⟩
  change Zc ⟶ Zd at v
  change ic ≫ v = jd at hv
  change v ≫ gd = gc at hvg
  subst jd
  intro hi
  let c : Compactification f := ⟨Zc, gc, ic, hc, hpc, hoc⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ v, hd, hpd, hod⟩
  let r : c.Refinement d := ⟨v, rfl, hvg⟩
  exact exists_counitRestriction_of_eq (fun M ↦ refinementRestriction.eq_def R r hi M)

end WeilConjectures.PurCompactSupport
