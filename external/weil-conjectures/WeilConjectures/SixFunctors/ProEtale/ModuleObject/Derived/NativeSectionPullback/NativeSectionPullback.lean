/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # Restricting native condensed pullbacks along a section

These are the formal compositor and unit identities used when restricting the
normalized DNC family comparison (blueprint: lemma-section-normal-bundle--1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeSectionPullback

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A pullback compositor with its composite named explicitly.
Source: the pullback identities in the family-constancy proof
(blueprint: lem-pur-native-section-pullback). -/
@[irreducible] def compAlong {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) :
    (upperStar Λ k).leftDerivedFunctor ≅
      (upperStar Λ g).leftDerivedFunctor ⋙ (upperStar Λ f).leftDerivedFunctor :=
by
  subst k
  exact leftDerivedUpperStarComp Λ f g

/-- Objectwise form of the compositor's equality transport.
Source: named-composite pullback coherence
(blueprint: lem-pur-native-section-pullback). -/
theorem compAlong_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (compAlong Λ f g k h).hom.app C =
      eqToHom (congrArg
        (fun (t : X ⟶ Z) ↦ (upperStar Λ t).leftDerivedFunctor.obj C) h.symm) ≫
        (leftDerivedUpperStarComp Λ f g).hom.app C := by
  subst k
  simp only [compAlong, eqToHom_refl, Category.id_comp]

/-- The inverse objectwise equality transport for a named compositor.
Source: named-composite pullback coherence
(blueprint: lem-pur-native-section-pullback). -/
theorem compAlong_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (compAlong Λ f g k h).inv.app C =
      (leftDerivedUpperStarComp Λ f g).inv.app C ≫
        eqToHom (congrArg
          (fun (t : X ⟶ Z) ↦ (upperStar Λ t).leftDerivedFunctor.obj C) h) := by
  subst k
  simp only [compAlong, eqToHom_refl, Category.comp_id]

/-- The compositor associativity law with named composites.
Source: pullback coherence used in family constancy
(blueprint: lem-pur-native-section-pullback). -/
theorem compAlong_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hleft : f ≫ gh = fgh) (hright : fg ≫ h = fgh)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (compAlong Λ fg h fgh hright).hom.app C ≫
        (compAlong Λ f g fg hfg).hom.app (((upperStar Λ h).leftDerivedFunctor).obj C) =
      (compAlong Λ f gh fgh hleft).hom.app C ≫
        ((upperStar Λ f).leftDerivedFunctor).map ((compAlong Λ g h gh hgh).hom.app C) := by
  subst fg
  subst gh
  subst fgh
  simp only [compAlong_hom_app, eqToHom_refl, Category.id_comp]
  rw [← cancel_epi (eqToHom (congrArg
    (fun (k : W ⟶ Z) ↦ ((upperStar Λ k).leftDerivedFunctor).obj C) (Category.assoc f g h)))]
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.refl_hom, NatTrans.id_app, Functor.map_comp, CategoryTheory.Functor.map_id]
    using leftDerivedUpperStarComp_assoc_app Λ f g h C

/-- Pullback along a section evaluates a constant family.
Source: family constancy and its normalization
(blueprint: lem-pur-native-section-pullback). -/
def sectionIso {B P : Scheme.{u}} (i : B ⟶ P) (a : P ⟶ B) (h : i ≫ a = 𝟙 B) :
    (upperStar Λ a).leftDerivedFunctor ⋙ (upperStar Λ i).leftDerivedFunctor ≅ 𝟭 _ :=
  (compAlong Λ i a (𝟙 B) h).symm ≪≫ leftDerivedUpperStarId Λ B

private theorem compAlong_id_left {X Y : Scheme.{u}} (g : X ⟶ Y)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (compAlong Λ (𝟙 X) g g (Category.id_comp g)).hom.app C ≫
      (leftDerivedUpperStarId Λ X).hom.app (((upperStar Λ g).leftDerivedFunctor).obj C) =
        𝟙 _ := by
  rw [compAlong_hom_app, Category.assoc, leftDerivedUpperStarComp_id_left_app]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem compAlong_id_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (compAlong Λ f (𝟙 Y) f (Category.comp_id f)).hom.app C ≫
      ((upperStar Λ f).leftDerivedFunctor).map ((leftDerivedUpperStarId Λ Y).hom.app C) =
        𝟙 _ := by
  rw [compAlong_hom_app, Category.assoc, leftDerivedUpperStarComp_id_right_app]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem section_pasting {K : Type*} [Category K]
    {T A B S F G H J : K}
    (p : T ≅ A) (q : A ≅ B) (r : A ≅ S) (s : F ≅ S)
    (t : T ≅ F) (u : F ≅ T) (v : T ≅ G) (z : G ≅ B)
    (w : G ≅ J) (a : H ≅ J) (b : T ≅ H) (d : H ≅ T)
    (A1 : p.hom ≫ r.hom = t.hom ≫ s.hom)
    (A2 : p.hom ≫ q.hom = v.hom ≫ z.hom)
    (A3 : b.hom ≫ a.hom = v.hom ≫ w.hom)
    (UL : t.hom ≫ u.hom = 𝟙 T) (UR : b.hom ≫ d.hom = 𝟙 T) :
    q.inv ≫ r.hom ≫ s.inv ≫ u.hom = z.inv ≫ w.hom ≫ a.inv ≫ d.hom := by
  rw [← cancel_epi (p.hom ≫ q.hom)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% A1, Iso.hom_inv_id_assoc, UL, reassoc_of% A2,
    Iso.hom_inv_id_assoc, ← reassoc_of% A3, Iso.hom_inv_id_assoc, UR]

-- Native derived pullback types need the allowance used by their coherence laws.
/-- The two evaluations of a pulled-back constant family agree by associativity and units.
Source: base-change compatibility of normalized family constancy
(blueprint: lem-pur-native-section-pullback). -/
theorem section_commute {B B' P P' : Scheme.{u}} (b : B' ⟶ B)
    (a : P ⟶ B) (a' : P' ⟶ B') (f : P' ⟶ P) (i : B ⟶ P) (i' : B' ⟶ P')
    (hf : f ≫ a = a' ≫ b) (hi : i' ≫ f = b ≫ i)
    (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B))) :
    ((upperStar Λ i').leftDerivedFunctor).map
        ((compAlong Λ f a (f ≫ a) rfl).inv.app C ≫
          (compAlong Λ a' b (f ≫ a) hf.symm).hom.app C) ≫
        (sectionIso Λ i' a' h').hom.app _ =
      ((compAlong Λ i' f (i' ≫ f) rfl).inv.app _ ≫
          (compAlong Λ b i (i' ≫ f) hi.symm).hom.app _) ≫
        ((upperStar Λ b).leftDerivedFunctor).map ((sectionIso Λ i a h).hom.app C) := by
  have hb : i' ≫ f ≫ a = b := by rw [hf, ← Category.assoc, h', Category.id_comp]
  have A1 := (compAlong_assoc Λ i' a' b (𝟙 B') (f ≫ a) b h' hf.symm hb
    (Category.id_comp b) C).symm
  have A2 := (compAlong_assoc Λ i' f a (i' ≫ f) (f ≫ a) b rfl rfl hb
    (by rw [Category.assoc, hb]) C).symm
  have A3 := (compAlong_assoc Λ b i a (i' ≫ f) (𝟙 B) b hi.symm h
    (Category.comp_id b) (by rw [hi, Category.assoc, h, Category.comp_id]) C).symm
  have UL := compAlong_id_left Λ b C
  have UR := compAlong_id_right Λ b C
  have H := section_pasting
    ((compAlong Λ i' (f ≫ a) b hb).app C)
    (((upperStar Λ i').leftDerivedFunctor).mapIso
      ((compAlong Λ f a (f ≫ a) rfl).app C))
    (((upperStar Λ i').leftDerivedFunctor).mapIso
      ((compAlong Λ a' b (f ≫ a) hf.symm).app C))
    ((compAlong Λ i' a' (𝟙 B') h').app _)
    ((compAlong Λ (𝟙 B') b b (Category.id_comp b)).app C)
    ((leftDerivedUpperStarId Λ B').app _)
    ((compAlong Λ (i' ≫ f) a b (by rw [Category.assoc, hb])).app C)
    ((compAlong Λ i' f (i' ≫ f) rfl).app _)
    ((compAlong Λ b i (i' ≫ f) hi.symm).app _)
    (((upperStar Λ b).leftDerivedFunctor).mapIso ((compAlong Λ i a (𝟙 B) h).app C))
    ((compAlong Λ b (𝟙 B) b (Category.comp_id b)).app C)
    (((upperStar Λ b).leftDerivedFunctor).mapIso ((leftDerivedUpperStarId Λ B).app C))
    A1 A2 A3 UL UR
  simpa only [sectionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc] using H

section Reading

variable {B B' P P' : Scheme.{u}} (b : B' ⟶ B) {a : P ⟶ B} {a' : P' ⟶ B'}
  (f : P' ⟶ P) {i : B ⟶ P} {i' : B' ⟶ P'} (hi : i' ≫ f = b ≫ i)
  (h' : i' ≫ a' = 𝟙 B')
  {F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
    (condensedRingObj Λ P))}
  {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (condensedRingObj Λ B))}
  {C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B') Ab.{u + 1})
    (condensedRingObj Λ B'))}

/-- Read a constant presentation at a section using only pullback coherence.
Source: restriction of the normalized family comparison
(blueprint: lem-pur-native-section-pullback). -/
def readingIso (θ : ((upperStar Λ i).leftDerivedFunctor).obj F ≅ C)
    (e : ((upperStar Λ f).leftDerivedFunctor).obj F ≅
      ((upperStar Λ a').leftDerivedFunctor).obj C₀) :
    ((upperStar Λ b).leftDerivedFunctor).obj C ≅ C₀ :=
  (((compAlong Λ i' f (i' ≫ f) rfl).app F).symm ≪≫
      (compAlong Λ b i (i' ≫ f) hi.symm).app F ≪≫
        ((upperStar Λ b).leftDerivedFunctor).mapIso θ).symm ≪≫
    ((upperStar Λ i').leftDerivedFunctor).mapIso e ≪≫ (sectionIso Λ i' a' h').app C₀

/-- Changing the chosen fibre identification changes its reading contravariantly.
Source: the formal restriction calculation
(blueprint: lem-pur-native-section-pullback). -/
theorem readingIso_trans_left
    {C' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B))}
    (θ : ((upperStar Λ i).leftDerivedFunctor).obj F ≅ C) (ψ : C ≅ C')
    (e : ((upperStar Λ f).leftDerivedFunctor).obj F ≅
      ((upperStar Λ a').leftDerivedFunctor).obj C₀) :
    readingIso Λ b f hi h' (θ ≪≫ ψ) e =
      ((upperStar Λ b).leftDerivedFunctor).mapIso ψ.symm ≪≫
        readingIso Λ b f hi h' θ e := by
  ext
  simp [readingIso]

/-- Changing constant coordinates changes the reading by the same isomorphism.
Source: naturality of evaluation at a section
(blueprint: lem-pur-native-section-pullback). -/
theorem readingIso_trans_right
    {C₁ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B') Ab.{u + 1})
      (condensedRingObj Λ B'))}
    (θ : ((upperStar Λ i).leftDerivedFunctor).obj F ≅ C)
    (e : ((upperStar Λ f).leftDerivedFunctor).obj F ≅
      ((upperStar Λ a').leftDerivedFunctor).obj C₀) (χ : C₀ ≅ C₁) :
    readingIso Λ b f hi h' θ
        (e ≪≫ ((upperStar Λ a').leftDerivedFunctor).mapIso χ) =
      readingIso Λ b f hi h' θ e ≪≫ χ := by
  ext
  have H := (sectionIso Λ i' a' h').hom.naturality χ.hom
  simp only [Functor.comp_map, Functor.id_map] at H
  simp [readingIso, H]

private theorem reading_restrict_pasting {K : Type*} [Category K]
    {T T' X X' Y Y' Z Z' R : K}
    (p : T ≅ X) (q : T ≅ Y) (p' : T' ≅ X') (q' : T' ≅ Y')
    (k : X ≅ X') (l : Y ≅ Y') (m : T ⟶ T') (s : Y' ≅ R)
    (r : X' ⟶ Z) (t : Z ⟶ Z') (v : Z' ⟶ R)
    (n₁ : k.hom ≫ p'.inv = p.inv ≫ m)
    (n₂ : m ≫ q'.hom = q.hom ≫ l.hom)
    (H : r ≫ t ≫ v = p'.inv ≫ q'.hom ≫ s.hom) :
    s.inv ≫ l.inv ≫ q.inv ≫ p.hom ≫ k.hom ≫ r ≫ t ≫ v = 𝟙 R := by
  rw [H, reassoc_of% n₁, Iso.hom_inv_id_assoc, reassoc_of% n₂,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- A family comparison, restricted and then read at the same section, gives the identity.
Source: restriction of family constancy, using the compositor associativity and unit laws
(blueprint: lem-pur-native-section-pullback). -/
theorem readingIso_restrict (hf : f ≫ a = a' ≫ b) (h : i ≫ a = 𝟙 B)
    (κ : F ≅ ((upperStar Λ a).leftDerivedFunctor).obj C) :
    readingIso Λ b f hi h'
        (((upperStar Λ i).leftDerivedFunctor).mapIso κ ≪≫ (sectionIso Λ i a h).app C)
        (((upperStar Λ f).leftDerivedFunctor).mapIso κ ≪≫
          ((compAlong Λ f a (f ≫ a) rfl).app C).symm ≪≫
          (compAlong Λ a' b (f ≫ a) hf.symm).app C) = Iso.refl _ := by
  rw [readingIso]
  apply Iso.ext
  have n₁ := (compAlong Λ i' f (i' ≫ f) rfl).inv.naturality κ.hom
  have n₂ := (compAlong Λ b i (i' ≫ f) hi.symm).hom.naturality κ.hom
  simp only [Functor.comp_map] at n₁ n₂
  have H := section_commute Λ b a a' f i i' hf hi h h' C
  simp only [Functor.map_comp, Category.assoc] at H
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.refl_hom,
    Functor.map_comp, Category.assoc]
  exact reading_restrict_pasting
    ((compAlong Λ i' f (i' ≫ f) rfl).app F)
    ((compAlong Λ b i (i' ≫ f) hi.symm).app F)
    ((compAlong Λ i' f (i' ≫ f) rfl).app _)
    ((compAlong Λ b i (i' ≫ f) hi.symm).app _)
    (((upperStar Λ i').leftDerivedFunctor).mapIso
      (((upperStar Λ f).leftDerivedFunctor).mapIso κ))
    (((upperStar Λ b).leftDerivedFunctor).mapIso
      (((upperStar Λ i).leftDerivedFunctor).mapIso κ))
    (((upperStar Λ (i' ≫ f)).leftDerivedFunctor).map κ.hom)
    (((upperStar Λ b).leftDerivedFunctor).mapIso ((sectionIso Λ i a h).app C))
    _ _ _ n₁ n₂ H

end Reading

end AlgebraicGeometry.ProEtale.CondensedRing.NativeSectionPullback
