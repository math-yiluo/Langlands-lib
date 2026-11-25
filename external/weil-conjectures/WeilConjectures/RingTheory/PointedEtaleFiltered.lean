/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Filteredness of pointed etale algebras

The proof constructs successors and equalizers directly by algebra pushouts.
Source: Stacks Project, Algebra, Tag 04GW, filteredness paragraphs
(blueprint: lem-sc-pointed-etale-filtered).
-/

@[expose] public section
universe u

open CategoryTheory

namespace Algebra

private lemma etale_pushout_inr {R : Type u} [CommRing R]
    {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : A ⟶ C)
    (hf : f.hom.toRingHom.Etale) :
    (Limits.pushout.inr f g).hom.toRingHom.Etale := by
  let F := forget₂ (CommAlgCat R) CommRingCat
  have : Limits.PreservesColimitsOfShape Limits.WalkingSpan F := by
    change Limits.PreservesColimitsOfShape Limits.WalkingSpan
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget _)
    infer_instance
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale)
    ((IsPushout.of_hasPushout f g).map F).flip hf

private lemma etale_pushout_inl {R : Type u} [CommRing R]
    {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : A ⟶ C)
    (hg : g.hom.toRingHom.Etale) :
    (Limits.pushout.inl f g).hom.toRingHom.Etale := by
  let F := forget₂ (CommAlgCat R) CommRingCat
  have : Limits.PreservesColimitsOfShape Limits.WalkingSpan F := by
    change Limits.PreservesColimitsOfShape Limits.WalkingSpan
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget _)
    infer_instance
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale)
    ((IsPushout.of_hasPushout f g).map F) hg

private lemma etale_of_map {R : Type u} [CommRing R]
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (hA : Etale R A) (hB : Etale R B) :
    f.hom.toRingHom.Etale := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun r ↦ (f.hom.commutes r).symm
  have := hA
  have := hB
  exact Etale.of_restrictScalars R A B

private lemma etale_comp_map {R : Type u} [CommRing R]
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (hA : Etale R A)
    (hf : f.hom.toRingHom.Etale) : Etale R B := by
  let : Algebra A B := f.hom.toRingHom.toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun r ↦ (f.hom.commutes r).symm
  have := hA
  have : Etale A B := hf
  exact Etale.comp R A B

/-- Filteredness follows from identity, tensor-product successors, and the iterated
 tensor equalizer construction of Stacks Tag 04GW.
Source: Stacks Project, Algebra, Tag 04GW.
(blueprint: lem-sc-pointed-etale-filtered). -/
theorem pointedEtale_filtered
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    IsFiltered P.FullSubcategory := by
  classical
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
  change IsFiltered P.FullSubcategory
  refine { nonempty := ?nonempty, cocone_objs := ?cocone_objs, cocone_maps := ?cocone_maps }
  case nonempty =>
    exact ⟨⟨Over.mk (CommAlgCat.ofHom (Algebra.ofId R K)),
      show Etale R R from inferInstance⟩⟩
  case cocone_objs =>
    intro s t
    let a : CommAlgCat.of R R ⟶ s.obj.left := CommAlgCat.ofHom (Algebra.ofId R _)
    let b : CommAlgCat.of R R ⟶ t.obj.left := CommAlgCat.ofHom (Algebra.ofId R _)
    let U := Limits.pushout a b
    have hab : a ≫ s.obj.hom = b ≫ t.obj.hom := by
      apply CommAlgCat.hom_ext
      exact Algebra.ext_id _ _ _
    let c : U ⟶ CommAlgCat.of R K := Limits.pushout.desc s.obj.hom t.obj.hom hab
    have hU : Etale R U := etale_comp_map (Limits.pushout.inr a b) t.property
      (etale_pushout_inr a b (etale_of_map a inferInstance s.property))
    let z : P.FullSubcategory := ⟨Over.mk c, hU⟩
    exact ⟨z, ObjectProperty.homMk (Over.homMk (Limits.pushout.inl a b)
      (Limits.pushout.inl_desc _ _ _)),
      ObjectProperty.homMk (Over.homMk (Limits.pushout.inr a b)
        (Limits.pushout.inr_desc _ _ _)), trivial⟩
  case cocone_maps =>
    intro s t f g
    let f₀ : s.obj.left ⟶ t.obj.left := f.hom.left
    let g₀ : s.obj.left ⟶ t.obj.left := g.hom.left
    let a : CommAlgCat.of R R ⟶ t.obj.left := CommAlgCat.ofHom (Algebra.ofId R _)
    let E := Limits.pushout f₀ g₀
    let T := Limits.pushout a a
    let l : t.obj.left ⟶ E := Limits.pushout.inl f₀ g₀
    let r : t.obj.left ⟶ E := Limits.pushout.inr f₀ g₀
    have hR : a ≫ l = a ≫ r := by
      apply CommAlgCat.hom_ext
      exact Algebra.ext_id _ _ _
    let m : T ⟶ E := Limits.pushout.desc l r hR
    let d : T ⟶ t.obj.left := Limits.pushout.desc (𝟙 _) (𝟙 _) (by simp)
    let U := Limits.pushout m d
    let k : E ⟶ U := Limits.pushout.inl m d
    let h : t.obj.left ⟶ U := Limits.pushout.inr m d
    have hl : l ≫ k = h := by
      have hw := congrArg (Limits.pushout.inl a a ≫ ·)
        (Limits.pushout.condition (f := m) (g := d))
      simpa only [Category.assoc, m, d, Limits.pushout.inl_desc_assoc,
        Category.id_comp] using hw
    have hr : r ≫ k = h := by
      have hw := congrArg (Limits.pushout.inr a a ≫ ·)
        (Limits.pushout.condition (f := m) (g := d))
      simpa only [Category.assoc, m, d, Limits.pushout.inr_desc_assoc,
        Category.id_comp] using hw
    have heq : f₀ ≫ h = g₀ ≫ h := by
      calc
        f₀ ≫ h = (f₀ ≫ l) ≫ k := by rw [Category.assoc, hl]
        _ = (g₀ ≫ r) ≫ k := congrArg (· ≫ k) Limits.pushout.condition
        _ = g₀ ≫ h := by rw [Category.assoc, hr]
    let e : E ⟶ CommAlgCat.of R K := Limits.pushout.desc t.obj.hom t.obj.hom
      ((Over.w f.hom).trans (Over.w g.hom).symm)
    have hmd : m ≫ e = d ≫ t.obj.hom := by
      apply Limits.pushout.hom_ext <;> simp [m, d, e, l, r]
    let c : U ⟶ CommAlgCat.of R K := Limits.pushout.desc e t.obj.hom hmd
    have hc : h ≫ c = t.obj.hom := Limits.pushout.inr_desc _ _ _
    have hret : r.hom.toRingHom.Etale :=
      etale_pushout_inr f₀ g₀ (etale_of_map f₀ s.property t.property)
    have hT : Etale R T := etale_comp_map (Limits.pushout.inr a a) t.property
      (etale_pushout_inr a a (etale_of_map a inferInstance t.property))
    have hdet : d.hom.toRingHom.Etale := etale_of_map d hT t.property
    have hket : k.hom.toRingHom.Etale := etale_pushout_inl m d hdet
    have hU : Etale R U := etale_comp_map k (etale_comp_map r t.property hret) hket
    let z : P.FullSubcategory := ⟨Over.mk c, hU⟩
    let h' : t ⟶ z := ObjectProperty.homMk (Over.homMk h hc)
    refine ⟨z, h', ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact heq

end Algebra
