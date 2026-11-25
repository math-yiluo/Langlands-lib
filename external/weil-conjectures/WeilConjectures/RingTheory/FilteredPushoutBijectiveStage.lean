/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Filtered.Final

/-! # Bijectivity at a stage of a filtered system of pushout ring maps -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CommRingCat

/-- A finitely presented map in a cartesian system of rings is bijective at a stage
if its colimit map is bijective.

Source: Stacks Project, Algebra, Tag 05N9 (2), (3), as used in Tag 02JO (3).
(blueprint: lem-weil-pbc-filtered-pushout-bijective-stage)

Proof: choose an object i. Its target is finitely presented over its source.
Restrict to objects equipped with an arrow from i; this filtered category is cofinal.
Whisker both colimit cocones along this final forgetful functor. The structure
maps from the source at i make the restricted diagrams algebras over that ring.
The inverse of the colimit map, restricted to the target at i, is an algebra map.
Factor it through a source stage using finite presentation, Tag 05N9 (2). The composite
on the target at i agrees with its transition map at the colimit. Finite generation
of that target over the source
and Tag 05N9 (3) make them agree at a later stage l. The pushout property at
i → l extends the inverse candidate and the identity of the source at l to a
map from the target at l to the source at l. One inverse identity is its
restriction to the source leg. For the other, check the source and target legs
of the pushout; on the target leg use the eventual equality just obtained.
The two identities give bijectivity there. Empty presentations and zero rings
require no separate argument; nonemptiness follows from filteredness.
-/
theorem exists_bijective_stage_of_filtered_pushouts
    {J : Type v} [SmallCategory J] [IsFiltered J] [UnivLE.{v, u}]
    (D E : J ⥤ CommRingCat.{u}) (α : D ⟶ E)
    (cD : Cocone D) (cE : Cocone E) (hD : IsColimit cD) (hE : IsColimit cE)
    (f : cD.pt ⟶ cE.pt)
    (hf : ∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f)
    (hbij : Function.Bijective f)
    (hfp : ∀ j, (α.app j).hom.FinitePresentation)
    (hpush : ∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
      (E.map r) (α.app k)) :
    ∃ j, Function.Bijective (α.app j) := by
  classical
  let : PreservesFilteredColimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE (forget CommRingCat.{u})
  let i : J := Classical.choice IsFiltered.nonempty
  let U := Under.forget i
  let D' := U ⋙ D
  let E' := U ⋙ E
  let cD' := cD.whisker U
  let cE' := cE.whisker U
  have hD' : IsColimit cD' := (Functor.Final.isColimitWhiskerEquiv U cD).symm hD
  have hE' : IsColimit cE' := (Functor.Final.isColimitWhiskerEquiv U cE).symm hE
  let β : (Functor.const (Under i)).obj (D.obj i) ⟶ D' :=
    { app j := D.map j.hom
      naturality := fun j k r ↦ by
        change 𝟙 _ ≫ D.map k.hom = D.map j.hom ≫ D.map r.right
        rw [Category.id_comp, ← D.map_comp, Under.w r] }
  let γ : (Functor.const (Under i)).obj (D.obj i) ⟶ E' :=
    { app j := α.app i ≫ E.map j.hom
      naturality := fun j k r ↦ by
        change 𝟙 _ ≫ (α.app i ≫ E.map k.hom) =
          (α.app i ≫ E.map j.hom) ≫ E.map r.right
        rw [Category.id_comp, Category.assoc, ← E.map_comp, Under.w r] }
  let ef := RingEquiv.ofBijective f.hom hbij
  let g : cE.pt ⟶ cD.pt := CommRingCat.ofHom ef.symm.toRingHom
  have hfg : f ≫ g = 𝟙 _ := by ext x; exact ef.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 _ := by ext x; exact ef.apply_symm_apply x
  obtain ⟨k, a, ha, hac⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (D.obj i) D' β (α.app i) cD' hD' (hfp i) (cE.ι.app i ≫ g) (by
        intro j
        change α.app i ≫ cE.ι.app i ≫ g = D.map j.hom ≫ cD.ι.app j.right
        rw [← Category.assoc, hf i, Category.assoc, hfg]
        simp [cD.w j.hom])
  have hca : a ≫ cD.ι.app k.right = cE.ι.app i ≫ g := hac.symm
  have hlimit : (a ≫ α.app k.right) ≫ cE.ι.app k.right =
      E.map k.hom ≫ cE.ι.app k.right := by
    rw [Category.assoc, hf k.right, ← Category.assoc, hca,
      Category.assoc, hgf]
    simp [cE.w k.hom]
  obtain ⟨l, r, s, hrs⟩ :=
    RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
      (D.obj i) E' γ (α.app i) cE' hE'
      (RingHom.FiniteType.of_finitePresentation (hfp i)).essFiniteType
      (a ≫ α.app k.right) (by
        change α.app i ≫ a ≫ α.app k.right = α.app i ≫ E.map k.hom
        rw [← Category.assoc, ha]
        exact α.naturality k.hom)
      (E.map k.hom) rfl hlimit
  let b : E.obj i ⟶ D.obj l.right := a ≫ D.map r.right
  have hb : α.app i ≫ b = D.map l.hom := by
    dsimp [b]
    rw [← Category.assoc, ha]
    change D.map k.hom ≫ D.map r.right = D.map l.hom
    rw [← D.map_comp, Under.w r]
  have hba : b ≫ α.app l.right = E.map l.hom := by
    dsimp [b]
    rw [Category.assoc, α.naturality r.right, ← Category.assoc]
    have hrs' : (a ≫ α.app k.right) ≫ E.map r.right =
        E.map k.hom ≫ E.map s.right := hrs
    rw [hrs']
    rw [← E.map_comp, Under.w s]
  let hp := hpush l.hom
  let inv : E.obj l.right ⟶ D.obj l.right := hp.desc b (𝟙 _) (by simpa using hb)
  have hleft : α.app l.right ≫ inv = 𝟙 _ := hp.inr_desc _ _ _
  have hright : inv ≫ α.app l.right = 𝟙 _ := by
    apply hp.hom_ext
    · rw [← Category.assoc, hp.inl_desc]
      simpa using hba
    · rw [← Category.assoc, hleft]
      simp
  refine ⟨l.right, ?_⟩
  constructor
  · intro x y hxy
    have hx := congrArg (fun z ↦ inv z) hxy
    have h := congrArg (fun m : D.obj l.right ⟶ D.obj l.right ↦ m x) hleft
    have h' := congrArg (fun m : D.obj l.right ⟶ D.obj l.right ↦ m y) hleft
    exact h.symm.trans (hx.trans h')
  · intro y
    refine ⟨inv y, ?_⟩
    exact congrArg (fun m : E.obj l.right ⟶ E.obj l.right ↦ m y) hright

end CommRingCat
