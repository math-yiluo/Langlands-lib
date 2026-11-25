/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Extensionality for binary operations on inverse-image sheaves

The local representatives used in Stacks Tags 008X and 0089 determine operations
commuting with restriction, independently of any module structure.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

local notation "P" A =>
  Functor.sheafPullbackConstruction.sheafPullback (Opens.map f) A
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
set_option quotPrecheck false in
local notation "η" A =>
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) A
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit

/-- Two binary operations with sheaf-valued output on inverse-image sections agree if
both commute with restriction and agree on pairs of unit images.
Source: Stacks Tags 008X (inverse image as sheafified presheaf inverse image), 007X
(local representatives in sheafification), and 0078 (separatedness of a sheaf).
Proof: near any point of an open, each of the two input sections comes from a
section of the presheaf inverse image, since sheafification is locally surjective.
The filtered colimit defining that presheaf is represented by a section on a
neighbourhood of the image point. Shrink the open around the original point and
intersect the two image neighbourhoods; restrict both representatives to this
intersection. The inputs on the smaller open are restrictions of unit images
from this single neighbourhood. The assumed unit equality, followed by the two
restriction laws, gives equality on this smaller open. These smaller opens cover
the original open, so separatedness of the output sheaf gives equality there.
On the empty open the output sheaf has exactly one section, so equality also holds.
No additivity or scalar action is assumed.
(blueprint: lem-pc-inverse-image-operation-ext). -/
theorem inverseImageOperation_ext
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (H : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (α β : ∀ U : (Opens X)ᵒᵖ,
      ((P CommRingCat.{u}).obj R).obj.obj U →
      ((P AddCommGrpCat.{u}).obj F).obj.obj U → H.obj.obj U)
    (hα : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) r m,
      H.obj.map i (α U r m) = α V
        (((P CommRingCat.{u}).obj R).obj.map i r)
        (((P AddCommGrpCat.{u}).obj F).obj.map i m))
    (hβ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) r m,
      H.obj.map i (β U r m) = β V
        (((P CommRingCat.{u}).obj R).obj.map i r)
        (((P AddCommGrpCat.{u}).obj F).obj.map i m))
    (hη : ∀ (V : (Opens Y)ᵒᵖ) (r : R.obj.obj V) (m : F.obj.obj V),
      α ((Opens.map f).op.obj V)
        (((η CommRingCat.{u}).app R).hom.app V r)
        (((η AddCommGrpCat.{u}).app F).hom.app V m) =
      β ((Opens.map f).op.obj V)
        (((η CommRingCat.{u}).app R).hom.app V r)
        (((η AddCommGrpCat.{u}).app F).hom.app V m)) :
    ∀ U r m, α U r m = β U r m := by
  intro U r m
  let J := Opens.grothendieckTopology X
  let R₀ := (Opens.map f).op.lan.obj R.obj
  let F₀ := (Opens.map f).op.lan.obj F.obj
  let θR := toSheafify J R₀
  let θF := toSheafify J F₀
  apply H.isSeparated U.unop (Presheaf.imageSieve θR r ⊓ Presheaf.imageSieve θF m)
  · exact J.intersection_covering (Presheaf.imageSieve_mem J θR r)
      (Presheaf.imageSieve_mem J θF m)
  · intro W i hi
    obtain ⟨r₀, hr₀⟩ := hi.1
    obtain ⟨m₀, hm₀⟩ := hi.2
    let CR := (Functor.LeftExtension.mk R₀ ((Opens.map f).op.lanUnit.app R.obj)).coconeAt
      (op W)
    let CF := (Functor.LeftExtension.mk F₀ ((Opens.map f).op.lanUnit.app F.obj)).coconeAt
      (op W)
    have hCR : IsColimit CR :=
      (Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit R.obj (op W)
    have hCF : IsColimit CF :=
      (Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op W)
    obtain ⟨a, x, hx⟩ := Concrete.isColimit_exists_rep _ hCR r₀
    obtain ⟨b, y, hy⟩ := Concrete.isColimit_exists_rep _ hCF m₀
    let c := IsFiltered.max a b
    let ac := IsFiltered.leftToMax a b
    let bc := IsFiltered.rightToMax a b
    have hx' : CR.ι.app c (R.obj.map ac.left x) = r₀ := by
      have hh := NatTrans.naturality_apply CR.ι ac x
      exact hh.trans hx
    have hy' : CF.ι.app c (F.obj.map bc.left y) = m₀ := by
      have hh := NatTrans.naturality_apply CF.ι bc y
      exact hh.trans hy
    rw [hα, hβ]
    change α (op W) ((sheafify J R₀).map i.op r) ((sheafify J F₀).map i.op m) =
      β (op W) ((sheafify J R₀).map i.op r) ((sheafify J F₀).map i.op m)
    rw [← hr₀, ← hm₀, ← hx', ← hy']
    have hcR (z : R.obj.obj c.left) :
        θR.app (op W) (CR.ι.app c z) =
          ((P CommRingCat.{u}).obj R).obj.map c.hom
            (((η CommRingCat.{u}).app R).hom.app c.left z) := by
      exact NatTrans.naturality_apply θR c.hom _
    have hcF (z : F.obj.obj c.left) :
        θF.app (op W) (CF.ι.app c z) =
          ((P AddCommGrpCat.{u}).obj F).obj.map c.hom
            (((η AddCommGrpCat.{u}).app F).hom.app c.left z) := by
      exact NatTrans.naturality_apply θF c.hom _
    rw [hcR, hcF]
    exact (hα c.hom _ _).symm.trans
      ((congrArg (H.obj.map c.hom) (hη c.left _ _)).trans (hβ c.hom _ _))

end
end TopCat.Sheaf
