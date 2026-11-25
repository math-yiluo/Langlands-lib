/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Directed monomorphic cocones that cover all stalks

Source: Stacks Project, Cohomology, Lemma 02UX, first paragraph.
(blueprint: lem-sc-abelian-sheaf-directed-stalk-colimit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace TopCat

/-- A directed cocone of subsheaves is a colimit if its maps jointly cover every stalk.

Source: Stacks Project, Cohomology, Lemma 02UX, the stalkwise colimit argument.
Proof: On each stalk, joint coverage gives surjectivity. For two elements with the same
image, choose a common stage by directedness. Its map to the target stalk is injective,
so the elements agree there. This recognizes a filtered colimit of underlying sets.
Stalks and the forgetful functor preserve the filtered colimit, so the comparison
from the sheaf colimit is an isomorphism on every stalk and hence an isomorphism.
(blueprint: lem-sc-abelian-sheaf-directed-stalk-colimit). -/
theorem abelianSheaf_directed_stalk_colimit
    (X : TopCat.{u}) (F : X.Sheaf AddCommGrpCat.{u})
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ X.Sheaf AddCommGrpCat.{u})
    (c : D ⟶ (Functor.const I).obj F)
    (hmono : ∀ i, Mono (c.app i))
    (hcover : ∀ (x : X) (t : Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x),
      ∃ (i : I) (s : Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj i).obj x),
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (c.app i).hom s = t) :
    Nonempty (IsColimit (Cocone.mk F c)) := by
  classical
  let C := Cocone.mk F c
  let m := (colimit.isColimit D).descCoconeMorphism C
  have hm : IsIso m.hom := by
    apply (Presheaf.isIso_iff_stalkFunctor_map_iso m.hom).2
    intro x
    let S := (Sheaf.forget AddCommGrpCat.{u} X ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} x) ⋙ CategoryTheory.forget AddCommGrpCat
    have ht : IsColimit (S.mapCocone C) := by
      apply Types.FilteredColimit.isColimitOf'
      · intro t
        obtain ⟨i, s, hs⟩ := hcover x t
        exact ⟨i, s, hs.symm⟩
      · intro i a b hab
        have hi : Mono ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (c.app i).hom) := (Presheaf.mono_iff_stalk_mono (c.app i)).1 (hmono i) x
        have he : a = b := (AddCommGrpCat.mono_iff_injective _).1 hi hab
        exact ⟨i, 𝟙 i, congrArg _ he⟩
    have hmS : IsIso (S.map m.hom) := by
      have hh := (isColimitOfPreserves S (colimit.isColimit D)).hom_isIso ht
        ((Cocone.functoriality D S).map m)
      exact (Cocone.forget (D ⋙ S)).map_isIso
        ((Cocone.functoriality D S).map m)
    change IsIso ((Sheaf.forget AddCommGrpCat.{u} X ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} x).map m.hom)
    have : IsIso ((CategoryTheory.forget AddCommGrpCat.{u}).map
        ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map m.hom.hom)) := hmS
    exact isIso_of_reflects_iso
      ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map m.hom.hom)
      (CategoryTheory.forget AddCommGrpCat)
  have : IsIso ((colimit.isColimit D).desc C) := hm
  exact ⟨IsColimit.ofPointIso (colimit.isColimit D) (t := C)⟩

end TopCat
