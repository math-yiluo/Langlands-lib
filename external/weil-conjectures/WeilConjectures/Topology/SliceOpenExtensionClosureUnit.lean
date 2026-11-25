/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Grp.Zero

/-! # The closed-support unit for the slice-site open extension

Source: Stacks Project, Cohomology, Proposition 02UZ, closure-support observation
(blueprint: lem-sc-slice-open-extension-closure-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Cohomology, Proposition 02UZ, first paragraph;
Sheaves, Lemmas 00A5 and 00AE.
(blueprint: lem-sc-slice-open-extension-closure-unit).

Proof: Write G for the displayed sheafification and i for the inclusion
of the closure of U. If x is outside U, every neighbourhood V of x
has no inclusion into U. Thus the direct sum defining the presheaf on V
is zero. Every presheaf stalk element is a germ of such a section, so
the presheaf stalk is zero. The sheafification unit is an isomorphism
on stalks, hence G has zero stalks outside U, in particular outside its closure.
Put F' = i inverse-image G. Outside
the closure both G and i pushforward F' have zero stalks (the latter by
the closed-pushforward stalk formula). On the closure, the stalk map of
the unit followed by the closed-pushforward germ comparison is the
inverse-image stalk isomorphism. This equality is checked on germs using
the inverse-image unit formula; germs generate the stalk. The unit is
therefore an isomorphism on every stalk. The stalkwise isomorphism
criterion for abelian sheaves makes it an isomorphism of sheaves. The
argument also covers U empty (G is zero) and dense U (i is an isomorphism).
No Noetherian assumption is needed. -/
theorem slice_open_extension_closure_unit_isIso
    (X : TopCat.{u}) (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥(closure (U : Set X)) ⟶ X)).unit.app
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((siteExtensionByZeroPresheaf U).obj (F.over U).obj))) := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (siteExtensionByZeroPresheaf U).obj (F.over U).obj
  let G : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P
  let i : TopCat.of ↥(closure (U : Set X)) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F' := (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj G
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G
  have hzero (x : X) (hx : x ∉ U) : IsZero (TopCat.Presheaf.stalk G.obj x) := by
    have hp : IsZero (P.stalk x) := by
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      suffices hh : ∀ t : P.stalk x, t = 0 from
        ⟨fun a b ↦ (hh a).trans (hh b).symm⟩
      intro t
      obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
      have : IsEmpty (V ⟶ U) := ⟨fun f ↦ hx (f.le hxV)⟩
      change DirectSum (V ⟶ U)
        (fun φ ↦ (F.over U).obj.obj (Opposite.op (Over.mk φ))) at s
      have hs : s = 0 := Subsingleton.elim _ _
      erw [hs]
      exact map_zero _
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{u} P
    exact hp.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))).symm
  have hc := closedPushforwardAbelianStalks (closure (U : Set X)) isClosed_closure F'
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso η).2
  intro x
  by_cases hx : x ∈ closure (U : Set X)
  · let z : TopCat.of ↥(closure (U : Set X)) := ⟨x, hx⟩
    obtain ⟨c, hcomp, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_ab i z
    have he : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z =
        (c.app G).hom := by
      apply TopCat.Presheaf.stalk_hom_ext G.obj
      intro V hxV
      rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
      change η.hom.app (Opposite.op V) ≫
        (TopCat.Presheaf.germ
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj F'.obj) V (i z) hxV ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z) = _
      rw [TopCat.Presheaf.stalkPushforward_germ]
      ext s
      exact (hcomp G V hxV s).symm
    have := hc.2.1 z
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (TopCat.Presheaf.stalkPushforward
      AddCommGrpCat.{u} i F'.obj z)
  · exact (hzero x (fun h ↦ hx (subset_closure h))).isIso (hc.1 x hx) _

end TopCat
