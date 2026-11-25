/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import all WeilConjectures.Topology.ConstantSubsheafStalkBound
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks

/-! # Integer coordinates for extension by zero

Source: Stacks Project, Cohomology, Lemma 0A38
(blueprint: lem-sc-abelian-open-extension-integer-germ-coordinates).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Source: Stacks Project, Sheaves, Lemma 00A5; Cohomology, Lemma 0A38.
Proof: The canonical extension-by-zero stalk comparison on U carries the displayed
unit germ to the unit germ of the constant integer sheaf. Sheafification preserves
stalks. The constant presheaf has integer stalk: every germ is represented by an
integer and restriction maps are identities, so equality of germs is equality of
integers. The neighborhood system at x is nonempty and filtered. Thus multiplication
of the unit germ by z gives a bijection from the integers to this stalk. The germ
comparison for any V contained in U is the same one by restriction compatibility.
The hypothesis x in V excludes empty V and empty U.
(blueprint: lem-sc-abelian-open-extension-integer-germ-coordinates). -/
theorem abelianOpenExtension_integer_germ_coordinates
    (X : TopCat.{u}) (U V : Opens X) (hV : V ≤ U) (x : X) (hx : x ∈ V) :
    let E := (abelianOpenExtensionByZero U).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    let unit := abelianOpenExtensionSection U
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) V hV
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map U.inclusion').obj V)) (ULift.up 1))
    ∀ t : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) E.obj x),
      ∃! z : ℤ, z • (TopCat.Presheaf.germ E.obj V x hx unit) = t := by
  classical
  intro E unit
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let G := (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    AddCommGrpCat.{u}).obj Z
  let xi : U := ⟨x, hV hx⟩
  obtain ⟨eG, heG⟩ := constantSubsheaf_canonical_stalks ((Opens.toTopCat X).obj U) Z
  obtain ⟨eE, heE, _, _, _⟩ := abelianOpenExtensionByZero_stalks X U
  let e : Z ≅ TopCat.Presheaf.stalk E.obj x := (eG xi).symm.trans (eE xi G)
  have hunit : (eG xi).inv =
      (toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj Z)).app
        (op ((Opens.map U.inclusion').obj V)) ≫
      TopCat.Presheaf.germ G.obj ((Opens.map U.inclusion').obj V) xi hx := by
    apply (cancel_mono (eG xi).hom).mp
    rw [Iso.inv_hom_id]
    exact (heG xi ((Opens.map U.inclusion').obj V) hx).symm
  have he : e.hom (ULift.up 1) = TopCat.Presheaf.germ E.obj V x hx unit := by
    have hh := heE xi G V hV hx
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [hunit, Category.assoc, hh]
    rfl
  have hz (z : ℤ) : e.hom (ULift.up z) =
      z • (TopCat.Presheaf.germ E.obj V x hx unit) := by
    rw [← he]
    have hu : (ULift.up z : ULift.{u} ℤ) = z • (ULift.up 1 : ULift.{u} ℤ) := by
      apply ULift.ext
      simp
    rw [hu]
    exact map_zsmul e.hom.hom z (ULift.up 1)
  intro t
  refine ⟨(e.inv t).down, ?_, ?_⟩
  · change ((e.inv t).down : ℤ) • (TopCat.Presheaf.germ E.obj V x hx) unit = t
    rw [← hz]
    exact e.inv_hom_id_apply t
  · intro z hzt
    have hzt' : e.hom (ULift.up z) = t := (hz z).trans hzt
    have hh := congrArg (fun v ↦ e.inv v) hzt'
    have hh' : (ULift.up z : ULift.{u} ℤ) = e.inv t := by
      rw [← ConcreteCategory.comp_apply, e.hom_inv_id] at hh
      simpa using hh
    exact congrArg ULift.down hh'


end TopCat.Sheaf
