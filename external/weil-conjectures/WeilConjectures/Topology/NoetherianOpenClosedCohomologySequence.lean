/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Topology.SliceOpenClosedShortExact
import WeilConjectures.Topology.SliceOpenExtensionClosureUnit
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.Topology.InverseImageStalk

/-!
# The open-closed exact sequence on a Noetherian space

Source: Stacks Project, Modules, Lemma 02UT; Cohomology, Lemma 02UV and
Proposition 02UZ (blueprint: lem-sc-noetherian-open-closed-cohomology-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Modules, Lemma 02UT; Cohomology, Lemma 02UV and
Proposition 02UZ (blueprint: lem-sc-noetherian-open-closed-cohomology-sequence).

The first sheaf is the sheafification of the existing slice-site extension-by-zero
presheaf applied to `F.over U`. Opens of `U` are precisely opens of `X` contained
in `U`, so this is `j_!j^*F`. The displayed injection formula specifies the
canonical adjunction map: identity on the sole summand when `V ≤ U`, zero when
there is no such summand. The second map is the inverse-image adjunction unit
for the inclusion of the closed complement.

Proof: (1) On `U`, the first map is the identity on stalks and the last sheaf has
zero stalks, using lem-sc-topological-extension-by-zero-stalks and
lem-sc-closed-pushforward-abelian-stalks. (2) On the complement, the first stalk
is zero and the second map is the identity under the inverse-image and closed
pushforward stalk identifications, using lem-weil-pbc-topological-inverse-image-stalk.
(3) Apply lem-sc-abelian-sheaf-short-exact-stalkwise. (4) Outside the closure of
`U`, extension by zero has zero stalks. Its unit map to the closed pushforward
of its inverse image on that closure is an isomorphism on all stalks, hence an
isomorphism, using lem-weil-pbc-sets-sheaf-iso-on-stalks. (5) Apply
lem-sc-cohomology-closed-immersion-pushforward and transport along this isomorphism.
-/
theorem noetherian_open_closed_cohomology_sequence
    (X : TopCat.{u}) [NoetherianSpace X] (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ∃ a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((siteExtensionByZeroPresheaf U).obj (F.over U).obj) ⟶ F,
      (∀ (V : Opens X) (φ : V ⟶ U)
          (s : F.obj.obj (Opposite.op V)),
        (a.hom.app (Opposite.op V))
          ((toSheafify (Opens.grothendieckTopology X)
            ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)).app (Opposite.op V)
            (DirectSum.of (fun ψ : V ⟶ U ↦
              (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)) = s) ∧
      (∃ h : a ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F = 0,
        (ShortComplex.mk a
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
              TopCat.of ↥((U : Set X)ᶜ) ⟶ X)).unit.app F) h).ShortExact) ∧
      ∃ F' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ↥(closure (U : Set X))),
        Nonempty
          ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
              ((siteExtensionByZeroPresheaf U).obj (F.over U).obj) ≅
            (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
              (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
                TopCat.of ↥(closure (U : Set X)) ⟶ X)).obj F') ∧
        ∀ p : ℕ, Nonempty
          (@CategoryTheory.Sheaf.H' (Opens ↥(closure (U : Set X))) _
              (Opens.grothendieckTopology ↥(closure (U : Set X))) _
              (HasExt.standard _) F' p ⊤ ≅
            @CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
              (HasExt.standard _)
              ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
                ((siteExtensionByZeroPresheaf U).obj (F.over U).obj)) p ⊤) := by
  classical
  let P := (siteExtensionByZeroPresheaf U).obj (F.over U).obj
  let q : P ⟶ F.obj :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid fun _ : V.unop ⟶ U ↦ AddMonoidHom.id _)
      naturality := by
        intro V W f
        let : DecidableEq (V.unop ⟶ U) := Classical.decEq _
        let : DecidableEq (W.unop ⟶ U) := Classical.decEq _
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro φ s
        simp only [AddCommGrpCat.hom_comp, ConcreteCategory.hom_ofHom,
          AddMonoidHom.coe_comp, Function.comp_apply]
        erw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
          DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        rfl }
  let a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P ⟶ F :=
    ObjectProperty.homMk (sheafifyLift (Opens.grothendieckTopology X) q F.property)
  have ha : ∀ (V : Opens X) (φ : V ⟶ U) (s : F.obj.obj (Opposite.op V)),
      (a.hom.app (Opposite.op V))
        ((toSheafify (Opens.grothendieckTopology X) P).app (Opposite.op V)
          (DirectSum.of (fun ψ : V ⟶ U ↦
            (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)) = s := by
    intro V φ s
    have h := NatTrans.congr_app
      (toSheafify_sheafifyLift (Opens.grothendieckTopology X) q F.property)
      (Opposite.op V)
    have hs := ConcreteCategory.congr_hom h
      (DirectSum.of (fun ψ : V ⟶ U ↦
        (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)
    change (a.hom.app (Opposite.op V))
      ((toSheafify (Opens.grothendieckTopology X) P).app (Opposite.op V)
        (DirectSum.of (fun ψ : V ⟶ U ↦
          (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s)) =
        (q.app (Opposite.op V))
          (DirectSum.of (fun ψ : V ⟶ U ↦
            (F.over U).obj.obj (Opposite.op (Over.mk ψ))) φ s) at hs
    rw [hs]
    dsimp [q]
    exact DirectSum.toAddMonoid_of _ _ _
  refine ⟨a, ha, ?_, ?_⟩
  · exact slice_open_closed_short_exact X U F a ha
  · let i : TopCat.of ↥(closure (U : Set X)) ⟶ X :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let G := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P
    let F' := (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj G
    have hi : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction
        AddCommGrpCat.{u} i).unit.app G) := by
      exact slice_open_extension_closure_unit_isIso X U F
    let e : G ≅ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F' :=
      asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G)
    refine ⟨F', ⟨e⟩, fun p ↦ ?_⟩
    obtain ⟨c⟩ := cohomology_closed_immersion_pushforward i
      (Topology.IsClosedEmbedding.subtypeVal isClosed_closure) F' p
    exact ⟨c ≪≫ ((@CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens X) _ (Opens.grothendieckTopology X) _ (HasExt.standard _) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)).mapIso e.symm)⟩

end TopCat
