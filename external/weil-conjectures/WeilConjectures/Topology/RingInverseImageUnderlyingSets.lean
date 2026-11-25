/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison

/-!
# Underlying sets of the inverse image of a ring sheaf

Source: Stacks Project, Sheaves, Tags 008F and 0087; Categories, Tag 04AX.
(blueprint: lem-a1-ring-inverse-image-underlying-sets)

The two comparisons are natural isomorphisms. The representative equation specifies
all neighbourhood-colimit coprojections, and the sheafification equation specifies
which sheaf isomorphism is induced by that presheaf comparison. We use the explicit
sheaf-pullback construction and its adjunction from the dependency's Mathlib match.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse image of commutative-ring sheaves commutes with underlying sets, including
its presheaf colimit representatives, sheafification maps and adjunction units.
Source: Stacks Project, Sheaves, Tags 008F and 0087, Section 008P; Categories, Tag 04AX.
(blueprint: lem-a1-ring-inverse-image-underlying-sets)

Proof plan:
1. For an open W the opens B with W ≤ h⁻¹B form a small nonempty filtered poset
   under reverse inclusion: the whole space is an object and intersections give
   common successors. This is the pointwise left-Kan-extension indexing category
   in def-weil-pbc-topological-inverse-image and def-weil-pbc-category-colimit.
2. The underlying ring-colimit coprojections induce beta. Surjectivity follows
   from lem-pc-filtered-colimit-commrings-elementwise (1). Its clause (2), followed
   by lem-weil-pbc-filtered-colimit-sets-elementwise (2), gives injectivity.
3. Restrictions and morphisms of ring sheaves send a representative (B,s) to the
   same representative or its image. Hence beta is a presheaf isomorphism natural
   in G. The representative equation below expresses its defining coprojections
   as the presheaf unit followed by restriction from h⁻¹B to W.
4. By lem-pc-sites-sheafification-underlying-sets, forgetting the ring
   sheafification gives a set sheafification. Its composite with beta does too.
   The universal property of def-weil-pbc-sheafification gives inverse sheaf maps
   alpha and delta, with alpha characterized by the sheafification equation below.
   Their composites are identities by uniqueness after the sheafification maps.
5. Precompose the naturality square for alpha with the sheafification unit. The
   defining equation and naturality of beta make it commute; uniqueness gives
   naturality of alpha itself.
6. The actual sheaf adjunction units are the presheaf units followed by the
   sheafification maps. Substitute the representative equation at W = h⁻¹B
   into the sheafification equation to obtain the displayed unit equation.
No step requires nonempty spaces, separation, compactness or surjectivity. -/
theorem ringInverseImage_underlyingSets {T Z : TopCat.{u}} (h : T ⟶ Z) :
    ∃ β :
      (sheafToPresheaf (Opens.grothendieckTopology Z) CommRingCat.{u} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{u}) ⋙
        TopCat.Presheaf.pullback (Type u) h) ≅
      (sheafToPresheaf (Opens.grothendieckTopology Z) CommRingCat.{u} ⋙
        TopCat.Presheaf.pullback CommRingCat.{u} h ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{u})),
    ∃ α :
      (sheafCompose (Opens.grothendieckTopology Z)
          (CategoryTheory.forget CommRingCat.{u}) ⋙
        Functor.sheafPullbackConstruction.sheafPullback (Opens.map h) (Type u)
          (Opens.grothendieckTopology Z) (Opens.grothendieckTopology T)) ≅
      (Functor.sheafPullbackConstruction.sheafPullback (Opens.map h) CommRingCat.{u}
          (Opens.grothendieckTopology Z) (Opens.grothendieckTopology T) ⋙
        sheafCompose (Opens.grothendieckTopology T)
          (CategoryTheory.forget CommRingCat.{u})),
      (∀ (G : Z.Sheaf CommRingCat.{u}) (W : Opens T) (B : Opens Z)
          (i : W ≤ (Opens.map h).obj B) (s : G.obj.obj (op B)),
        (β.hom.app G).app (op W)
          (((TopCat.Presheaf.pullback (Type u) h).obj
              (G.obj ⋙ CategoryTheory.forget CommRingCat.{u})).map (homOfLE i).op
            (((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) h).unit.app
              (G.obj ⋙ CategoryTheory.forget CommRingCat.{u})).app (op B) s)) =
        ((TopCat.Presheaf.pullback CommRingCat.{u} h).obj G.obj).map (homOfLE i).op
          (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} h).unit.app
            G.obj).app (op B) s)) ∧
      (∀ G : Z.Sheaf CommRingCat.{u},
        toSheafify (Opens.grothendieckTopology T)
            ((TopCat.Presheaf.pullback (Type u) h).obj
              (G.obj ⋙ CategoryTheory.forget CommRingCat.{u})) ≫ (α.hom.app G).hom =
        β.hom.app G ≫ Functor.whiskerRight
          (toSheafify (Opens.grothendieckTopology T)
            ((TopCat.Presheaf.pullback CommRingCat.{u} h).obj G.obj))
          (CategoryTheory.forget CommRingCat.{u})) ∧
      (∀ (G : Z.Sheaf CommRingCat.{u}) (B : Opens Z) (s : G.obj.obj (op B)),
        (α.hom.app G).hom.app (op ((Opens.map h).obj B))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map h) (Type u) (Opens.grothendieckTopology Z)
              (Opens.grothendieckTopology T)).unit.app
            ((sheafCompose (Opens.grothendieckTopology Z)
              (CategoryTheory.forget CommRingCat.{u})).obj G)).hom.app (op B) s) =
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map h) CommRingCat.{u} (Opens.grothendieckTopology Z)
          (Opens.grothendieckTopology T)).unit.app G).hom.app (op B) s) := by
  let U := CategoryTheory.forget CommRingCat.{u}
  let L := (Opens.map h).op
  let J := Opens.grothendieckTopology Z
  let K := Opens.grothendieckTopology T
  let (W : (Opens T)ᵒᵖ) : IsFiltered (CostructuredArrow L W) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (Opens.map h) (unop W))
  let β := Functor.isoWhiskerLeft (sheafToPresheaf J CommRingCat.{u})
    (U.lanCompIsoOfPreserves L).symm
  let α := (sheafPullbackForgetIso J K (Opens.map h) U).symm
  refine ⟨β, α, ?_, ?_, ?_⟩
  · intro G W B i s
    have hn := (β.hom.app G).naturality (homOfLE i).op
    have hu := U.leftKanExtensionCompIsoOfPreserves_inv_fac_app G.obj L (op B)
    have hn' := ConcreteCategory.congr_hom hn
      (((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) h).unit.app
        (G.obj ⋙ U)).app (op B) s)
    have hu' := ConcreteCategory.congr_hom hu s
    exact hn'.trans (congrArg
      (fun x ↦ ((TopCat.Presheaf.pullback CommRingCat.{u} h).obj G.obj).map
        (homOfLE i).op x) hu')
  · intro G
    change toSheafify K (L.lan.obj (G.obj ⋙ U)) ≫
      (sheafifyMap K (U.leftKanExtensionCompIsoOfPreserves G.obj L).inv ≫
        (sheafifyComposeIso K U (L.lan.obj G.obj)).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    erw [sheafComposeIso_hom_fac]
    rfl
  · intro G B s
    have hu := sheafPullbackForgetIso_unit J K (Opens.map h) U G
    have hu' := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg ((sheafToPresheaf J (Type u)).map) hu) (op B)) s
    have hi := ConcreteCategory.congr_hom
      (NatTrans.congr_app
        (congrArg ((sheafToPresheaf K (Type u)).map) (α.inv_hom_id_app G))
        (op ((Opens.map h).obj B)))
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map h) CommRingCat.{u} J K).unit.app G).hom.app (op B) s)
    exact (congrArg ((α.hom.app G).hom.app (op ((Opens.map h).obj B))) hu').symm.trans hi

end TopCat.Sheaf
