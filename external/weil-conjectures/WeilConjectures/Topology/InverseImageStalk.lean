/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of topological inverse images

Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P
(blueprint: lem-weil-pbc-topological-inverse-image-stalk).

The two statements give the natural stalk isomorphism, its formula on germs using
the sheaf-adjunction unit, and representation of every inverse-image stalk element.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

noncomputable section

open CategoryTheory.Limits

section General

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type*) [Category.{u} A]
variable {FA : A → A → Type*} {CA : A → Type u}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)

private def inverseImageStalkMap (G : Y.Sheaf A) :
    Presheaf.stalk G.obj (f x) ⟶ Presheaf.stalk ((pullback A f).obj G).obj x :=
  (Presheaf.stalkFunctor A (f x)).map
      ((pullbackPushforwardAdjunction A f).unit.app G).hom ≫
    Presheaf.stalkPushforward A f ((pullback A f).obj G).obj x

@[reassoc]
private theorem inverseImageStalkMap_germ (G : Y.Sheaf A)
    (V : Opens Y) (hV : f x ∈ V) :
    Presheaf.germ G.obj V (f x) hV ≫ inverseImageStalkMap A f x G =
      (((pullbackPushforwardAdjunction A f).unit.app G).hom.app (op V)) ≫
        Presheaf.germ ((pullback A f).obj G).obj ((Opens.map f).obj V) x hV := by
  simp [inverseImageStalkMap]

private theorem inverseImageStalkMap_isIso (G : Y.Sheaf A) :
    IsIso (inverseImageStalkMap A f x G) := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    A (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let e := Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction A f) adj
  let k := Presheaf.stalkPullbackHom A f G.obj x ≫
    (Presheaf.stalkFunctor A x).map
      (toSheafify (Opens.grothendieckTopology X) ((Presheaf.pullback A f).obj G.obj))
  have : IsIso (Presheaf.stalkPullbackHom A f G.obj x) :=
    (Presheaf.stalkPullbackIso A f G.obj x).isIso_hom
  have := Presheaf.stalkFunctor_map_unit_toSheafify_isIso x A
    ((Presheaf.pullback A f).obj G.obj)
  have hk : IsIso k := inferInstance
  have he : IsIso ((Presheaf.stalkFunctor A x).map (e.hom.app G).hom) :=
    inferInstance
  have hcomp : inverseImageStalkMap A f x G ≫
      (Presheaf.stalkFunctor A x).map (e.hom.app G).hom = k := by
    apply Presheaf.stalk_hom_ext
    intro V hV
    rw [inverseImageStalkMap_germ_assoc, Presheaf.stalkFunctor_map_germ]
    dsimp [k]
    rw [Presheaf.germ_stalkPullbackHom_assoc, Presheaf.stalkFunctor_map_germ]
    rw [← Category.assoc]
    have hu := Adjunction.unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction A f) adj G
    have huV := congrArg (fun q ↦ q.hom.app (op V)) hu
    change (((pullbackPushforwardAdjunction A f).unit.app G).hom.app (op V) ≫
      (e.hom.app G).hom.app (op ((Opens.map f).obj V))) =
      (adj.unit.app G).hom.app (op V) at huV
    have hu0 : (adj.unit.app G).hom.app (op V) =
        ((Presheaf.pullbackPushforwardAdjunction A f).unit.app G.obj).app (op V) ≫
          (toSheafify (Opens.grothendieckTopology X)
            ((Presheaf.pullback A f).obj G.obj)).app (op ((Opens.map f).obj V)) := by
      change ((sheafToPresheaf (Opens.grothendieckTopology Y) A).map
        (adj.unit.app G)).app (op V) = _
      dsimp only [adj, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      simp [Adjunction.comp_unit_app, Presheaf.pullbackPushforwardAdjunction,
        Presheaf.pullback]
    rw [hu0] at huV
    rw [huV, Category.assoc]
    rfl
  rw [← hcomp] at hk
  exact IsIso.of_isIso_comp_right (inverseImageStalkMap A f x G)
    ((Presheaf.stalkFunctor A x).map (e.hom.app G).hom)

private def inverseImageStalkIso :
    (forget A Y ⋙ Presheaf.stalkFunctor A (f x)) ≅
      (pullback A f ⋙ forget A X ⋙ Presheaf.stalkFunctor A x) := by
  have (G : Y.Sheaf A) : IsIso (inverseImageStalkMap A f x G) :=
    inverseImageStalkMap_isIso A f x G
  refine NatIso.ofComponents (fun G ↦ asIso (inverseImageStalkMap A f x G)) ?_
  intro G H q
  apply Presheaf.stalk_hom_ext
  intro V hV
  dsimp [forget]
  rw [Presheaf.stalkFunctor_map_germ_assoc, inverseImageStalkMap_germ,
    inverseImageStalkMap_germ_assoc, Presheaf.stalkFunctor_map_germ]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun r ↦ r.hom.app (op V) ≫
    Presheaf.germ ((pullback A f).obj H).obj ((Opens.map f).obj V) x hV)
      ((pullbackPushforwardAdjunction A f).unit.naturality q)

end General

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Stalks of the inverse image for sheaves of abelian groups, naturally in the sheaf.
Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P.
(blueprint: lem-weil-pbc-topological-inverse-image-stalk)

Proof route from the node:
0. Identify the inverse image with the sheafification of the presheaf inverse image
   (def-weil-pbc-topological-inverse-image); the unit is the presheaf unit followed
   by the sheafification map.
1. Apply lem-weil-pbc-presheaf-inverse-image-stalk to identify the presheaf stalks,
   with its germ formula.
2. Apply lem-weil-pbc-stalk-sheafification-space in the abelian case, or
   lem-weil-pbc-ring-stalk-sheafification-space in the ring case, to the
   sheafification map.
3. Compose these isomorphisms. Their germ formulas give the displayed unit formula.
4. Represent an original stalk element by a germ (def-weil-pbc-module-stalk,
   and lem-weil-pbc-filtered-colimit-algebras-elementwise for rings). Surjectivity
   of the composite gives the final clause.
5. Naturality of the unit gives naturality on germs; since germs exhaust stalks,
   this gives naturality of the isomorphism.
-/
theorem exists_inverseImage_stalk_iso_ab {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    ∃ c : (forget AddCommGrpCat.{u} Y ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)) ≅
        (pullback AddCommGrpCat.{u} f ⋙ forget AddCommGrpCat.{u} X ⋙
          Presheaf.stalkFunctor AddCommGrpCat.{u} x),
      (∀ (G : Y.Sheaf AddCommGrpCat.{u}) (V : Opens Y) (hV : f x ∈ V)
          (s : G.obj.obj (op V)),
        (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) =
          Presheaf.germ ((pullback AddCommGrpCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G).hom.app (op V)) s)) ∧
      (∀ (G : Y.Sheaf AddCommGrpCat.{u})
          (t : Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
            ((pullback AddCommGrpCat.{u} f).obj G).obj x),
        ∃ (V : Opens Y) (hV : f x ∈ V) (s : G.obj.obj (op V)),
          Presheaf.germ ((pullback AddCommGrpCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G).hom.app
              (op V)) s) = t) := by
  let c := inverseImageStalkIso AddCommGrpCat.{u} f x
  refine ⟨c, ?_, ?_⟩
  · intro G V hV s
    exact ConcreteCategory.congr_hom
      (inverseImageStalkMap_germ AddCommGrpCat.{u} f x G V hV) s
  · intro G t
    obtain ⟨V, hV, s, hs⟩ := Presheaf.exists_germ_eq G.obj ((c.app G).inv t)
    refine ⟨V, hV, s, ?_⟩
    have hg := ConcreteCategory.congr_hom
      (inverseImageStalkMap_germ AddCommGrpCat.{u} f x G V hV) s
    change (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) = _ at hg
    simp only [ConcreteCategory.comp_apply] at hg
    erw [← hg, hs]
    exact ConcreteCategory.congr_hom (c.app G).inv_hom_id t

/-- Stalks of the inverse image for sheaves of commutative rings, naturally in the sheaf.
Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P.
(blueprint: lem-weil-pbc-topological-inverse-image-stalk)

Proof route from the node:
0. Identify the inverse image with the sheafification of the presheaf inverse image
   (def-weil-pbc-topological-inverse-image); the unit is the presheaf unit followed
   by the sheafification map.
1. Apply lem-weil-pbc-presheaf-inverse-image-stalk to identify the presheaf stalks,
   with its germ formula.
2. Apply lem-weil-pbc-stalk-sheafification-space in the abelian case, or
   lem-weil-pbc-ring-stalk-sheafification-space in the ring case, to the
   sheafification map.
3. Compose these isomorphisms. Their germ formulas give the displayed unit formula.
4. Represent an original stalk element by a germ (def-weil-pbc-module-stalk,
   and lem-weil-pbc-filtered-colimit-algebras-elementwise for rings). Surjectivity
   of the composite gives the final clause.
5. Naturality of the unit gives naturality on germs; since germs exhaust stalks,
   this gives naturality of the isomorphism.
-/
theorem exists_inverseImage_stalk_iso_commRing {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    ∃ c : (forget CommRingCat.{u} Y ⋙ Presheaf.stalkFunctor CommRingCat.{u} (f x)) ≅
        (pullback CommRingCat.{u} f ⋙ forget CommRingCat.{u} X ⋙
          Presheaf.stalkFunctor CommRingCat.{u} x),
      (∀ (G : Y.Sheaf CommRingCat.{u}) (V : Opens Y) (hV : f x ∈ V)
          (s : G.obj.obj (op V)),
        (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) =
          Presheaf.germ ((pullback CommRingCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app G).hom.app (op V)) s)) ∧
      (∀ (G : Y.Sheaf CommRingCat.{u})
          (t : Presheaf.stalk (C := CommRingCat.{u}) (X := X)
            ((pullback CommRingCat.{u} f).obj G).obj x),
        ∃ (V : Opens Y) (hV : f x ∈ V) (s : G.obj.obj (op V)),
          Presheaf.germ ((pullback CommRingCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app G).hom.app
              (op V)) s) = t) := by
  let c := inverseImageStalkIso CommRingCat.{u} f x
  refine ⟨c, ?_, ?_⟩
  · intro G V hV s
    exact ConcreteCategory.congr_hom
      (inverseImageStalkMap_germ CommRingCat.{u} f x G V hV) s
  · intro G t
    obtain ⟨V, hV, s, hs⟩ := Presheaf.exists_germ_eq G.obj ((c.app G).inv t)
    refine ⟨V, hV, s, ?_⟩
    have hg := ConcreteCategory.congr_hom
      (inverseImageStalkMap_germ CommRingCat.{u} f x G V hV) s
    change (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) = _ at hg
    simp only [ConcreteCategory.comp_apply] at hg
    erw [← hg, hs]
    exact ConcreteCategory.congr_hom (c.app G).inv_hom_id t

end

end TopCat.Sheaf
