/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Topology.ModuleObjectOpenDescentAux

/-! # Effectivity of open-cover descent for sheaves of modules

Source: Stacks Project, Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Local module sheaves with compatible overlap isomorphisms descend to a global module.
Source: Stacks Project, Sheaves, Lemma 00AL (first proof) and Lemma 00AM.
(blueprint: lem-weil-pbc-module-object-open-descent).

Proof: First reduce the cover to a small subcover: for each point of X choose one
cover member containing it. This indexes a covering by a type in universe u, even
when the original index type lies in a larger universe. Retain the overlap maps
and cocycle on that subcover. On an open W, form the module of families of sections
of the local modules on W intersected with these cover members. Scalar action is
through restriction from O(W), and impose the equations that each overlap map sends
the restriction of one component to the restriction of the other. These equations
are linear, so compatible families form a submodule of the product. This product
and submodule lie in universe max u v. Restriction acts componentwise; naturality
of the overlap maps preserves compatibility, and functoriality and semilinearity
follow from those of the local modules.

For any open covering of W, glue each component with the corresponding local
sheaf axiom. On an overlap, both sides of the compatibility equation restrict to
the same section on every covering member. Separation of the local target sheaf
therefore proves compatibility of the glued family. Componentwise uniqueness gives
uniqueness of the family. Thus these modules and restrictions form a module sheaf H.

For every original index i and W contained in U i, transport the components of a
family by the overlap maps to Fi i on W intersected with the small cover. The
cocycle makes these sections compatible, so the sheaf axiom of Fi i glues them on W.
Conversely, from a section of Fi i on W, restriction followed by the overlap map
from i to each small-cover index gives a compatible family. The cocycle with all
three indices equal and invertibility imply that the diagonal overlap map is the
identity. It follows, using separation, that the two constructions are inverse.
They are linear and commute with restriction, by uniqueness of gluing; hence they
form an isomorphism H.over (U i) to Fi i. Finally, the cocycle identifies the two
routes from a component to Fi j on W contained in U i and U j. Separation on the
small covering of W gives the required compatibility of these isomorphisms. 
(blueprint: lem-weil-pbc-module-object-open-descent-diagonal)
-/
theorem diagonal_transition_identity
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I, (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (hcoc : ∀ (i j k : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j)
      (hk : W ≤ U k), (φij i k).hom.val.app (op (Over.mk
      (homOfLE (le_inf hi hk)))) = (φij i j).hom.val.app (op (Over.mk
      (homOfLE (le_inf hi hj)))) ≫ (φij j k).hom.val.app (op (Over.mk
      (homOfLE (le_inf hj hk))))) :
    ∀ (i : I) (W : Opens X) (hi : W ≤ U i),
      (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi)))) = 𝟙 _ := by
  intro i W hi
  let f := (φij i i).hom.val.app (op (Over.mk (homOfLE (le_inf hi hi))))
  let g := (φij i i).inv.val.app (op (Over.mk (homOfLE (le_inf hi hi))))
  have hgf : g ≫ f = 𝟙 _ := by
    have hh := congrArg (fun q => q.val.app (op (Over.mk (homOfLE (le_inf hi hi)))))
      (φij i i).inv_hom_id
    exact hh
  have hff : f = f ≫ f := hcoc i i i W hi hi hi
  have h := congrArg (fun q => g ≫ q) hff
  rw [← Category.assoc, hgf, Category.id_comp] at h
  exact h.symm

/-- (blueprint: lem-weil-pbc-module-object-open-descent) -/
theorem module_object_open_descent
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤) :
    ∀ (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
      (φij : ∀ i j : I,
        (SheafOfModules.overMap (moduleRings X) (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj
            (Fi i) ≅
          (SheafOfModules.overMap (moduleRings X)
            (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j)),
      (∀ (i j k : I) (W : Opens X)
        (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (φij i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (φij j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) →
      ∃ (H : SheafOfModules.{max u v} (moduleRings X))
        (φi : ∀ i : I, H.over (U i) ≅ Fi i),
        ∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
          (φi i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
            (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
              (φi j).hom.val.app (op (Over.mk (homOfLE hj))) := by
  intro Fi φij hcoc
  apply module_object_open_descent_aux X I U hcover Fi φij
    (diagonal_transition_identity X I U Fi φij hcoc) hcoc

end AlgebraicGeometry
