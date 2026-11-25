/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of inverse images of sheaves of sets

Source: Stacks Project, Sheaves on Spaces, Lemma 6.21.6 (Tag 008I), with
Lemma 6.21.2 (Tag 008E).
(blueprint: lem-weil-pbc-sets-inverse-image-composition)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- Source: Stacks Project, Sheaves on Spaces, Lemma 6.21.6 (Tag 008I).
(blueprint: lem-weil-pbc-sets-inverse-image-composition)
Inverse images compose by a natural isomorphism whose component at each sheaf is the
unique sheaf morphism compatible with the adjunction units on every section.

Proof, following the node's five steps:
1. Direct images compose: their sections, restrictions and maps are evaluated on
   the same inverse-image opens (def-weil-pbc-topological-inverse-image (1), Tag 008E).
   In Lean use the canonical pushforward composition isomorphism.
2. Compose the adjunctions for g and f (def-weil-pbc-composite-adjunction and
   def-weil-pbc-topological-inverse-image (3)). The composite unit on a section is
   eta_f applied to eta_g, evaluated on the inverse image under g of the original open.
3. Equality of sheaf morphisms is sectionwise equality. Thus the displayed condition
   is precisely R(c) composed with the composite unit equals the unit for f followed by g.
4. Apply situation-conventions to the two adjunctions and the
   pushforward composition isomorphism. This gives a natural isomorphism satisfying
   the unit equation, hence the displayed section equation.
5. For any competing morphism at a fixed sheaf, situation-conventions
   for the composite adjunction recovers it from the same unit equation as counit
   composed with the inverse image of that equation's right-hand side. Therefore
   it equals the comparison component, even without any naturality assumption. -/
theorem exists_sets_inverseImage_comp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ e : pullback (Type u) g ⋙ pullback (Type u) f ≅ pullback (Type u) (f ≫ g),
      ∀ G : Z.Sheaf (Type u),
        (∀ (W : Opens Z) (s : G.obj.obj (op W)),
          (e.hom.app G).hom.app (op ((Opens.map (f ≫ g)).obj W))
            (((pullbackPushforwardAdjunction (Type u) f).unit.app
                ((pullback (Type u) g).obj G)).hom.app (op ((Opens.map g).obj W))
              (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app
                (op W) s)) =
            ((pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G).hom.app
              (op W) s) ∧
        (∀ c : (pullback (Type u) f).obj ((pullback (Type u) g).obj G) ⟶
            (pullback (Type u) (f ≫ g)).obj G,
          (∀ (W : Opens Z) (s : G.obj.obj (op W)),
            c.hom.app (op ((Opens.map (f ≫ g)).obj W))
              (((pullbackPushforwardAdjunction (Type u) f).unit.app
                  ((pullback (Type u) g).obj G)).hom.app (op ((Opens.map g).obj W))
                (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app
                  (op W) s)) =
              ((pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G).hom.app
                (op W) s) →
          c = e.hom.app G) := by
  let adj := (pullbackPushforwardAdjunction (Type u) g).comp
    (pullbackPushforwardAdjunction (Type u) f)
  let adj' : pullback (Type u) (f ≫ g) ⊣
      pushforward (Type u) f ⋙ pushforward (Type u) g :=
    pullbackPushforwardAdjunction (Type u) (f ≫ g)
  let e := adj.leftAdjointUniq adj'
  refine ⟨e, fun G ↦ ?_⟩
  have heq := adj.unit_leftAdjointUniq_hom_app adj' G
  constructor
  · intro W s
    rw [Adjunction.comp_unit_app] at heq
    exact congrArg (fun k ↦ k.hom.app (op W) s) heq
  · intro c hc
    apply (adj.homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, heq]
    apply CategoryTheory.Sheaf.hom_ext
    ext W s
    rw [Adjunction.comp_unit_app]
    exact hc W.unop s

end TopCat.Sheaf
