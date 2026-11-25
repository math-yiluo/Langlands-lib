/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Explicit vertices of an adjunction exchange

The three arrows are the actual unit insertion, square transport and counit contraction.
Their four endpoints are given directly, without identity or association functor wrappers.
(blueprint: def-weil-pbc-adjunction-exchange-chain)
-/

@[expose] public section

open CategoryTheory
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/-- A diagram of three arrows with its four vertices retained. -/
structure ExchangeChain (C : Type*) [Category C] where
  obj0 : C
  obj1 : C
  obj2 : C
  obj3 : C
  first : obj0 ⟶ obj1
  second : obj1 ⟶ obj2
  third : obj2 ⟶ obj3

namespace ExchangeChain

variable {C D : Type*} [Category C] [Category D]

/-- The composite of the three specified arrows. -/
def composite (s : ExchangeChain C) : s.obj0 ⟶ s.obj3 :=
  s.first ≫ s.second ≫ s.third

/-- Apply a functor to all four vertices and three arrows. -/
def map (s : ExchangeChain C) (F : C ⥤ D) : ExchangeChain D where
  obj0 := F.obj s.obj0
  obj1 := F.obj s.obj1
  obj2 := F.obj s.obj2
  obj3 := F.obj s.obj3
  first := F.map s.first
  second := F.map s.second
  third := F.map s.third

/-- A functor preserves the specified composite, with every endpoint fixed by the diagram. -/
theorem map_composite (s : ExchangeChain C) (F : C ⥤ D) :
    (s.map F).composite = F.map s.composite := by
  simp only [map, composite, Functor.map_comp]

/-- Map an endpoint arrow with the mapped diagram's endpoints retained in its type. -/
def mapHom (s : ExchangeChain C) (F : C ⥤ D) (η : s.obj0 ⟶ s.obj3) :
    (s.map F).obj0 ⟶ (s.map F).obj3 := F.map η

/-- A functor preserves the composite with endpoints fixed by the mapped diagram. -/
theorem mapHom_composite (s : ExchangeChain C) (F : C ⥤ D) :
    s.mapHom F s.composite = (s.map F).composite :=
  (map_composite s F).symm

end ExchangeChain

namespace CategoryTheory.Adjunction

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {U : C ⥤ D} {R : D ⥤ C} {V : E ⥤ F} {S : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}

/-- The three actual factors of a mate, with their nested endpoints displayed once. -/
def exchangeChain (a : U ⊣ R) (b : V ⊣ S) (θ : G ⋙ V ⟶ U ⋙ H) (K : D) :
    ExchangeChain E where
  obj0 := G.obj (R.obj K)
  obj1 := S.obj (V.obj (G.obj (R.obj K)))
  obj2 := S.obj (H.obj (U.obj (R.obj K)))
  obj3 := S.obj (H.obj K)
  first := b.unit.app (G.obj (R.obj K))
  second := S.map (θ.app (R.obj K))
  third := S.map (H.map (a.counit.app K))

set_option backward.defeqAttrib.useBackward true in
/-- The component of the actual adjunction mate is the composite of this diagram.
Source: Mathlib `mateEquiv`. Proof: expand the mate component and functor composition. -/
theorem mate_eq_exchangeChain_composite (a : U ⊣ R) (b : V ⊣ S)
    (θ : G ⋙ V ⟶ U ⋙ H) (K : D) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app K =
      (exchangeChain a b θ K).composite := by
  simp [mateEquiv, exchangeChain, ExchangeChain.composite]

end CategoryTheory.Adjunction
