/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsStrictHenselization

/-!
# Strict henselization presentations in a universe containing the base ring

Source: Stacks Project, Algebra, Tag 04GW, pointed-algebra description
(blueprint: def-sc-ring-strict-henselization).

This is the recorded pointed-etale colimit presentation with independent base-ring and
algebra universes. The common algebra universe is at least the base-ring universe.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The forgetful diagram of pointed etale algebras in any universe containing the base.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
def strictHenselizationPointedDiagramIn (A : Type u) (K : Type (max u v))
    [CommRing A] [CommRing K] [Algebra A K] :
    (ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left)) ⥤
        CommAlgCat.{max u v} A :=
  ObjectProperty.ι (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left) ⋙
    Over.forget (CommAlgCat.of A K)

end Algebra
