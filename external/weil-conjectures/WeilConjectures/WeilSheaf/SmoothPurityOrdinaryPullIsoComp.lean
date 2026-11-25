/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceProof

/-! # Ordinary coefficient pullback composition without the nonflat derived cube

This is the ordinary composition proof from `NonFlatPullCoherence`, isolated so
ordinary Tate comparisons do not import the derived exceptional-functor theory.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The underived (Pull) isomorphisms `pullIso a` are compatible with the composition
isomorphisms `(f ≫ g)^* ≅ g^* ⋙ f^*`: they are the conjugates of the isomorphisms
`comapLowerStarIso a`, which are compatible with the composition isomorphisms of
pushforwards. -/
lemma purity_pullIso_hom_app_comp
    (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (pullIso a (f ≫ g)).hom.app M ≫
        (upperStarComp Λ' f g).hom.app ((Mod.extendScalars (coefficientMap a Z)).obj M) =
      (Mod.extendScalars (coefficientMap a X)).map ((upperStarComp Λ f g).hom.app M) ≫
        (pullIso a f).hom.app ((g)^*⟦Λ⟧.obj M) ≫
          (f)^*⟦Λ'⟧.map ((pullIso a g).hom.app M) :=
  Adjunction.pullIsoOfComapIso_hom_app_comp
    (adj_f := upperStarLowerStarAdjunction Λ f) (adj_g := upperStarLowerStarAdjunction Λ g)
    (adj_fg := upperStarLowerStarAdjunction Λ (f ≫ g))
    (adj'_f := upperStarLowerStarAdjunction Λ' f) (adj'_g := upperStarLowerStarAdjunction Λ' g)
    (adj'_fg := upperStarLowerStarAdjunction Λ' (f ≫ g))
    (c := upperStarComp Λ f g) (c' := upperStarComp Λ' f g)
    (h := fun N ↦ by
      simp only [conjugateIsoEquiv_apply_hom, conjugateEquiv_upperStarComp_hom_eq_lowerStarComp]
      exact comapLowerStarIso_hom_app_lowerStarComp Λ f g a N) (M := M) ..

end AlgebraicGeometry.ProEtale.CondensedRing
