/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!

# The exchange formalism of bounded constructible complexes

The derived pullbacks `Lf^*`, the derived pushforwards `Rf_*` and the extensions by zero `j_!`
on the bounded constructible derived categories `Dᵇc(X)⟦Λ⟧` of separated `k`-schemes of finite
type (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`) form a
`CategoryTheory.ExchangeFormalism`, indexed by the full subcategory
`AlgebraicGeometry.SepFinType k` of `Over (Spec k)` with the open immersions as class of
morphisms (`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`). The pseudofunctor
laws are `boundedConstructibleUpperStarComp_assoc_app` and the unit laws of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback`.

The formal coherence results of `CategoryTheory.ExchangeFormalism` (pasting, identity and cube
laws of the base change and exchange maps) then apply to the bounded constructible functors.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`: the exchange formalism of
  bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme


variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **The exchange formalism of bounded constructible complexes**: the bounded constructible
derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of the separated `k`-schemes of finite type, with the derived
pullbacks `Lf^*` (`boundedConstructibleUpperStar`), their composition and identity isomorphisms,
the derived pushforwards `Rf_*` and the extensions by zero `j_!` along open immersions. -/
noncomputable def boundedConstructibleExchangeFormalism :
    ExchangeFormalism (SepFinType k) SepFinType.openImmersion where
  obj X := Dᵇc(X.obj.left)⟦Profinite.padicAlgClRingObj ℓ⟧
  pb f := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f.hom
  pbId X := boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X.obj
  pbComp f g := boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f.hom g.hom
  pbComp_assoc f g h M := boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj
      ℓ) ℓ f.hom g.hom h.hom M
  pbId_comp f M := boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ
      f.hom M
  pbComp_id f M := boundedConstructibleUpperStarComp_id_right_app (Profinite.padicAlgClRingObj ℓ) ℓ
      f.hom M
  pf f := boundedConstructibleLowerStar ℓ f.hom
  adj f := boundedConstructibleUpperStarLowerStarAdjunction ℓ f.hom
  sh j _ := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j.hom
  shAdj j _ := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j.hom

section Fields

variable {k} {X Y Z : SepFinType k}

@[simp]
lemma boundedConstructibleExchangeFormalism_obj :
    (boundedConstructibleExchangeFormalism ℓ k).obj X = Dᵇc(X.obj.left)⟦Profinite.padicAlgClRingObj
        ℓ⟧ :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pb (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism ℓ k).pb f = boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pbId :
    (boundedConstructibleExchangeFormalism ℓ k).pbId X =
      boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X.obj :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pbComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedConstructibleExchangeFormalism ℓ k).pbComp f g =
      boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f.hom g.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_pf (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism ℓ k).pf f = boundedConstructibleLowerStar ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_adj (f : X ⟶ Y) :
    (boundedConstructibleExchangeFormalism ℓ k).adj f =
      boundedConstructibleUpperStarLowerStarAdjunction ℓ f.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_sh (j : X ⟶ Y) [Fact (SepFinType.openImmersion j)] :
    (boundedConstructibleExchangeFormalism ℓ k).sh j =
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j.hom :=
  rfl

@[simp]
lemma boundedConstructibleExchangeFormalism_shAdj (j : X ⟶ Y)
    [Fact (SepFinType.openImmersion j)] :
    (boundedConstructibleExchangeFormalism ℓ k).shAdj j =
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj
          ℓ) ℓ j.hom :=
  rfl

end Fields
end AlgebraicGeometry.ProEtale.CondensedRing
