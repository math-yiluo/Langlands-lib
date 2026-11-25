/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!

# The relative Künneth map

Let `Λ` be a finite coefficient ring, `f : X ⟶ B`, `g : Y ⟶ B` morphisms admitting
compactifications and `p`, `q` the projections of `X ×_B Y`. This file defines the canonical
isomorphism of the relative product theorem (blueprint `lemma-kunneth-formula-compact-supports`,
`lemma-kunneth-formula-compact-supports--1`)

`κ^rel_{K,L} : R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`

as the explicit composite of the blueprint: the inverse of the composition isomorphism
`α_{g,q}`, the inverse of the projection map of `q` at `(Lp^* K, L)`, the inverse of the
compact-support base change map `Ex_! : Lg^* Rf_! K ⟶ Rq_! Lp^* K`, the symmetry of `⊗ᴸ`, the
inverse of the projection map of `g` at `(L, Rf_! K)` and the symmetry of `⊗ᴸ`. It is
defined for an arbitrary cartesian square (`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`)
and specialised to the chosen fibre product (`AlgebraicGeometry.Etale.relativeKunnethIso`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`: the composition isomorphism
  `R(h)_! ≅ Rf_! ⋙ Rg_!` for `f ≫ g = h`, on unbounded derived categories, for a finite
  coefficient ring.
- `AlgebraicGeometry.Etale.derivedTensorBraiding`: the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the
  derived tensor product, the braiding `DerivedCategory.braidedCategory'`.
- `AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`,
  `AlgebraicGeometry.Etale.relativeKunnethIso`: the relative Künneth isomorphism.
- `AlgebraicGeometry.Etale.relativeKunnethNatIso`: the relative Künneth isomorphism as a
  natural isomorphism of bifunctors `D(X_ét) ⥤ D(Y_ét) ⥤ D(B_ét)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Braiding

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The symmetry `σ : K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product of étale sheaves, natural
in both variables: the braiding `DerivedCategory.braidedCategory'` of `D(X_ét)`, as an
isomorphism between `- ⊗ᴸ -` and the flipped bifunctor. -/
noncomputable def derivedTensorBraiding : derivedTensor A X ≅ (derivedTensor A X).flip :=
  @BraidedCategory.curriedBraidingNatIso _ _ _
    (_root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A))


/-- The symmetry `σ_{M,N} : M ⊗ᴸ N ≅ N ⊗ᴸ M` of the derived tensor product of étale sheaves, the
component of `AlgebraicGeometry.Etale.derivedTensorBraiding`. -/
noncomputable def derivedTensorBraidingIso
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X)[A]).obj M).obj N ≅ ((-⊗ᴸ-(X)[A]).obj N).obj M :=
  ((derivedTensorBraiding A X).app M).app N

variable {A X} in
@[reassoc]
lemma derivedTensorBraidingIso_hom_naturality_left
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X)[A]).map φ).app N ≫ (derivedTensorBraidingIso A X M' N).hom =
      (derivedTensorBraidingIso A X M N).hom ≫ ((-⊗ᴸ-(X)[A]).obj N).map φ :=
  NatTrans.naturality_app (derivedTensorBraiding A X).hom N φ

variable {A X} in
@[reassoc]
lemma derivedTensorBraidingIso_hom_naturality_right
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (ψ : N ⟶ N') :
    ((-⊗ᴸ-(X)[A]).obj M).map ψ ≫ (derivedTensorBraidingIso A X M N').hom =
      (derivedTensorBraidingIso A X M N).hom ≫ ((-⊗ᴸ-(X)[A]).map ψ).app M :=
  ((derivedTensorBraiding A X).hom.app M).naturality ψ
end Braiding

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- statements specialised here (as in `LowerShriekProjectionExchange`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Composition

variable {X Y S : Scheme.{u}}

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: the composition isomorphism
`α : R(h)_! ≅ Rf_! ⋙ Rg_!` for `f ≫ g = h`, on unbounded derived categories, for a finite
coefficient ring (`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` transported along
`f ≫ g = h`). -/
noncomputable def rightDerivedLowerShriekCompIsoOfEq (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (w : f ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [QuasiCompact h] :
    R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : HasCompactification (f ≫ g) := .of_eq w.symm
  haveI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
  eqToIso (by subst w; rfl) ≪≫ rightDerivedLowerShriekCompIso Λ f g

end Composition

section Components

variable {B X Y P : Scheme.{u}}

/-- The composition isomorphism `α : Rh_! M ≅ Rg_! Rf_! M` for `f ≫ g = h`, at an object `M`
(the component of `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`). -/
noncomputable def rightDerivedLowerShriekCompIsoApp {S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (h : X ⟶ S) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj M ≅
      (R(g)_![ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) :=
  (rightDerivedLowerShriekCompIsoOfEq Λ f g h w).app M

@[reassoc]
lemma rightDerivedLowerShriekCompIsoApp_hom_naturality {S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (h : X ⟶ S) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ M') :
    (R(h)_![ModuleCat.{u + 1} Λ]).map φ ≫ (rightDerivedLowerShriekCompIsoApp Λ f g h w M').hom =
      (rightDerivedLowerShriekCompIsoApp Λ f g h w M).hom ≫
        (R(g)_![ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ) :=
  (rightDerivedLowerShriekCompIsoOfEq Λ f g h w).hom.naturality φ

/-- The projection formula `PF_{f,K,L} : Rf_! K ⊗ᴸ L ≅ Rf_!(K ⊗ᴸ Lf^* L)` for a finite
coefficient ring, as an isomorphism: the component at `L` of
`AlgebraicGeometry.Etale.projectionIso`, i.e. the projection map
`AlgebraicGeometry.Etale.projectionMap` at `(K, L)`. -/
noncomputable def projectionIsoApp (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj L ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  (projectionIso Λ f K).app L

lemma projectionIsoApp_hom (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (projectionIsoApp Λ f K L).hom = ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L :=
  rfl

@[reassoc]
lemma projectionIsoApp_hom_naturality_left (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app L ≫
        (projectionIsoApp Λ f K' L).hom =
      (projectionIsoApp Λ f K L).hom ≫ (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map φ).app ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  NatTrans.naturality_app (projectionMap (ModuleCat.{u + 1} Λ) f) L φ

@[reassoc]
lemma projectionIsoApp_hom_naturality_right (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map ψ ≫
        (projectionIsoApp Λ f K L').hom =
      (projectionIsoApp Λ f K L).hom ≫ (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map ψ)) :=
  ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).naturality ψ

@[reassoc]
lemma projectionIsoApp_inv_naturality_left (f : X ⟶ Y) [HasCompactification f]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).map φ).app ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
        (projectionIsoApp Λ f K' L).inv =
      (projectionIsoApp Λ f K L).inv ≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app L := by
  rw [Iso.comp_inv_eq, Category.assoc, projectionIsoApp_hom_naturality_left, Iso.inv_hom_id_assoc]

@[reassoc]
lemma projectionIsoApp_inv_naturality_right (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    (R(f)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map ψ)) ≫
        (projectionIsoApp Λ f K L').inv =
      (projectionIsoApp Λ f K L).inv ≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map ψ := by
  rw [Iso.comp_inv_eq, Category.assoc, projectionIsoApp_hom_naturality_right, Iso.inv_hom_id_assoc]

/-- Compact-support base change `Ex_! : Lg^* Rf_! K ≅ Rq_! Lp^* K` for a cartesian square
`p ≫ f = q ≫ g` and a finite coefficient ring, as an isomorphism: the component of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`. -/
noncomputable def rightDerivedLowerShriekBaseChangeIso {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≅
      (R(q)_![ModuleCat.{u + 1} Λ]).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)

lemma rightDerivedLowerShriekBaseChangeIso_hom {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeIso Λ sq K).hom =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app K :=
  rfl

@[reassoc]
lemma rightDerivedLowerShriekBaseChangeIso_inv_naturality {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g) [HasCompactification f]
    [HasCompactification q] [QuasiCompact q]
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    (R(q)_![ModuleCat.{u + 1} Λ]).map ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ) ≫
        (rightDerivedLowerShriekBaseChangeIso Λ sq K').inv =
      (rightDerivedLowerShriekBaseChangeIso Λ sq K).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, rightDerivedLowerShriekBaseChangeIso_hom,
    rightDerivedLowerShriekBaseChangeIso_hom]
  exact ((rightDerivedLowerShriekBaseChangeMap Λ sq).naturality φ).symm
end Components

section Kunneth

/-- Naturality of a composite of four isomorphisms, from the naturality of each factor. -/
lemma _root_.CategoryTheory.Iso.hom_naturality_trans₄ {C : Type*} [Category C]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : C}
    {e₁ : A₁ ≅ A₂} {e₂ : A₂ ≅ A₃} {e₃ : A₃ ≅ A₄} {e₄ : A₄ ≅ A₅}
    {e₁' : B₁ ≅ B₂} {e₂' : B₂ ≅ B₃} {e₃' : B₃ ≅ B₄} {e₄' : B₄ ≅ B₅}
    {φ₁ : A₁ ⟶ B₁} {φ₂ : A₂ ⟶ B₂} {φ₃ : A₃ ⟶ B₃} {φ₄ : A₄ ⟶ B₄} {φ₅ : A₅ ⟶ B₅}
    (h₁ : φ₁ ≫ e₁'.hom = e₁.hom ≫ φ₂) (h₂ : φ₂ ≫ e₂'.hom = e₂.hom ≫ φ₃)
    (h₃ : φ₃ ≫ e₃'.hom = e₃.hom ≫ φ₄) (h₄ : φ₄ ≫ e₄'.hom = e₄.hom ≫ φ₅) :
    φ₁ ≫ (e₁' ≪≫ e₂' ≪≫ e₃' ≪≫ e₄').hom = (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).hom ≫ φ₅ := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

variable {B X Y P : Scheme.{u}}

section Inner

variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
  [HasCompactification f] [HasCompactification q] [QuasiCompact q]

/-- The middle three arrows of the relative Künneth isomorphism, for a cartesian square
`p ≫ f = q ≫ g`:

```
Rq_!(Lp^*K ⊗ᴸ Lq^*L) ≅ Rq_! Lp^*K ⊗ᴸ L       (PF_{q, Lp^*K, L}⁻¹)
                     ≅ Lg^* Rf_! K ⊗ᴸ L      (Ex_!⁻¹ ⊗ 1)
                     ≅ L ⊗ᴸ Lg^* Rf_! K      (σ)
``` -/
noncomputable def relativeKunnethInnerIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(q)_![ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj L).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  (projectionIsoApp Λ q ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) L).symm ≪≫
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).mapIso (rightDerivedLowerShriekBaseChangeIso Λ sq K).symm).app
      L ≪≫
    derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) Y _ L

@[reassoc]
lemma relativeKunnethInnerIso_hom_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(q)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).map
        ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ)).app ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
      (relativeKunnethInnerIso Λ sq K' L).hom =
    (relativeKunnethInnerIso Λ sq K L).hom ≫ ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj L).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)) := by
  simp only [relativeKunnethInnerIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [projectionIsoApp_inv_naturality_left_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    rightDerivedLowerShriekBaseChangeIso_inv_naturality, Functor.map_comp,
    NatTrans.comp_app_assoc, derivedTensorBraidingIso_hom_naturality_left]

@[reassoc]
lemma relativeKunnethInnerIso_hom_naturality_right
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    (R(q)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).map ((L((q)^*[ModuleCat.{u + 1} Λ])).map ψ)) ≫
      (relativeKunnethInnerIso Λ sq K L').hom =
    (relativeKunnethInnerIso Λ sq K L).hom ≫ ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ψ).app
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  simp only [relativeKunnethInnerIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [projectionIsoApp_inv_naturality_right_assoc, NatTrans.naturality_assoc,
    derivedTensorBraidingIso_hom_naturality_right]

end Inner

/-- The relative Künneth isomorphism for an arbitrary cartesian square

```
  P --q--> Y
  |        |
  p        g
  v        v
  X --f--> B
```

and a morphism `h = q ≫ g`: for `K` on `X` and `L` on `Y`, the composite

```
Rh_!(Lp^*K ⊗ᴸ Lq^*L) ≅ Rg_! Rq_!(Lp^*K ⊗ᴸ Lq^*L)      (α_{g,q}⁻¹)
                     ≅ Rg_!(Rq_! Lp^*K ⊗ᴸ L)           (Rg_! PF_{q, Lp^*K, L}⁻¹)
                     ≅ Rg_!(Lg^* Rf_! K ⊗ᴸ L)          (Rg_!(Ex_!⁻¹ ⊗ 1))
                     ≅ Rg_!(L ⊗ᴸ Lg^* Rf_! K)          (Rg_! σ)
                     ≅ Rg_! L ⊗ᴸ Rf_! K                (PF_{g, L, Rf_! K}⁻¹)
                     ≅ Rf_! K ⊗ᴸ Rg_! L                (σ)
```

of blueprint `lemma-kunneth-formula-compact-supports`. Every arrow is an isomorphism for a finite
coefficient ring: the composition law, the projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def relativeKunnethIsoOfIsPullback {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) :=
  rightDerivedLowerShriekCompIsoApp Λ q g h w _ ≪≫
    (R(g)_![ModuleCat.{u + 1} Λ]).mapIso (relativeKunnethInnerIso Λ sq K L) ≪≫
    (projectionIsoApp Λ g L ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).symm ≪≫
    derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) B _ _

section Naturality

variable {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B)
  (w : q ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification q]
  [HasCompactification h] [QuasiCompact q] [QuasiCompact h]

@[reassoc]
lemma rightDerivedLowerShriek_map_relativeKunnethInnerIso_hom_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(g)_![ModuleCat.{u + 1} Λ]).map ((R(q)_![ModuleCat.{u + 1} Λ]).map
        (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).map ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ)).app
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L))) ≫
      ((R(g)_![ModuleCat.{u + 1} Λ]).mapIso (relativeKunnethInnerIso Λ sq K' L)).hom =
    ((R(g)_![ModuleCat.{u + 1} Λ]).mapIso (relativeKunnethInnerIso Λ sq K L)).hom ≫
      (R(g)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj L).map
        ((L((g)^*[ModuleCat.{u + 1} Λ])).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ))) := by
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
    relativeKunnethInnerIso_hom_naturality_left]

/-- Blueprint `lemma-kunneth-formula-compact-supports`: the relative Künneth isomorphism is natural
in the first variable. -/
@[reassoc]
theorem relativeKunnethIsoOfIsPullback_hom_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).map
        ((L((p)^*[ModuleCat.{u + 1} Λ])).map φ)).app ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
      (relativeKunnethIsoOfIsPullback Λ sq h w K' L).hom =
    (relativeKunnethIsoOfIsPullback Λ sq h w K L).hom ≫
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).map ((R(f)_![ModuleCat.{u + 1} Λ]).map φ)).app
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) := by
  exact Iso.hom_naturality_trans₄ (rightDerivedLowerShriekCompIsoApp_hom_naturality Λ q g h w _)
    (rightDerivedLowerShriek_map_relativeKunnethInnerIso_hom_naturality_left Λ sq φ L)
    (projectionIsoApp_inv_naturality_right Λ g L ((R(f)_![ModuleCat.{u + 1} Λ]).map φ))
    (derivedTensorBraidingIso_hom_naturality_right _ _)

/-- Blueprint `lemma-kunneth-formula-compact-supports`: the relative Künneth isomorphism is natural
in the second variable. -/
@[reassoc]
theorem relativeKunnethIsoOfIsPullback_hom_naturality_right
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ L') :
    (R(h)_![ModuleCat.{u + 1} Λ]).map (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).map ((L((q)^*[ModuleCat.{u + 1} Λ])).map ψ)) ≫
      (relativeKunnethIsoOfIsPullback Λ sq h w K L').hom =
    (relativeKunnethIsoOfIsPullback Λ sq h w K L).hom ≫
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).map
        ((R(g)_![ModuleCat.{u + 1} Λ]).map ψ) := by
  exact Iso.hom_naturality_trans₄ (rightDerivedLowerShriekCompIsoApp_hom_naturality Λ q g h w _)
    (by rw [Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
      relativeKunnethInnerIso_hom_naturality_right])
    (projectionIsoApp_inv_naturality_left Λ g ψ _)
    (derivedTensorBraidingIso_hom_naturality_left _ _)

/-- Blueprint `lemma-kunneth-formula-compact-supports`: the relative Künneth isomorphism
`Rh_!(Lp^*K ⊗ᴸ Lq^*L) ≅ Rf_! K ⊗ᴸ Rg_! L` as a natural isomorphism of bifunctors
`D(X_ét) ⥤ D(Y_ét) ⥤ D(B_ét)`, with components
`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`. -/
noncomputable def relativeKunnethNatIsoOfIsPullback :
    L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ -⊗ᴸ-(P)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj L((q)^*[ModuleCat.{u + 1} Λ]) ⋙
          (Functor.whiskeringRight _ _ _).obj R(h)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ -⊗ᴸ-(B)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(g)_![ModuleCat.{u + 1} Λ] :=
  NatIso.ofComponents
    (fun K ↦ NatIso.ofComponents (fun L ↦ relativeKunnethIsoOfIsPullback Λ sq h w K L)
      (fun ψ ↦ relativeKunnethIsoOfIsPullback_hom_naturality_right Λ sq h w K ψ))
    (fun φ ↦ by
      ext L
      exact relativeKunnethIsoOfIsPullback_hom_naturality_left Λ sq h w φ L)

lemma relativeKunnethNatIsoOfIsPullback_app_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((relativeKunnethNatIsoOfIsPullback Λ sq h w).app K).app L =
      relativeKunnethIsoOfIsPullback Λ sq h w K L :=
  rfl

end Naturality

section FibreProduct

variable (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
  [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]

omit [HasCompactification f] [HasCompactification g] [QuasiCompact g]
  [HasCompactification (pullback.toBase f g)] in
lemma quasiCompact_pullback_snd : QuasiCompact (pullback.snd f g) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback f g)
    inferInstance

omit [HasCompactification f] [HasCompactification g]
  [HasCompactification (pullback.toBase f g)] in
lemma quasiCompact_pullback_toBase : QuasiCompact (pullback.toBase f g) := by
  have := quasiCompact_pullback_snd f g
  rw [← pullback.snd_comp_eq_toBase]
  infer_instance

/-- Blueprint `lemma-kunneth-formula-compact-supports` (detailed:
`lemma-kunneth-formula-compact-supports--1`): **the relative Künneth isomorphism**. For `f : X ⟶ B`,
`g : Y ⟶ B` admitting compactifications, with `p`, `q` the projections of `X ×_B Y`, `K` on `X` and
`L` on `Y`, and a finite coefficient ring `Λ`,

`κ^rel_{K,L} : R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`

is the composite of the inverse of the composition isomorphism `α_{g,q}`, the inverse of the
projection map of `q` at `(Lp^* K, L)`, the inverse of compact-support base change
`Ex_! : Lg^* Rf_! K ⟶ Rq_! Lp^* K`, the symmetry of `⊗ᴸ`, the inverse of the projection map of
`g` at `(L, Rf_! K)` and the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback` for the fibre product square). Every
arrow is an isomorphism for all `K` and `L`; the blueprint's `Dctf` hypotheses are not needed
for a finite coefficient ring. -/
noncomputable def relativeKunnethIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K L) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) :=
  haveI := quasiCompact_pullback_snd f g
  haveI := quasiCompact_pullback_toBase f g
  relativeKunnethIsoOfIsPullback Λ (IsPullback.of_hasPullback f g) _
    (pullback.snd_comp_eq_toBase f g) K L

/-- Blueprint `lemma-kunneth-formula-compact-supports`: the relative Künneth isomorphism
`R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L` as a natural isomorphism of bifunctors
`D(X_ét) ⥤ D(Y_ét) ⥤ D(B_ét)`, with components `AlgebraicGeometry.Etale.relativeKunnethIso`. -/
noncomputable def relativeKunnethNatIso :
    L((pullback.fst f g)^*[ModuleCat.{u + 1} Λ]) ⋙ -⊗ᴸ-(pullback f g)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ]) ⋙
          (Functor.whiskeringRight _ _ _).obj R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ -⊗ᴸ-(B)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI := quasiCompact_pullback_snd f g
  haveI := quasiCompact_pullback_toBase f g
  relativeKunnethNatIsoOfIsPullback Λ (IsPullback.of_hasPullback f g) _
    (pullback.snd_comp_eq_toBase f g)

lemma relativeKunnethNatIso_app_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((relativeKunnethNatIso Λ f g).app K).app L = relativeKunnethIso Λ f g K L :=
  rfl

end FibreProduct

end Kunneth

end Etale

end AlgebraicGeometry
