/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Open base change for the pushforward of `ℓ`-adic sheaves

Let

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

be a cartesian square of schemes with `j` and `j'` weakly étale. The base change map
`j^* g''_* ⟶ g'_* j'^*` of sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`) lifts to sheaves of modules over
the constant `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicBaseChangeMap`), where it is again
an isomorphism, the forgetful functor reflecting isomorphisms. For `j` an open immersion the
pullbacks along `j` and `j'` have exact left adjoints, the extensions by zero, so they preserve
K-injective complexes, and the base change isomorphism derives:
`j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*` (`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`). In
particular the higher direct images commute with restriction to an open subscheme.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

private lemma adicBaseChange_mate_symm_app {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H G R₂) (M : C) :
    ((mateEquiv adj₁ adj₂).symm β).app M =
      L₂.map (G.map (adj₁.unit.app M)) ≫
        L₂.map (β.app (L₁.obj M)) ≫ adj₂.counit.app (H.obj (L₁.obj M)) := by
  simp

private lemma adicBaseChange_isoTrans_app {C D : Type*} [Category* C] [Category* D]
    {F₁ F₂ F₃ F₄ : C ⥤ D} (e₁ : F₁ ≅ F₂) (e₂ : F₂ ≅ F₃) (e₃ : F₄ ≅ F₃) (M : C) :
    (e₁ ≪≫ e₂ ≪≫ e₃.symm).hom.app M =
      e₁.hom.app M ≫ e₂.hom.app M ≫ e₃.inv.app M := rfl

variable (l : ℕ) [Fact l.Prime]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

/-- The square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards of `ℓ`-adic sheaves
attached to a commutative square `g' ≫ j = j' ≫ g''`. -/
noncomputable def adicSquareLowerStarIso (sq : CommSq g' j' j g'') :
    (j')_*ᵃ[l] ⋙ (g'')_*ᵃ[l] ≅ (g')_*ᵃ[l] ⋙ (j)_*ᵃ[l] :=
  adicLowerStarComp l j' g'' ≪≫ adicLowerStarCongr l sq.w.symm ≪≫
    (adicLowerStarComp l g' j).symm

private lemma adicSquareLowerStarIso_hom_app (sq : CommSq g' j' j g'')
    (M : AdicSheaf l U') :
    (adicSquareLowerStarIso l sq).hom.app M =
      (adicLowerStarComp l j' g'').hom.app M ≫
        (adicLowerStarCongr l sq.w.symm).hom.app M ≫ (adicLowerStarComp l g' j).inv.app M :=
  adicBaseChange_isoTrans_app _ _ _ _

private lemma adicSquareLowerStarIso_hom_app_hom (sq : CommSq g' j' j g'')
    (M : AdicSheaf l U') :
    ((adicSquareLowerStarIso l sq).hom.app M).hom =
      (ProEtale.squareLowerStarIso (WeilCoefficients.{u} l) sq).hom.app M.X := by
  -- Compare on sections and retain the rewrite proofs: reducing the composite module
  -- structures directly makes kernel checking much more expensive.
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  rewrite [adicSquareLowerStarIso_hom_app]
  unfold ProEtale.squareLowerStarIso
  repeat' rewrite [Iso.trans_hom]
  repeat' rewrite [Iso.symm_hom]
  repeat' rewrite [NatTrans.comp_app]
  repeat' rewrite [Mod.comp_hom']
  repeat' rewrite [ObjectProperty.FullSubcategory.comp_hom]
  repeat' rewrite [NatTrans.comp_app]
  rewrite [adicLowerStarComp_hom_app_hom_hom_app,
    adicLowerStarCongr_hom_app_hom_hom_app, adicLowerStarComp_inv_app_hom_hom_app]
  rewrite [lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app]
  rfl

private lemma adicBaseChange_unit_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : AdicSheaf l Y) :
    ((adicUpperStarLowerStarAdjunction l f).unit.app M).hom =
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit.app M.X := by
  exact Adjunction.modAdjunction_unit_app_hom _ _ _

private lemma adicBaseChange_counit_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : AdicSheaf l X) :
    ((adicUpperStarLowerStarAdjunction l f).counit.app M).hom =
      (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).counit.app M.X := by
  exact Adjunction.modAdjunction_counit_app_hom _ _ _

variable [WeaklyEtale j] [WeaklyEtale j']

/-- **The base change map** `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of `ℓ`-adic sheaves, for a commutative
square with `j` and `j'` weakly étale: the mate of
`AlgebraicGeometry.ProEtale.adicSquareLowerStarIso` along `j'^* ⊣ j'_*` and `j^* ⊣ j_*`. -/
noncomputable def adicBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*ᵃ[l] ⋙ (j)^*ᵃ[l] ⟶ (j')^*ᵃ[l] ⋙ (g')_*ᵃ[l] :=
  ((mateEquiv (adicUpperStarLowerStarAdjunction l j')
    (adicUpperStarLowerStarAdjunction l j)).symm
    (TwoSquare.mk _ _ _ _ (adicSquareLowerStarIso l sq).hom))

omit [WeaklyEtale j] [WeaklyEtale j'] in
/-- The underlying map of sheaves of `ℚ̄_ℓ`-modules of the base change map of `ℓ`-adic sheaves is
the base change map of the underlying sheaves. -/
lemma adicBaseChangeMap_app_hom (sq : CommSq g' j' j g'') (M : AdicSheaf l Z') :
    ((adicBaseChangeMap l sq).app M).hom =
      (ProEtale.baseChangeMap (WeilCoefficients.{u} l) sq).app M.X := by
  dsimp only [adicBaseChangeMap, ProEtale.baseChangeMap]
  rw [adicBaseChange_mate_symm_app, adicBaseChange_mate_symm_app]
  simp (config := { dsimp := false }) only [Mod.comp_hom', adicUpperStar_map_hom,
    adicLowerStar_map_hom, adicBaseChange_unit_app_hom, adicBaseChange_counit_app_hom,
    adicSquareLowerStarIso_hom_app_hom]
  rfl

/-- **Weakly étale base change for `ℓ`-adic sheaves**: for a cartesian square the base change
map is an isomorphism. -/
instance isIso_adicBaseChangeMap_of_isPullback (hsq : IsPullback g' j' j g'') :
    IsIso (adicBaseChangeMap l hsq.toCommSq) := by
  have := ProEtale.isIso_baseChangeMap_of_isPullback (WeilCoefficients.{u} l) hsq
  have (M : AdicSheaf l Z') : IsIso ((adicBaseChangeMap l hsq.toCommSq).app M) := by
    have : IsIso ((Mod.forget _).map ((adicBaseChangeMap l hsq.toCommSq).app M)) := by
      change IsIso ((adicBaseChangeMap l hsq.toCommSq).app M).hom
      rw [adicBaseChangeMap_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

section Derived

variable [IsOpenImmersion j] [IsOpenImmersion j']

instance : (j')^*ᵃ[l].PreservesKInjectiveComplexes :=
  (adicOpenImmersionLowerShriekAdjunction l j').preservesKInjectiveComplexes

/-- **Open base change for the derived pushforward of `ℓ`-adic sheaves**: for a cartesian square
with `j` (hence `j'`) an open immersion, `j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*`.

```
D(Z') --Rg''_*--> D(Z)
  |                 |
 j'^*             j^*
  v                 v
D(U') --Rg'_*---> D(U)
```
-/
noncomputable def adicDerivedBaseChangeIso (hsq : IsPullback g' j' j g'') :
    (g'')_*ᵃ[l].rightDerivedFunctor ⋙ (j)^*ᵃ[l].mapDerivedCategory ≅
      (j')^*ᵃ[l].mapDerivedCategory ⋙ (g')_*ᵃ[l].rightDerivedFunctor :=
  have := isIso_adicBaseChangeMap_of_isPullback l hsq
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (g'')_*ᵃ[l] (j)^*ᵃ[l]).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (adicBaseChangeMap l hsq.toCommSq)) ≪≫
    Functor.rightDerivedFunctorCompIso (j')^*ᵃ[l] (g')_*ᵃ[l] ≪≫
    Functor.isoWhiskerRight (j')^*ᵃ[l].rightDerivedFunctorIsoMapDerivedCategory
      (g')_*ᵃ[l].rightDerivedFunctor

end Derived

end AlgebraicGeometry.ProEtale
