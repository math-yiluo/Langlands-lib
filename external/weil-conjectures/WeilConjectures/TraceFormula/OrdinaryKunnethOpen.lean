/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.OrdinaryKunneth
public import WeilConjectures.CategoryTheory.Adjunction.KunnethNatTransRestriction
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbient
public import WeilConjectures.TraceFormula.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# The ordinary Künneth map under restriction to an open subscheme

Let `v : V ⟶ X` and `j : U ⟶ Y` be open immersions of separated `k`-schemes of finite type. This
file shows that the restriction along `v × 𝟙 : V ⨯ Y ⟶ X ⨯ Y` of the Künneth map
`M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` (`ProEtale.CondensedRing.openKunnethMap`) is an isomorphism as
soon as the Künneth map of `Lv^* M` is
(`ProEtale.CondensedRing.isIso_upperStar_map_openKunnethMap_of_isOpenImmersion`).

## Main statements

- `ProEtale.CondensedRing.isIso_exchangeRight_pullbackSquareComparison_app_of_weaklyEtale`:
  weakly étale base change on bounded constructible complexes, deduced from the ambient statement
  `ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`.
- `ProEtale.CondensedRing.isPullback_prodMap_prodMap`: the square of `v × 𝟙` and `𝟙 × j` is
  cartesian.
- `ProEtale.CondensedRing.isIso_upperStar_map_openKunnethMap_of_isOpenImmersion`: the restriction
  of the Künneth map, by the abstract statement
  `CategoryTheory.Adjunction.isIso_map_kunnethNatTrans_app_of_isIso_homEquiv`.

## Implementation notes

As in `WeilConjectures.TraceFormula.OrdinaryKunneth`, the Künneth maps are compared through an
abstract lemma, and the second factors only through the invertibility of their transposes: terms
elaborated in this file differ from the bodies of the definitions of `OrdinaryKunneth` in their
auxiliary proofs, and comparing them makes the elaborator and the kernel unfold the six functors.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

section BaseChange

variable {A B A' B' : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
  [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType A'.hom] [QuasiCompact A'.hom] [IsSeparated A'.hom]
  [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
  {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}

/-- **Weakly étale base change on bounded constructible complexes**: for a commutative square
`g' ≫ f = f' ≫ g` whose underlying square of schemes is cartesian, with `g` and `g'` weakly étale
(for instance open immersions), the base change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*` is an
isomorphism on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`. On the ambient derived categories it is the base change morphism
`baseChangeMap` of the square, an isomorphism by weakly étale base change
(`isIso_baseChangeMap_of_weaklyEtale`). -/
theorem isIso_exchangeRight_pullbackSquareComparison_app_of_weaklyEtale (sq : CommSq g' f' f g)
    (hsq : IsPullback g'.left f'.left f.left g.left) [WeaklyEtale g.left] [WeaklyEtale g'.left]
    (K : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq)).app
        K) := by
  -- Reuse the graded tensor instances across the schemes in the square.
  have tensor₄ (T : Scheme.{u})
      (W X Y Z : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))) :
      GradedObject.HasTensor₄ObjExt W X Y Z := by infer_instance
  have tensor₁₂ (T : Scheme.{u})
      (X Y Z : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have tensor₂₃ (T : Scheme.{u})
      (X Y Z : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have hamb : IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) hsq.toCommSq).app K.obj) := by
    have := isIso_baseChangeMap_of_weaklyEtale (Profinite.padicAlgClRingObj ℓ) hsq
    infer_instance
  unfold baseChangeMap at hamb
  rw [pullbackSquareComparison_eq_leftDerivedFunctorSquareIso] at hamb
  have hθ (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).hom.app
        K).hom = (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison
          (Profinite.padicAlgClRingObj ℓ) hsq.toCommSq)).hom.app K.obj := by
    rw [boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison,
      pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  have key := Adjunction.isIso_exchangeRight_restrictFullyFaithful_app _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ f K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ f' K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ g' K)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq)
    hθ K hamb
  convert key using 3
  all_goals rfl

end BaseChange

variable {X Y U V : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The square `(v × 𝟙_U) ≫ (𝟙_X × j) = (𝟙_V × j) ≫ (v × 𝟙_Y)` of products is cartesian. -/
lemma isPullback_prodMap_prodMap (v : V ⟶ X) (j : U ⟶ Y) :
    IsPullback (prod.map v (𝟙 U)) (prod.map (𝟙 V) j) (prod.map (𝟙 X) j) (prod.map v (𝟙 Y)) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_prod_fst_with_id v Y).flip
  rw [prod.map_fst, prod.map_fst, Category.comp_id, Category.comp_id]
  exact (IsPullback.of_prod_fst_with_id v U).flip

/-- **The Künneth map restricted to an open subscheme**: for open immersions `v : V ⟶ X` and
`j : U ⟶ Y`, the restriction along `v × 𝟙 : V ⨯ Y ⟶ X ⨯ Y` of the Künneth map
`M ⊠ Rj_* B ⟶ R(𝟙 × j)_* (M ⊠ B)` is an isomorphism as soon as the Künneth map of `Lv^* M` is.
Through the base change isomorphism `L(v × 𝟙)^* R(𝟙 × j)_* ≅ R(𝟙 × j)_* L(v × 𝟙)^*` of the
cartesian square `isPullback_prodMap_prodMap` (weakly étale base change), the composition
isomorphisms of the pullbacks along the projections and the monoidal structure of `L(v × 𝟙)^*`,
the restricted Künneth map of `(M, B)` is a Künneth map of `(Lv^* M, B)` whose second factor has
an invertible transpose, as has the one of `openKunnethMap` by generic base change
(`CategoryTheory.Adjunction.isIso_map_kunnethNatTrans_app_of_isIso_homEquiv`). -/
theorem isIso_upperStar_map_openKunnethMap_of_isOpenImmersion
    {V : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (v : V ⟶ X) [IsOpenImmersion v.left] (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (openKunnethMap ℓ (X := V) j
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v).obj M) B)) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map v (𝟙 Y))).map (openKunnethMap ℓ j M B)) := by
  have hpb := isPullback_prodMap_prodMap v j
  have hoY : IsOpenImmersion (prod.map v (𝟙 Y)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id v Y).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion v.left))
  have hoU : IsOpenImmersion (prod.map v (𝟙 U)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_prod_fst_with_id v U).map (Over.forget _))
      (inferInstanceAs (IsOpenImmersion v.left))
  have hY : prod.map v (𝟙 Y) ≫ prod.snd = (prod.snd : V ⨯ Y ⟶ Y) := by
    rw [prod.map_snd, Category.comp_id]
  have hU : prod.map v (𝟙 U) ≫ prod.snd = (prod.snd : V ⨯ U ⟶ U) := by
    rw [prod.map_snd, Category.comp_id]
  unfold openKunnethMap at h ⊢
  have hc' := Adjunction.isIso_homEquiv_of_isIso_kunnethNatTrans_app _ _ _ h
    (isIso_homEquiv_openKunnethSecondFactor ℓ j B)
  refine Adjunction.isIso_map_kunnethNatTrans_app_of_isIso_homEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j)) _
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      hpb.toCommSq) (prodMapUpperStarFstIso ℓ j) _ (prodMapUpperStarFstIso ℓ (X := V) j) _
    (boundedConstructiblePullbackSquareComparison_hom_app_δ ℓ hpb.toCommSq)
    (M' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v).obj M)
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      (⟨prod.map_fst _ _⟩ : CommSq (prod.map v (𝟙 Y)) prod.fst prod.fst v)).app M).symm
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map v (𝟙 Y))
      prod.snd).symm.app _ ≪≫ eqToIso (congrArg (fun u ↦ (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ u).obj _) hY))
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map v (𝟙 U))
      prod.snd).symm.app _ ≪≫ eqToIso (congrArg (fun u ↦ (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ u).obj _) hU))
    ?_ ?_ ?_ ?_ h
  · exact isIso_exchangeRight_pullbackSquareComparison_app_of_weaklyEtale ℓ hpb.toCommSq
      (hpb.map (Over.forget _)) _
  · exact isIso_exchangeRight_pullbackSquareComparison_app_of_weaklyEtale ℓ hpb.toCommSq
      (hpb.map (Over.forget _)) _
  · exact isIso_homEquiv_openKunnethSecondFactor ℓ j B
  · exact hc'

end AlgebraicGeometry.ProEtale.CondensedRing
