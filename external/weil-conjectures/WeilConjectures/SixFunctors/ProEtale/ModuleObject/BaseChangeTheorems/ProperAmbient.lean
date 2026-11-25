/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.CategoryTheory.PullbackFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!
# Proper base change for `ℚ̄_ℓ`-sheaves on the ambient derived categories

The proper base change theorem for bounded constructible `ℚ̄_ℓ`-sheaves
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`) is stated
for the base-change morphism of the bounded constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`. This
file shows that the base change map `Lg^* Rp_* K ⟶ Rp'_* Lg'^* K`
(`ProEtale.CondensedRing.baseChangeMap`) of the ambient derived categories of module objects is
invertible at a bounded constructible `K` as soon as the bounded constructible base-change
morphism is
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isIso_boundedConstructibleExchangeRight`).
Proper base change on the ambient derived categories, over arbitrary noetherian bases over fields,
is `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase`).

The two base-change morphisms are the exchange morphisms of the pullback comparisons, and the
one on bounded constructible complexes is the restriction of the ambient one
(`CategoryTheory.Adjunction.exchangeRight_restrictFullyFaithful_app_hom`), the pullback
comparison on bounded constructible complexes being the ambient one (`ProEtale.CondensedRing.
boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- On the ambient derived categories, the pullback comparison of a commutative square on bounded
constructible complexes is the pullback comparison `pullbackSquareComparison` of the underlying
square of schemes. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq g' f' f g) (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
      (pullbackSquareComparison Λ
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom.app
        K.obj := by
  have hinv (a : X' ⟶ Y') (b : Y' ⟶ Y) :
      ((boundedConstructibleUpperStarComp Λ ℓ a b).inv.app K).hom =
        (leftDerivedUpperStarComp Λ a.left b.left).inv.app K.obj := by
    simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
      ObjectProperty.liftCompιIso]
  have e {A₁ A₂ : Dᵇc(X'.left)⟦Λ⟧} (h : A₁ = A₂) :
      (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    subst h
    rfl
  simp only [boundedConstructiblePullbackSquareComparison_hom_app Λ ℓ sq K,
    pullbackSquareComparison_hom_app Λ _ K.obj, ObjectProperty.FullSubcategory.comp_hom,
    hinv f' g, boundedConstructibleUpperStarComp_hom_app_hom Λ ℓ g' f K, e]

/-- Transport the ambient comparison of components along an equality of square isomorphisms. -/
private lemma boundedConstructiblePullbackSquareComparison_hom_app_hom_of_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq g' f' f g) (sq' : CommSq g'.left f'.left f.left g.left) {θ}
    (hθ : pullbackSquareComparison Λ sq' = θ) (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom = θ.hom.app K.obj := by
  obtain rfl : sq' = (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ :
      CommSq g'.left f'.left f.left g.left) := Subsingleton.elim _ _
  exact (boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison
    ℓ Λ sq K).trans (congrArg (fun e ↦ e.hom.app K.obj) hθ)

/-- The base change map of the ambient derived categories of module objects over `ℚ̲̄_ℓ` at a
bounded constructible `K` is an isomorphism as soon as the base-change morphism of the bounded
constructible derived categories is an isomorphism at `K`: the latter is the restriction of the
former (`Adjunction.exchangeRight_restrictFullyFaithful_app_hom`). -/
lemma isIso_baseChangeMap_app_of_isIso_boundedConstructibleExchangeRight
    (sq : CommSq g' f' f g)
    (sq' : CommSq g'.left f'.left f.left g.left) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hres : IsIso ((Adjunction.exchangeRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq)).app
        K)) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq').app K.obj) := by
  unfold baseChangeMap
  rw [pullbackSquareComparison_eq_leftDerivedFunctorSquareIso (Profinite.padicAlgClRingObj ℓ) sq']
  have key := Adjunction.exchangeRight_restrictFullyFaithful_app_hom
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f'.left)
    (Adjunction.leftDerivedFunctorSquareIso (upperStarSquareComparison
          (Profinite.padicAlgClRingObj ℓ) sq'))
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ f K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ f' K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj (Profinite.padicAlgClRingObj ℓ) ℓ g' K)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq)
    (boundedConstructiblePullbackSquareComparison_hom_app_hom_of_eq
      ℓ (Profinite.padicAlgClRingObj ℓ) sq sq'
      (pullbackSquareComparison_eq_leftDerivedFunctorSquareIso
        (Profinite.padicAlgClRingObj ℓ) sq')) K
  rw [← key, ObjectProperty.isIso_hom_iff]
  convert hres using 3
  all_goals rfl

end AlgebraicGeometry.ProEtale.CondensedRing
