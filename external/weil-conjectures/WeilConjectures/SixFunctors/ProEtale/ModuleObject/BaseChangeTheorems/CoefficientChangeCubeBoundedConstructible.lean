/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.CategoryTheory.PullbackFamily

/-!

# The bounded constructible base-change morphism under a flat change of coefficients

For a flat coefficient change `a : Λ ⟶ Λ'` and a commutative square of schemes separated and of
finite type over `k`, the scalar comparisons identify `T^{Y'}` of the base-change morphism `BC_sq`
on `Dᵇc(-)⟦Λ⟧` with the base-change morphism on `Dᵇc(-)⟦Λ'⟧` at `T^X K₀`, where `T` is the
restriction of the derived extension of scalars
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars`). This
is the ambient statement
`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars`, transferred along
the fully faithful inclusions by
`Adjunction.nonempty_arrowIso_lift_map_app_of_eq_exchangeRight_restrictFullyFaithful`.

## Implementation notes

The restricted derived pullbacks are compared with the ambient ones in the presentation
`ObjectProperty.lift (ι ⋙ L(h^*))` of `Adjunction.exchangeRight_restrictFullyFaithful_app_hom`.
The objects of `Dᵇc(-)⟦Λ⟧` carry another presentation of the instance
`MonoidalPreadditive (Sheaf _ Ab)` in `boundedConstructible` (an auxiliary proof constant of
`ProEtale.BoundedConstructible`), and identifying the two by proof irrelevance is very expensive.
Hence the comparison of the pullback square comparisons is restated here in the `lift`
presentation instead of using
`boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- the objects of the bounded constructible and of the ambient derived categories are compared
omit [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] in
/-- On the ambient derived categories, the pullback comparison of a commutative square on bounded
constructible complexes is the pullback comparison of the underlying square of schemes
(`boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison`), stated
with the restricted derived pullbacks presented as `ObjectProperty.lift`s of the ambient ones, as
they appear in `Adjunction.exchangeRight_restrictFullyFaithful_app_hom`: comparing this
presentation with the one through `Dᵇc(-)⟦Λ⟧` is expensive. -/
private lemma pullbackSquareComparison_hom_app_hom_aux
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq g' f' f g)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ((Iso.hom (X := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((g.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g K) ⋙
       (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f'.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K))
      (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K) ⋙
       (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((g'.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g' K))
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq)).app K).hom =
      (pullbackSquareComparison Λ
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom.app
        K.obj := by
  have hinv (p : X' ⟶ Y') (q : Y' ⟶ Y) :
      ((boundedConstructibleUpperStarComp Λ ℓ p q).inv.app K).hom =
        (leftDerivedUpperStarComp Λ p.left q.left).inv.app K.obj := by
    simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
      ObjectProperty.liftCompιIso]
  have e {A₁ A₂ : Dᵇc(X'.left)⟦Λ⟧} (h : A₁ = A₂) :
      (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    subst h
    rfl
  rw [boundedConstructiblePullbackSquareComparison_hom_app, pullbackSquareComparison_hom_app]
  exact congrArg₂ (· ≫ ·) (hinv f' g) (congrArg₂ (· ≫ ·) (e _)
    (boundedConstructibleUpperStarComp_hom_app_hom Λ ℓ g' f K))

/-- **The base-change morphism under a flat change of coefficients**, on bounded constructible
complexes. Let `T^X = L(Ext_{a_X})` preserve bounded constructible complexes on `X` and `Y'`, and
write `T^X : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧` for its restriction. Assume that `derivedPullIso a` is
compatible with the composition of derived pullbacks, and that the comparisons
`derivedPushHom a f` at `K₀` and `derivedPushHom a f'` at `Lg'^* K₀` are invertible. Then
`T^{Y'}` of the base-change morphism `BC_sq^Λ` at `K₀` and the base-change morphism `BC_sq^Λ'` at
`T^X K₀` are isomorphic arrows. -/
theorem nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' f' f g)
    (hRf : ∀ K : Dᵇc(X.left)⟦Λ⟧, boundedConstructible (condensedRingObj Λ Y.left)
      ((R((f.left)_*⟦Λ⟧)).obj K.obj))
    (hRf' : ∀ K : Dᵇc(X'.left)⟦Λ⟧, boundedConstructible (condensedRingObj Λ Y'.left)
      ((R((f'.left)_*⟦Λ⟧)).obj K.obj))
    (hSf : ∀ K : Dᵇc(X.left)⟦Λ'⟧, boundedConstructible (condensedRingObj Λ' Y.left)
      ((R((f.left)_*⟦Λ'⟧)).obj K.obj))
    (hSf' : ∀ K : Dᵇc(X'.left)⟦Λ'⟧, boundedConstructible (condensedRingObj Λ' Y'.left)
      ((R((f'.left)_*⟦Λ'⟧)).obj K.obj))
    (hX : ∀ K : Dᵇc(X.left)⟦Λ⟧, boundedConstructible (condensedRingObj Λ' X.left)
      (((boundedConstructible _).ι ⋙
        (Mod.extendScalars (coefficientMap a X.left)).leftDerivedFunctor).obj K))
    (hY' : ∀ K : Dᵇc(Y'.left)⟦Λ⟧, boundedConstructible (condensedRingObj Λ' Y'.left)
      (((boundedConstructible _).ι ⋙
        (Mod.extendScalars (coefficientMap a Y'.left)).leftDerivedFunctor).obj K))
    (β : (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧)) hRf ⋙
        boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f'.left)_*⟦Λ⟧)) hRf')
    (hβ : β = Adjunction.exchangeRight
      ((derivedUpperStarLowerStarAdjunction Λ f.left).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
        (ObjectProperty.liftCompιIso _ _ hRf).symm)
      ((derivedUpperStarLowerStarAdjunction Λ f'.left).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility Λ ℓ f').symm
        (ObjectProperty.liftCompιIso _ _ hRf').symm)
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq))
    (β' : (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ'⟧)) hSf ⋙
        boundedConstructibleUpperStar Λ' ℓ g ⟶
      boundedConstructibleUpperStar Λ' ℓ g' ⋙
        (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f'.left)_*⟦Λ'⟧)) hSf')
    (hβ' : β' = Adjunction.exchangeRight
      ((derivedUpperStarLowerStarAdjunction Λ' f.left).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility Λ' ℓ f).symm
        (ObjectProperty.liftCompιIso _ _ hSf).symm)
      ((derivedUpperStarLowerStarAdjunction Λ' f'.left).restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleUpperStarCompatibility Λ' ℓ f').symm
        (ObjectProperty.liftCompιIso _ _ hSf').symm)
      (boundedConstructiblePullbackSquareComparison Λ' ℓ sq))
    (K₀ : Dᵇc(X.left)⟦Λ⟧) (h₁ : IsIso ((derivedPushHom a f.left).app K₀.obj))
    (h₂ : IsIso ((derivedPushHom a f'.left).app
      ((g'.left)^*⟦Λ⟧.leftDerivedFunctor.obj K₀.obj))) :
    Nonempty (Arrow.mk (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
        (Mod.extendScalars (coefficientMap a Y'.left)).leftDerivedFunctor) hY').map
          (β.app K₀)) ≅
      Arrow.mk (β'.app
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          (Mod.extendScalars (coefficientMap a X.left)).leftDerivedFunctor) hX).obj K₀))) := by
  have := Adjunction.nonempty_arrowIso_lift_map_app_of_eq_exchangeRight_restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction Λ f.left) (derivedUpperStarLowerStarAdjunction Λ f'.left)
    (derivedUpperStarLowerStarAdjunction Λ' f.left)
    (derivedUpperStarLowerStarAdjunction Λ' f'.left) _ _ (derivedPullIso a f.left)
    (derivedPullIso a f'.left) (derivedPullIso a g.left) (derivedPullIso a g'.left)
    (derivedPullIso_cube a H ⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩)
    (derivedPushHom a f.left) (Adjunction.pushHomOfComapIso_eq_mateEquiv _ _ _ _ _)
    (derivedPushHom a f'.left) (Adjunction.pushHomOfComapIso_eq_mateEquiv _ _ _ _ _)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K) hRf
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K) hRf'
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ' ℓ f K) hSf
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ' ℓ f' K) hSf'
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ' ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ' ℓ g' K)
    hX hY' (boundedConstructiblePullbackSquareComparison Λ ℓ sq)
    (pullbackSquareComparison_hom_app_hom_aux ℓ Λ sq)
    (boundedConstructiblePullbackSquareComparison Λ' ℓ sq)
    (pullbackSquareComparison_hom_app_hom_aux ℓ Λ' sq) β hβ β' hβ' K₀ h₁ h₂
  exact this

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
