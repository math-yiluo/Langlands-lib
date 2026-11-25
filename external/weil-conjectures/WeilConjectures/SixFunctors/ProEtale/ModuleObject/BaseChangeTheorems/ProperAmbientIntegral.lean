/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbient

/-!
# Proper base change for `𝒪_E`-sheaves on the ambient derived categories

The proper base change theorem for bounded constructible `𝒪_E`-sheaves
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`) is stated
for the base-change morphism of the bounded constructible derived categories `Dᵇc(-)⟦𝒪̲_E⟧`. This
file reads it on the ambient derived categories of module objects: for a cartesian square
`g' ≫ p = p' ≫ g` of separated `k`-schemes of finite type with `p` proper, the base change map
`Lg^* Rp_* K ⟶ Rp'_* Lg'^* K` (`ProEtale.CondensedRing.baseChangeMap`) is an isomorphism for every
bounded constructible `K`
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_isProper`).

As for `ℚ̄_ℓ`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbient`),
the base-change morphism on bounded constructible complexes is the restriction of the ambient one
(`CategoryTheory.Adjunction.exchangeRight_restrictFullyFaithful_app_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

/-- Transfer invertibility from a restricted exchange map to its ambient component. -/
private lemma isIso_exchangeRight_of_restrictFullyFaithful_app
    {B A B' A' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
    {PB : ObjectProperty B} {PA : ObjectProperty A} {PB' : ObjectProperty B'}
    {PA' : ObjectProperty A'}
    {lf : B ⥤ A} {rf : A ⥤ B} {lf' : B' ⥤ A'} {rf' : A' ⥤ B'}
    {g : B ⥤ B'} {g' : A ⥤ A'}
    (ad : lf ⊣ rf) (ad' : lf' ⊣ rf') (t : g ⋙ lf' ≅ lf ⋙ g')
    (hlf : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ lf).obj K))
    (hrf : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ rf).obj K))
    (hlf' : ∀ K : PB'.FullSubcategory, PA' ((PB'.ι ⋙ lf').obj K))
    (hrf' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ rf').obj K))
    (hg : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ g).obj K))
    (hg' : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ g').obj K))
    (θ : PB'.lift (PB.ι ⋙ g) hg ⋙ PA'.lift (PB'.ι ⋙ lf') hlf' ≅
      PA.lift (PB.ι ⋙ lf) hlf ⋙ PA'.lift (PA.ι ⋙ g') hg')
    (hθ : ∀ K, (θ.hom.app K).hom = t.hom.app K.obj) (K : PA.FullSubcategory)
    (hK : IsIso ((Adjunction.exchangeRight
      (ad.restrictFullyFaithful PB.fullyFaithfulι PA.fullyFaithfulι
        (PA.liftCompιIso (PB.ι ⋙ lf) hlf).symm (PB.liftCompιIso (PA.ι ⋙ rf) hrf).symm)
      (ad'.restrictFullyFaithful PB'.fullyFaithfulι PA'.fullyFaithfulι
        (PA'.liftCompιIso (PB'.ι ⋙ lf') hlf').symm (PB'.liftCompιIso (PA'.ι ⋙ rf') hrf').symm)
      θ).app K)) :
    IsIso ((Adjunction.exchangeRight ad ad' t).app K.obj) := by
  rw [← Adjunction.exchangeRight_restrictFullyFaithful_app_hom
    ad ad' t hlf hrf hlf' hrf' hg hg' θ hθ K, ObjectProperty.isIso_hom_iff]
  exact hK

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The base change map of the ambient derived categories of module objects over `𝒪̲_E` at a
bounded constructible `K` is an isomorphism as soon as the base-change morphism of the bounded
constructible derived categories is an isomorphism at `K`: the latter is the restriction of the
former (`Adjunction.exchangeRight_restrictFullyFaithful_app_hom`). -/
lemma isIso_baseChangeMap_app_of_isIso_boundedConstructibleExchangeRight_padicIntegers
    (sq : CommSq g' f' f g) (sq' : CommSq g'.left f'.left f.left g.left)
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (hres : IsIso ((Adjunction.exchangeRight
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
      (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
        sq)).app K)) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq').app K.obj) := by
  unfold baseChangeMap
  rw [pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  -- Infer the square isomorphism from the goal to reuse its derived-functor instances.
  refine isIso_exchangeRight_of_restrictFullyFaithful_app
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left)
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f'.left)
    _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj
      (Profinite.padicIntegersRingObj ℓ E) ℓ f K)
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj
      (Profinite.padicIntegersRingObj ℓ E) ℓ f' K)
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj
      (Profinite.padicIntegersRingObj ℓ E) ℓ g K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj
      (Profinite.padicIntegersRingObj ℓ E) ℓ g' K)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ sq)
    ?_ K ?_
  · intro N
    rw [boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison,
      pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  · convert hres using 3
    all_goals rfl

/-- **Proper base change on the ambient derived categories** (blueprint
`proposition-proper-direct-image-constructible-complexes` (3), for `𝒪_E`-coefficients): for a
cartesian square `g' ≫ f = f' ≫ g` of separated `k`-schemes of finite type with `f` proper, the base
change map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` of the ambient derived categories of module objects over
`𝒪̲_E` is an isomorphism for every bounded constructible `K`. As for `ℚ̄_ℓ`, the underlying square
of schemes is only required to be equal to the square of the underlying morphisms. -/
theorem isIso_baseChangeMap_app_padicIntegers_of_isProper [IsProper f.left]
    (sq : IsPullback g' f' f g) {S T S' T' : Scheme.{u}} {p : S ⟶ T} {q : T' ⟶ T} {p' : S' ⟶ T'}
    {q' : S' ⟶ S} (sq' : CommSq q' p' p q) (hS : X.left = S) (hT : Y.left = T)
    (hS' : X'.left = S') (hT' : Y'.left = T') (hp : HEq f.left p) (hq : HEq g.left q)
    (hp' : HEq f'.left p') (hq' : HEq g'.left q')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) S)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) S) K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq').app K) := by
  subst hS hT hS' hT'
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq hp'
  obtain rfl := eq_of_heq hq'
  obtain ⟨K, rfl⟩ : ∃ K' : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧, K'.obj = K :=
    ⟨⟨K, hK⟩, rfl⟩
  have h := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E sq
  rw [PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight] at h
  exact isIso_baseChangeMap_app_of_isIso_boundedConstructibleExchangeRight_padicIntegers ℓ E
    sq.toCommSq sq' K (NatIso.isIso_app_of_isIso _ K)

end AlgebraicGeometry.ProEtale.CondensedRing
