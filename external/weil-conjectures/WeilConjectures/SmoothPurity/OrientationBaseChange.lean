/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.SmoothPurity.EtaleReductionProperBaseChange
public import WeilConjectures.SmoothPurity.UpperShriekBaseChangeReduction
public import WeilConjectures.TraceFormula.PurityTensorMap

/-!

# Compatibility of the smooth orientation with base change

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type. The orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`) is compatible with base change:
pulled back along `g'` and followed by the exceptional base change map
`Lg'^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekBaseChange`), it is the orientation of
`f'`, up to an isomorphism `Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists.

This is a property of the definition `smoothOrientation` of
`WeilConjectures.SmoothPurity.Defs`: the compatibility of smooth purity with base change
(`u^*γ_f(K) = γ_{f'}(v^*K)`) at the unit
`K = ℚ̄_ℓ,Y`, owed by the smooth purity section. It is proved here as
`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation_baseChange`, from smooth base
change for `Rf^!` and the compatibility of the reduction modulo `ℓ` with proper base change; the
base change compatibilities of the smooth trace and of the purity map are derived from it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Criterion for the base change of the orientation**: since the isomorphism `τ` of
`smoothOrientation_baseChange` is not prescribed, the compatibility holds as soon as the
orientation `γ_{f'}` and the base changed orientation
`Lg'^* ℚ̄_ℓ,X(d)[2d] ⟶ Lg'^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'` are isomorphisms;
`τ` is then the composite of the second with the inverse of the first. Both conditions can be
checked after reduction to finite coefficients, which is how `smoothOrientation_baseChange` is
meant to be proved. -/
theorem smoothOrientation_baseChange_of_isIso (sq : IsPullback g' f' f g) (d : ℕ)
    (h₁ : IsIso (smoothOrientation ℓ f' d))
    (h₂ : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothOrientation ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))) :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothOrientation ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothOrientation ℓ f' d := by
  refine ⟨@asIso _ _ _ _ _ h₂ ≪≫ (@asIso _ _ _ _ _ h₁).symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- **Base change of the orientation, given the compatibility of the reduction modulo `ℓ` with
proper base change**: the orientations `γ_f` and `γ_{f'}` are isomorphisms
(`isIso_smoothOrientation`), the exceptional base change map at the unit is an isomorphism by
smooth base change (`isIso_upperShriekBaseChange_of_smooth_of_etaleReductionProperCompatibleAll`)
and `Lg^* ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,Y'`, so `smoothOrientation_baseChange_of_isIso` applies. -/
theorem smoothOrientation_baseChange_of_etaleReductionProperBaseChangeCompatibleAll
    (hcompat : EtaleReductionProperBaseChangeCompatibleAll ℓ k) (sq : IsPullback g' f' f g)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothOrientation ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothOrientation ℓ f' d := by
  have := SmoothOfRelativeDimension.smooth d f.left
  have := isIso_upperShriekBaseChange_of_smooth_of_etaleReductionProperCompatibleAll ℓ hcompat sq
    (𝟙_ _)
  exact smoothOrientation_baseChange_of_isIso ℓ sq d inferInstance inferInstance

/-- Blueprint `proposition-compatibility-purity-base-change` at the unit (owed by the smooth purity
section, `chap-Smooth-purity`): **the orientation is compatible with base change**. For a
cartesian square with `f` (hence `f'`) smooth of pure relative dimension `d`, the pullback of the
orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, followed by the exceptional base change map at the
unit and `Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'`, is the orientation `γ_{f'}` up to an isomorphism
`Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists:
```
Lg'^* ℚ̄_ℓ,X(d)[2d] --Lg'^* γ_f--> Lg'^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'.
```
It follows from smooth base change for `Rf^!`, through the compatibility of the reduction modulo
`ℓ` with proper base change (`etaleReductionProperBaseChangeCompatibleAll`). -/
theorem smoothOrientation_baseChange (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothOrientation ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothOrientation ℓ f' d :=
  smoothOrientation_baseChange_of_etaleReductionProperBaseChangeCompatibleAll ℓ
    (etaleReductionProperBaseChangeCompatibleAll ℓ k) sq d

end AlgebraicGeometry.ProEtale.CondensedRing
