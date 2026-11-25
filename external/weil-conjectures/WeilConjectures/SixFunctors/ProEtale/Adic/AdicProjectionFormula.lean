/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicProjectionFormulaAux
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarKFlat

/-!
# The proper projection formula for `ℓ`-adic sheaves

Let `f : X ⟶ Y` be a morphism of schemes. The projection map of `ℓ`-adic sheaves is the right
adjoint projection map (`CategoryTheory.Adjunction.rightAdjointProjectionMap`)
`Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ f^* M)` of the derived adjunction `D(f^*) ⊣ Rf_*` of
`AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction`, for the tensor comparison
`D(f^*)(K ⊗ᴸ M) ⟶ D(f^*) K ⊗ᴸ D(f^*) M` of the exact strong monoidal functor `f^*`
(`CategoryTheory.Functor.mapDerivedCategoryTensorComparison`).

We transport the invertibility of the projection map from the condensed model
(`AlgebraicGeometry.ProEtale.CondensedRing.projectionMap`) along the equivalence
`E : AdicSheaf ℓ ≌ Mod_{Λ}` of the two models
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`):

* `AlgebraicGeometry.ProEtale.isIso_adicProjectionMap_of_isIso`: if `E_X`, `E_Y` and `f^*` carry
  strong monoidal structures for which the pullback compatibility
  `f^* ⋙ E_X ≅ E_Y ⋙ f^*` (`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`) is
  monoidal, then the `ℓ`-adic projection map at `(K, M)` is invertible as soon as the condensed
  projection map is invertible at `(LE_X K, LE_Y M)`. This uses
  `CategoryTheory.Adjunction.isIso_map_rightAdjointProjectionMap_of_mateEquiv`, the compatibility
  of the tensor comparisons of left derived functors along a monoidal square
  (`CategoryTheory.Functor.comparisonCompatible_leftDerivedTensorComparison`), and the fact that
  the base change maps are invertible, `E` being an equivalence.
* `AlgebraicGeometry.ProEtale.adicUpperStarMonoidalOfCondensed`: a strong monoidal structure on
  the pullback
  `f^*` of `ℓ`-adic sheaves for which the pullback compatibility is monoidal, transported from the
  condensed model along `E` (`CategoryTheory.Equivalence.monoidalOfPostcompFunctor`), where `E`
  carries the strong monoidal structure `AlgebraicGeometry.ProEtale.condensedModFunctorMonoidal`
  of forgetting ambient scalars (`AlgebraicGeometry.ProEtale.nativeScalarForgetting_monoidal`).
* `AlgebraicGeometry.ProEtale.isIso_adicProjectionMap_of_isProper`: **the proper projection
  formula** for this monoidal structure: for `f` proper between separated schemes of finite type
  over a field `k` of characteristic `≠ ℓ` and `K`, `M` whose condensed models are bounded
  constructible, the `ℓ`-adic projection map at `(K, M)` is an isomorphism.

## Implementation notes

The monoidal structure of `AlgebraicGeometry.ProEtale.adicUpperStarMonoidalOfCondensed` is not
shown to be
the one induced by the strong monoidal structure of the pullback of the underlying sheaves of
`ℚ̄_ℓ`-modules; `AlgebraicGeometry.ProEtale.isIso_adicProjectionMap_of_isIso` applies to any
strong monoidal structure on `f^*` for which the pullback compatibility is monoidal.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

local notation "𝐐" => Profinite.padicAlgClRingObj l

/-! ### Monoidal structures -/

/-- A strong monoidal structure on the comparison functor `E_X : AdicSheaf ℓ X ⥤ Mod_{Λ_X}` of the
two models: forgetting ambient scalars
(`AlgebraicGeometry.ProEtale.nativeScalarForgetting_monoidal`)
followed by restriction of scalars along an isomorphism of ring objects. -/
@[instance_reducible]
noncomputable def condensedModFunctorMonoidal (X : Scheme.{u}) :
    (adicSheafEquivCondensedMod l X).functor.Monoidal :=
  letI := Classical.choice (nativeScalarForgetting_monoidal l X)
  inferInstanceAs
    (AdicSheaf.forgetAb l X ⋙ Mod.comap (condensedRingObjIsoForgetAb l X).hom).Monoidal

variable {l} {X Y : Scheme.{u}} (f : X ⟶ Y)

instance : (f)^*ᵃ[l].IsLeftAdjoint := (adicUpperStarLowerStarAdjunction l f).isLeftAdjoint

/-- A strong monoidal structure on the pullback `f^*` of `ℓ`-adic sheaves, transported from the
pullback of module objects over the condensed coefficient ring along the comparison
`f^* ⋙ E_X ≅ E_Y ⋙ f^*` of the two models
(`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`). -/
@[instance_reducible]
noncomputable def adicUpperStarMonoidalOfCondensed : (f)^*ᵃ[l].Monoidal :=
  letI := condensedModFunctorMonoidal l X
  letI := condensedModFunctorMonoidal l Y
  letI := (adicSheafEquivCondensedMod l X).inverseMonoidal
  (adicSheafEquivCondensedMod l X).monoidalOfPostcompFunctor _
    (adicUpperStarCompCondensedModIso l f)

/-- The comparison `f^* ⋙ E_X ≅ E_Y ⋙ f^*` of the two models is monoidal for
`AlgebraicGeometry.ProEtale.adicUpperStarMonoidalOfCondensed`. -/
lemma isMonoidal_adicUpperStarCompCondensedModIso_hom :
    letI := condensedModFunctorMonoidal l X
    letI := condensedModFunctorMonoidal l Y
    letI := adicUpperStarMonoidalOfCondensed (l := l) f
    NatTrans.IsMonoidal (adicUpperStarCompCondensedModIso l f).hom := by
  let := condensedModFunctorMonoidal l X
  let := condensedModFunctorMonoidal l Y
  exact (adicSheafEquivCondensedMod l X).isMonoidal_monoidalOfPostcompFunctor _
    (adicUpperStarCompCondensedModIso l f)

/-! ### Transport of the projection formula -/

section Transport

variable [(adicSheafEquivCondensedMod l X).functor.Monoidal]
  [(adicSheafEquivCondensedMod l Y).functor.Monoidal] [(f)^*ᵃ[l].Monoidal]
  [NatTrans.IsMonoidal (adicUpperStarCompCondensedModIso l f).hom]

-- unifying the generic derived-category lemmas with the module-object instances is slow
/-- The `ℓ`-adic projection map at `(K, M)` is invertible as soon as the condensed projection
map is invertible at the images of `K` and `M` under the left derived functors of the
comparisons `E` of the two models. -/
theorem isIso_adicProjectionMap_of_isIso
    (K : DerivedCategory (AdicSheaf l X)) (M : DerivedCategory (AdicSheaf l Y))
    (h : IsIso (((CondensedRing.projectionMap 𝐐 f).app
      ((adicSheafEquivCondensedMod l X).functor.leftDerivedFunctor.obj K)).app
        ((adicSheafEquivCondensedMod l Y).functor.leftDerivedFunctor.obj M))) :
    IsIso (((((adicUpperStarLowerStarAdjunction l f).mapDerivedCategoryRightDerivedAdjunction
      ).rightAdjointProjectionMap (f)^*ᵃ[l].mapDerivedCategoryTensorComparison).app K).app M) := by
  let EX := (adicSheafEquivCondensedMod l X).functor
  let EY := (adicSheafEquivCondensedMod l Y).functor
  have : EX.PreservesFlat := EX.preservesFlat_of_isEquivalence
  have : EY.PreservesFlat := EY.preservesFlat_of_isEquivalence
  let α := (Functor.leftDerivedFunctorCompNatIso EY (CondensedRing.upperStar 𝐐 f) (f)^*ᵃ[l] EX
      (adicUpperStarCompCondensedModIso l f)).symm ≪≫
    Functor.isoWhiskerRight (f)^*ᵃ[l].leftDerivedFunctorIsoMapDerivedCategory
      EX.leftDerivedFunctor
  have H : Adjunction.ComparisonCompatible α (f)^*ᵃ[l].mapDerivedCategoryTensorComparison
      (CondensedRing.leftDerivedUpperStarTensor 𝐐 f) (asIso EX.leftDerivedTensorComparison)
      (asIso EY.leftDerivedTensorComparison) := by
    rw [CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
    exact Functor.comparisonCompatible_mapDerivedCategoryTensorComparison EY
      (CondensedRing.upperStar 𝐐 f) (f)^*ᵃ[l] EX (adicUpperStarCompCondensedModIso l f)
  let adjX := EX.leftDerivedFunctor.asEquivalence.toAdjunction
  let adjY := EY.leftDerivedFunctor.asEquivalence.toAdjunction
  have hβ (Z : DerivedCategory (AdicSheaf l X)) := Adjunction.isIso_mateEquiv_app_of_isIso
    ((adicUpperStarLowerStarAdjunction l f).mapDerivedCategoryRightDerivedAdjunction)
    (CondensedRing.derivedUpperStarLowerStarAdjunction 𝐐 f) α adjY adjX Z
  have := Adjunction.isIso_map_rightAdjointProjectionMap_of_mateEquiv
    ((adicUpperStarLowerStarAdjunction l f).mapDerivedCategoryRightDerivedAdjunction)
    (CondensedRing.derivedUpperStarLowerStarAdjunction 𝐐 f) H K M h (hβ K) (hβ _)
  exact isIso_of_reflects_iso _ EY.leftDerivedFunctor

end Transport

/-! ### The proper projection formula -/

/-- **The proper projection formula for `ℓ`-adic sheaves**: for a proper morphism `f : X ⟶ Y` of
separated schemes of finite type over a field `k` of characteristic `≠ ℓ`, and `K`, `M` whose
images in the condensed model are bounded constructible, the projection map
`Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ f^* M)` of `ℓ`-adic sheaves is an isomorphism, for the strong monoidal
structure `AlgebraicGeometry.ProEtale.adicUpperStarMonoidalOfCondensed` on `f^*`. -/
theorem isIso_adicProjectionMap_of_isProper {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ l)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (K : DerivedCategory (AdicSheaf l X.left)) (M : DerivedCategory (AdicSheaf l Y.left))
    (hK : boundedConstructible (condensedRingObj 𝐐 X.left)
      ((adicSheafDerivedEquivCondensedMod l X.left).functor.obj K))
    (hM : boundedConstructible (condensedRingObj 𝐐 Y.left)
      ((adicSheafDerivedEquivCondensedMod l Y.left).functor.obj M)) :
    letI := adicUpperStarMonoidalOfCondensed (l := l) f.left
    IsIso (((((adicUpperStarLowerStarAdjunction l f.left).mapDerivedCategoryRightDerivedAdjunction
      ).rightAdjointProjectionMap (f.left)^*ᵃ[l].mapDerivedCategoryTensorComparison).app K).app
        M) := by
  let := condensedModFunctorMonoidal l X.left
  let := condensedModFunctorMonoidal l Y.left
  let := adicUpperStarMonoidalOfCondensed (l := l) f.left
  have := isMonoidal_adicUpperStarCompCondensedModIso_hom (l := l) f.left
  refine isIso_adicProjectionMap_of_isIso f.left K M ?_
  exact (CondensedRing.properDirectImage_baseChange_projectionFormula_padicAlgClRingObj l
    (X' := X) (Y' := Y) f).2.2 _ _
    ((boundedConstructible _).prop_of_iso
      ((adicSheafEquivCondensedMod l X.left).functor.leftDerivedFunctorIsoMapDerivedCategory.app
        K).symm hK)
    ((boundedConstructible _).prop_of_iso
      ((adicSheafEquivCondensedMod l Y.left).functor.leftDerivedFunctorIsoMapDerivedCategory.app
        M).symm hM)

end AlgebraicGeometry.ProEtale
