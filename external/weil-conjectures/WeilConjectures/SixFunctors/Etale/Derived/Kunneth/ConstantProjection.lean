/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyLargeFilteredColimit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGEInt
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant

/-!
# Tensoring derived global sections with a constant complex

Let `X` be a quasi-compact quasi-separated scheme. For `E ∈ D⁺(X_ét)` and `K ∈ D⁺(ℤ)`, the
canonical map `RΓ(X_ét, E) ⊗ᴸ K ⟶ RΓ(X_ét, E ⊗ᴸ K_X)` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_constantProjectionMap_of_isGE_int`, blueprint
`corollary-open-direct-image-over-field--2`, [Stacks 0F0E]). More generally this holds over any
principal ideal domain
(`AlgebraicGeometry.Etale.isIso_constantProjectionMap_of_isPrincipalIdealRing`). Abelian sheaves are
sheaves of modules over `ULift ℤ`, and the map is `AlgebraicGeometry.Etale.constantProjectionMap`.

More generally, for any commutative ring `Λ`, the map is an isomorphism for `E` bounded below
and `K` of Tor amplitude in `[b, ∞)`
(`AlgebraicGeometry.Etale.isIso_constantProjectionMap_of_torAmplitudeGE`): it is the projection
map of the adjunction `c_X ⊣ RΓ_X`, which is an isomorphism at flat modules placed in degree `0`
because `RᵠΓ(X, -)` commutes with filtered colimits on a qcqs scheme, hence at every `K` of Tor
amplitude bounded below
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE`).
Over a principal ideal domain such as `ℤ`, every `K ∈ D^{≥ b}` has Tor amplitude in `[b - 1, ∞)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory DerivedCategory

-- `derivedTensor` uses the braiding of the coefficients coming from their symmetric structure;
-- the braiding of `ModuleCat` found by instance search is a different term, expensive to unify.
attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry.Etale

/-- Replace the natural transformation `σ` in `(σ.app X).app Y` by `τ = σ`, at the level of
natural transformations: the kernel then compares `σ` and `τ` and not their components. -/
private lemma app_app_eq_of_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} {τ : F ⟶ G} {X : C} {Y : D} (σ : F ⟶ G) (hσ : σ = τ) :
    (σ.app X).app Y = (τ.app X).app Y :=
  hσ ▸ rfl

section Coefficients

-- The coefficients of interest are `ModuleCat.{u + 1} Λ : Type (u + 2)`. For a coefficient type
-- in an arbitrary universe the kernel check of the defining equation below times out.
variable (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (W : Scheme.{u})
  [(constantSheaf W.smallEtaleTopology A).PreservesFlat]

/-- The derived tensor comparison of the constant sheaf functor at `M`, `N`. The equation is
proved at the level of natural transformations: the instance proofs abstracted in
`AlgebraicGeometry.Etale.leftDerivedConstantSheafTensorComparison` differ from the ones elaborated
here, and comparing the components directly unfolds the derived tensor comparison. -/
lemma leftDerivedConstantSheafTensorComparison_eq (M N : DerivedCategory A) :
    leftDerivedConstantSheafTensorComparison A W M N =
      ((constantSheaf W.smallEtaleTopology A).leftDerivedTensorComparison.app M).app N :=
  app_app_eq_of_eq _ rfl

/-- The constant-tensor comparison `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` is the projection map of
the adjunction `c_W ⊣ RΓ_W` (`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`). -/
lemma derivedConstantSheafProjectionMap_eq (K : DerivedCategory (Sheaf W.smallEtaleTopology A))
    (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M =
      (Functor.mapDerivedCategoryProjectionMap (derivedConstantSheafAdjunction A W) K).app M := by
  rw [Functor.mapDerivedCategoryProjectionMap_app,
    Functor.mapDerivedCategoryTensorComparison_app_app]
  unfold derivedConstantSheafProjectionMap derivedConstantSheafHomEquiv
    derivedConstantSheafProjectionMapTranspose derivedConstantSheafTensorComparison
  rw [leftDerivedConstantSheafTensorComparison_eq]
  rfl

end Coefficients

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) [CompactSpace X]
  [QuasiSeparatedSpace X]

/-- On a quasi-compact quasi-separated scheme `X`, the constant-tensor comparison
`RΓ_X E ⊗ᴸ K ⟶ RΓ_X (E ⊗ᴸ c_X K)` is an isomorphism for `E` bounded below and `K` of Tor
amplitude in `[b, ∞)`. -/
theorem isIso_constantProjectionMap_of_torAmplitudeGE
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{u + 1} Λ)) (b : ℤ)
    (hK : torAmplitudeGE (ModuleCat.{u + 1} Λ) b K) :
    IsIso (constantProjectionMap Λ X E K) := by
  rw [constantProjectionMap, derivedConstantSheafProjectionMap_eq]
  let adj := derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X
  have hΓ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (q : ℕ) :
      PreservesColimitsOfShape J
        ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerived q) :=
    Scheme.preservesColimitsOfShape_rightDerived_Γ_moduleCat X J Λ q
  exact Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE (adj := adj)
    (fun Y n _ ↦ Functor.isGE_rightDerivedFunctor_obj _ Y n) E a
    (fun M hM ↦ Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat adj hΓ
      E a M hM) K b hK

/-- Over a principal ideal domain `Λ`, on a quasi-compact quasi-separated scheme `X`, the
constant-tensor comparison `RΓ_X E ⊗ᴸ K ⟶ RΓ_X (E ⊗ᴸ c_X K)` is an isomorphism for `E` and `K`
bounded below: every complex concentrated in degrees `≥ b` has Tor amplitude in `[b - 1, ∞)`. -/
theorem isIso_constantProjectionMap_of_isPrincipalIdealRing [IsDomain Λ] [IsPrincipalIdealRing Λ]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{u + 1} Λ)) (b : ℤ) [K.IsGE b] :
    IsIso (constantProjectionMap Λ X E K) :=
  isIso_constantProjectionMap_of_torAmplitudeGE Λ X E a K (b - 1)
    (torAmplitudeGE_of_isGE_of_isPrincipalIdealRing K b)

/-- Blueprint `corollary-open-direct-image-over-field--2`: tensor with a constant complex over `ℤ`
([Stacks 0F0E]).

Let `X` be a quasi-compact quasi-separated scheme. For `E ∈ D⁺(X_ét)` and `K ∈ D⁺(ℤ)`, the
canonical map `RΓ(X_ét, E) ⊗ᴸ_ℤ K ⟶ RΓ(X_ét, E ⊗ᴸ_ℤ K_X)`
(`AlgebraicGeometry.Etale.constantProjectionMap`) is an isomorphism. Abelian sheaves are
sheaves of modules over `ULift ℤ`. -/
theorem isIso_constantProjectionMap_of_isGE_int
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (a : ℤ) [E.IsGE a] (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (b : ℤ)
    [K.IsGE b] :
    IsIso (constantProjectionMap (ULift.{u + 1} ℤ) X E K) :=
  isIso_constantProjectionMap_of_torAmplitudeGE _ X E a K (b - 1)
    (torAmplitudeGE_of_isGE_int K b)

end AlgebraicGeometry.Etale
