/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMateReflect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaProperField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldDerivedMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# The projection formula for bounded constructible `𝒪_E`-complexes

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and let `p : X ⟶ Y` be a proper morphism of separated `k`-schemes of finite type. This file
proves the projection formula of blueprint `proposition-proper-direct-image-constructible-complexes`
(3): the projection map `Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism for bounded
constructible `𝒪_E`-complexes `K` and `M`
(`ProEtale.CondensedRing.isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible`).

Both sides are bounded constructible, so by derived Nakayama
(`ProEtale.isIso_of_isIso_derivedReduction_map`) it suffices that the first derived reduction
`- ⊗ᴸ_{𝒪_E} 𝔽_E` of the projection map is an isomorphism. This reduction is computed in two
steps:

* the derived extension of scalars `T = L(Ext)` along the residue map `𝒪̲_E ⟶ 𝔽̲_E` carries the
  projection map with coefficients `𝒪̲_E` to the one with coefficients `𝔽̲_E`, up to the (Pull)
  isomorphism, which is monoidal (`comparisonCompatible_derivedUpperStarExtendScalarsIso`), and
  the (Push) comparison, invertible on bounded below complexes
  (`isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`);
* the equivalence `D(G)` between module objects over `𝔽̲_E` and pro-étale sheaves of
  `𝔽_E`-modules carries it to the projection map of pro-étale sheaves of `𝔽_E`-modules
  (`exists_comparisonCompatible_residueFieldDerivedUpperStarIso`,
  `isIso_residueFieldDerivedPushHom`).

The latter is an isomorphism at the reductions of bounded constructible complexes, by the
proper projection formula over the finite field `𝔽_E`
(`ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_boundedConstructible_of_field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section Reduction

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived extension of scalars `T` along the residue map `𝒪̲_E ⟶ 𝔽̲_E` carries the projection
map with coefficients `𝒪̲_E` at `(K, M)` to an isomorphism, as soon as the projection map with
coefficients `𝔽̲_E` is an isomorphism at the reductions `(T K, T M)` and `K` and `K ⊗ᴸ Lf^* M`
are bounded below. -/
lemma isIso_map_projectionMap_derivedExtendScalars_residueField
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y)))
    (n m : ℤ) (hn : K.IsGE n)
    (hm : (((curriedTensor _).obj K).obj
      (((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).leftDerivedFunctor.obj M)).IsGE m)
    (h : IsIso (((projectionMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
      f).app ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj
        K)).app ((Mod.extendScalars (padicIntegersToResidueField Y ℓ E)).leftDerivedFunctor.obj
          M))) :
    IsIso ((Mod.extendScalars (padicIntegersToResidueField Y ℓ E)).leftDerivedFunctor.map
      (((projectionMap (Profinite.padicIntegersRingObj ℓ E) f).app K).app M)) :=
  Adjunction.isIso_map_rightAdjointProjectionMap_of_mateEquiv
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f)
    (derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
    (comparisonCompatible_derivedUpperStarExtendScalarsIso
      (Profinite.padicIntegersRingObjToResidueField ℓ E) f) K M h
    (isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f K n)
    (isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f _ m)

/-- The projection map with coefficients `𝔽̲_E` at `(A, B)` is an isomorphism as soon as the
projection map of pro-étale sheaves of `𝔽_E`-modules is an isomorphism at `(D(G) A, D(G) B)`. -/
lemma isIso_projectionMap_residueField_of_moduleCat
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) X)))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y)))
    (h : IsIso (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f).app
        ((residueFieldModuleSheaf X ℓ E).mapDerivedCategory.obj A)).app
        ((residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.obj B))) :
    IsIso (((projectionMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
      f).app A).app B) := by
  obtain ⟨m_X, m_Y, H⟩ := exists_comparisonCompatible_residueFieldDerivedUpperStarIso ℓ E f
  have := Adjunction.isIso_map_rightAdjointProjectionMap_of_mateEquiv
    (derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction _ f) H A B h
    (NatIso.isIso_app_of_isIso (residueFieldDerivedPushHom ℓ E f) A)
    (NatIso.isIso_app_of_isIso (residueFieldDerivedPushHom ℓ E f) _)
  have : IsIso ((residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.map
      (((projectionMap (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f).app
        A).app B)) := this
  exact isIso_of_reflects_iso _ (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory

end Reduction

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The residue field `𝔽_E`, lifted to the universe of the pro-étale coefficients, is a field. -/
lemma isField_residueFieldCoeff : IsField (ResidueFieldCoeff.{u} ℓ E) :=
  MulEquiv.isField (Field.toIsField (integersResidueField ℓ E)) ULift.ringEquiv.toMulEquiv

instance : Finite (ResidueFieldCoeff.{u} ℓ E) :=
  inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E)))

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The projection formula for `𝒪_E`** (blueprint
`proposition-proper-direct-image-constructible-complexes` (3)): for a proper `p : X ⟶ Y` and bounded
constructible `𝒪_E`-complexes `K` on `X` and `M` on `Y`, the projection map
`Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism. -/
theorem isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible (p : X ⟶ Y)
    [IsProper p.left]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)))
    (hK : boundedConstructible _ K) (hM : boundedConstructible _ M) :
    IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y.hom
  have hKM := (PadicIntegersRingObj.isMonoidal_boundedConstructible ℓ E X).toTensorLE.prop_tensor
    _ _ hK (boundedConstructible_leftDerivedUpperStar_obj _ ℓ p ⟨M, hM⟩)
  have hL := (PadicIntegersRingObj.isMonoidal_boundedConstructible ℓ E Y).toTensorLE.prop_tensor
    _ _ (PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj_of_isProper ℓ E p
      ⟨K, hK⟩) hM
  have hR := PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj_of_isProper ℓ E p
    ⟨_, hKM⟩
  -- the projection map over `𝔽_E` at the reductions
  have hC := isIso_rightDerivedLowerStarProjectionMap_app_app_of_boundedConstructible_of_field
    (ResidueFieldCoeff.{u} ℓ E) (isField_residueFieldCoeff ℓ E) p.left
    (boundedConstructible_derivedReduction_obj X.left ℓ E K hK)
    (boundedConstructible_derivedReduction_obj Y.left ℓ E M hM)
  have h𝔽 := isIso_projectionMap_residueField_of_moduleCat ℓ E p.left _ _ hC
  have hT := isIso_map_projectionMap_derivedExtendScalars_residueField ℓ E p.left K M
    (exists_isGE_of_boundedConstructible hK).choose
    (exists_isGE_of_boundedConstructible hKM).choose
    (exists_isGE_of_boundedConstructible hK).choose_spec
    (exists_isGE_of_boundedConstructible hKM).choose_spec h𝔽
  have hD : IsIso ((residueFieldModuleSheaf Y.left ℓ E).mapDerivedCategory.map
      ((Mod.extendScalars (padicIntegersToResidueField Y.left ℓ E)).leftDerivedFunctor.map
        (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M))) :=
    Functor.map_isIso _ _
  let φ : (⟨_, hL⟩ : BoundedConstructible _) ⟶ ⟨_, hR⟩ :=
    ObjectProperty.homMk (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M)
  have hφ : IsIso φ := isIso_of_isIso_derivedReduction_map Y.left ℓ E φ hD
  exact Functor.map_isIso (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)).ι φ

end AlgebraicGeometry.ProEtale.CondensedRing
