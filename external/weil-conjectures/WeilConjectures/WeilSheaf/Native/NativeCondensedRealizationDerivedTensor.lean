/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTotalTensor
public import WeilConjectures.WeilSheaf.Native.NativePullKFlat
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization

/-!
# The derived condensed realization of the native tensor

For `X` separated, of finite type and quasi-compact over `k₀`, the derived condensed realization
`derivedCondensedRealization k₀ l X` carries the native derived tensor `nativeDerivedTensor` of
Weil complexes to the derived tensor product of condensed module objects on the geometric fibre:
```
condensedRealizationTensor k₀ l X :
  nativeDerivedTensor ⋙ derivedCondensedRealization ≅
    derivedCondensedRealization.prod derivedCondensedRealization ⋙ (- ⊗ᴸ -)
```
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor`).

It is normalized on native K-flat representatives `P`, `T`
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor_normalization`): it is the
localization of the totalization `condensedRealizationTotalTensorIso` of the sheaf-level
comparison `condensedRealizationSheafTensorIso`, composed with the native K-flat model
`nativeOpenTensorModel` and the condensed K-flat model `condensedTensorModel`, the lax monoidal
structure of `DerivedCategory.Q` (invertible on K-flat complexes). The totalization is fixed on
each summand (`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTotalTensorIso_summand`).

The construction is the generic descent
`NativeRestrictionDescentProof.restriction_derived_representative` along the full localization of
native K-flat complexes, the condensed realization preserving K-flatness
(`AlgebraicGeometry.ProEtaleWeilSheaf.kFlat_condensedRealization`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

section

attribute [-instance] Endofunctor.IsoAlgebra.instPreadditive Mod.instPreadditive

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero

/-- The totalized sheaf comparison `condensedRealizationTotalTensorIso`, with source and target
written through the descent input `condensedRealizationTensorInput`. -/
def condensedRealizationTensorInputTotalIso :
    Functor.uncurry.obj (condensedRealizationTensorInput k₀ l X).TB ⋙
        (condensedRealizationTensorInput k₀ l X).R.mapHomologicalComplex (.up ℤ) ≅
      ((condensedRealizationTensorInput k₀ l X).R.mapHomologicalComplex (.up ℤ)).prod
          ((condensedRealizationTensorInput k₀ l X).R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (condensedRealizationTensorInput k₀ l X).TA :=
  condensedRealizationTotalTensorIso k₀ l X

/-- The normalization of a comparison `rho` between the derived condensed realization of the
native derived tensor and the derived tensor of the realizations: on native K-flat
representatives `P`, `T` it is the localization of the totalized sheaf comparison
`condensedRealizationTotalTensorIso`, composed with the native K-flat model
`nativeOpenTensorModel` and the condensed K-flat model `condensedTensorModel`. -/
def CondensedRealizationTensorNormalization
    (rho : (condensedRealizationTensorInput k₀ l X).DB ⋙
        (condensedRealizationTensorInput k₀ l X).R.mapDerivedCategory ≅
      (condensedRealizationTensorInput k₀ l X).R.mapDerivedCategory.prod
          (condensedRealizationTensorInput k₀ l X).R.mapDerivedCategory ⋙
        (condensedRealizationTensorInput k₀ l X).DA) : Prop :=
  OpenTensorRestrictionNormalization (condensedRealizationTensorInput k₀ l X).R
    (condensedRealizationTensorInput k₀ l X).TA (condensedRealizationTensorInput k₀ l X).TB
    (condensedRealizationTensorInput k₀ l X).DA (condensedRealizationTensorInput k₀ l X).DB
    (condensedRealizationTensorInput k₀ l X).flatA (condensedRealizationTensorInput k₀ l X).flatB
    (kFlat_condensedRealization k₀ l X) (condensedRealizationTensorModels k₀ l X).modelA
    (condensedRealizationTensorModels k₀ l X).modelB
    (fun P T ↦ (condensedRealizationTensorInputTotalIso k₀ l X).app (P, T)) rho

/-- The derived condensed realization of the native derived tensor exists, normalized on native
K-flat representatives by the totalized sheaf comparison and the native and condensed K-flat
models: the generic restriction descent along the native K-flat localization. -/
theorem exists_condensedRealizationTensor :
    ∃ rho, CondensedRealizationTensorNormalization k₀ l X rho := by
  let c := condensedRealizationTensorInput k₀ l X
  have : ((ObjectProperty.ι c.flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (ObjectProperty.ι c.flatB)) :=
    native_open_tensor_full_kflat_localization k₀ l X
  exact NativeRestrictionDescentProof.restriction_derived_representative.{u + 2, u + 1}
    (A := Mod (Sheaf (Scheme.ProEt.topology
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) (B := ProEtaleWeilSheaf k₀ l X) c
    (condensedRealizationTensorModels k₀ l X) (kFlat_condensedRealization k₀ l X)
    (condensedTensorModel_naturality k₀ l X)
    (native_normalized_tensor_models k₀ l X).choose_spec.1
    (condensedRealizationTensorInputTotalIso k₀ l X)

end

/-- **The derived condensed realization of the native tensor.** The derived condensed realization
carries the native derived tensor of pro-étale Weil complexes on `X` to the derived tensor product
`- ⊗ᴸ -` of condensed module objects on the geometric fibre `X̄`
(`ProEtale.CondensedRing.derivedTensor` is `curriedTensor` of this derived category). It is the
descent of the totalized sheaf comparison along the native K-flat localization, see
`condensedRealizationTensor_normalization`. -/
def condensedRealizationTensor :
    nativeDerivedTensor k₀ l X ⋙ derivedCondensedRealization k₀ l X ≅
      (derivedCondensedRealization k₀ l X).prod (derivedCondensedRealization k₀ l X) ⋙
        Functor.uncurry.obj (curriedTensor _) :=
  (exists_condensedRealizationTensor k₀ l X).choose

/-- On native K-flat representatives `P`, `T`, the comparison `condensedRealizationTensor` is the
localization of the totalization `condensedRealizationTotalTensorIso` of the sheaf-level
comparison, composed with the native K-flat model `nativeOpenTensorModel` and the condensed
K-flat model `condensedTensorModel` (the lax monoidal structure of `DerivedCategory.Q`). -/
theorem condensedRealizationTensor_normalization :
    CondensedRealizationTensorNormalization k₀ l X (condensedRealizationTensor k₀ l X) :=
  (exists_condensedRealizationTensor k₀ l X).choose_spec

/-- The normalization of `condensedRealizationTensor` on native K-flat representatives `P`, `T`,
written out: after the exact-functor factors of the derived condensed realization and the
condensed K-flat model, it is the realization of the native K-flat model followed by the
localization of the totalized sheaf comparison. -/
theorem condensedRealizationTensor_hom_app_comp
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T) :
    (condensedRealizationTensor k₀ l X).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom ((condensedRealization k₀ l X).mapDerivedCategoryFactors.hom.app P)
          ((condensedRealization k₀ l X).mapDerivedCategoryFactors.hom.app T)) ≫
      (condensedTensorModel k₀ l X _ _ (kFlat_condensedRealization k₀ l X P hP)
        (kFlat_condensedRealization k₀ l X T hT)).hom =
    (derivedCondensedRealization k₀ l X).map (nativeOpenTensorModel k₀ l X P T hP hT).hom ≫
      (condensedRealization k₀ l X).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((condensedRealizationTotalTensorIso k₀ l X).app (P, T)).hom :=
  condensedRealizationTensor_normalization k₀ l X P T hP hT

end AlgebraicGeometry.ProEtaleWeilSheaf
