/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleComplex
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible

/-!
# Derived scalar extension preserves `Dᵇctf`

Let `R ⟶ S` be a homomorphism of finite commutative rings whose exponent is invertible on a
scheme `X` of finite type over a field. Derived extension of scalars
`Ψ = - ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` carries bounded constructible complexes of finite
Tor amplitude to bounded constructible complexes of finite Tor amplitude (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`).

The proof goes through flat models. A complex `K ∈ Dᵇctf(X_proét, R)` is `ν^* K'` for some
`K' ∈ Dᵇctf(X_ét, R)`, and `K'` is quasi-isomorphic to a bounded complex `P` of flat
constructible sheaves
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`).
Then `ν^* P` is a bounded above complex of flat sheaves, hence K-flat, so `Ψ K` is computed
by the underived extension of scalars `S ⊗_R ν^* P ≅ ν^*(S ⊗_R P)`. The complex `S ⊗_R P` is a
bounded complex of flat constructible étale sheaves
(`AlgebraicGeometry.ProEtale.flat_etaleSheafExtendScalars_obj`,
`AlgebraicGeometry.ProEtale.isConstructibleSheaf_etaleSheafExtendScalars_obj`), so it lies in
`Dᵇctf(X_ét, S)` (`AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_Q_obj`), and
`ν^*` carries it into `Dᵇctf(X_proét, S)`.

## Main results

- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_leftDerivedSheafExtendScalars`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]

/-- **Derived scalar extension preserves `Dᵇctf`** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`): for a homomorphism `R ⟶ S` of finite rings whose
exponent is invertible on a scheme `X` of finite type over a field, `K ⊗ᴸ_R S` is bounded
constructible of finite Tor amplitude whenever `K` is. -/
theorem constructibleFiniteTor_leftDerivedSheafExtendScalars {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent R X]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  obtain ⟨⟨K', hK', ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X (min a b) b K' :=
    ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) X a b).prop_of_iso e.symm ht)).mono
        (min_le_left _ _) le_rfl
  obtain ⟨Pc, ⟨hPz, hPflat⟩, hPc, ⟨e'⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel R (min a b) b (min_le_right _ _)
      K' hK').1 (Etale.hasTorAmplitudeIn_of_torAmplitudeIn ht')
  have : Pc.IsStrictlyGE (min a b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hPz i (.inl hi)
  have : Pc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hPz i (.inr hi)
  let NR := ν^*(X)[ModuleCat.{u + 1} R]
  let NS := ν^*(X)[ModuleCat.{u + 1} S]
  let E := sheafExtendScalars (algebraMap R S) X
  let Ee := etaleSheafExtendScalars (algebraMap R S) X
  -- the pro-étale flat model `ν^* Pc` of `K`
  let Pp := (NR.mapHomologicalComplex (.up ℤ)).obj Pc
  have : CochainComplex.IsStrictlyLE Pp b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _ _ b).2 inferInstance
  have hPp := CochainComplex.kFlat_of_isStrictlyLE_of_flat Pp b
    (fun n ↦ flat_comparisonUpperStar_obj (hPflat n))
  let eK : DerivedCategory.Q.obj Pp ≅ K :=
    (NR.mapDerivedCategoryFactors.app Pc).symm ≪≫ NR.mapDerivedCategory.mapIso e'.symm ≪≫ e
  -- the étale complex `S ⊗_R Pc`
  let Pe := (Ee.mapHomologicalComplex (.up ℤ)).obj Pc
  let eP : (E.mapHomologicalComplex (.up ℤ)).obj Pp ≅
      (NS.mapHomologicalComplex (.up ℤ)).obj Pe :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ ((etaleSheafExtendScalarsCompComparisonUpperStarIso (algebraMap R S) X).app
        (Pc.X n)).symm)
      (fun i j _ ↦ ((etaleSheafExtendScalarsCompComparisonUpperStarIso (algebraMap R S)
        X).inv.naturality (Pc.d i j)).symm)
  have := E.isIso_leftDerivedFunctorCounit_app_of_kFlat Pp hPp
  let eL : (L(E)).obj K ≅ NS.mapDerivedCategory.obj (DerivedCategory.Q.obj Pe) :=
    (L(E)).mapIso (eK.symm ≪≫ ((DerivedCategory.quotientCompQhIso _).app Pp).symm) ≪≫
      asIso (E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Pp)) ≪≫
      DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app Pp) ≪≫
      (DerivedCategory.quotientCompQhIso _).app ((E.mapHomologicalComplex (.up ℤ)).obj Pp) ≪≫
      DerivedCategory.Q.mapIso eP ≪≫
      (NS.mapDerivedCategoryFactors.app Pe).symm
  refine (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X).prop_of_iso eL.symm
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory S ?_)
  have hz (n : ℤ) (hn : IsZero (Pc.X n)) : IsZero (Pe.X n) := Ee.map_isZero hn
  have : CochainComplex.IsStrictlyGE Pe (min a b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hz i (hPz i (.inl hi))
  have : CochainComplex.IsStrictlyLE Pe b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hz i (hPz i (.inr hi))
  exact Etale.DerivedCategory.constructibleFiniteTor_Q_obj Pe (min a b) b
    (fun n ↦ flat_etaleSheafExtendScalars_obj (hPflat n)) (fun n ↦
      have := hPc n
      isConstructibleSheaf_etaleSheafExtendScalars_obj (algebraMap R S) (Pc.X n))

end AlgebraicGeometry.ProEtale
