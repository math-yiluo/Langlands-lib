/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso
public import WeilConjectures.CategoryTheory.Triangulated.AdjunctionUnitLocal
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar

/-!

# Reduction modulo `ℓⁿ` read on the étale site commutes with `Rd^!` for closed immersions

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, `n : ℕ`, and write
`red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small étale
site (`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`). For a closed immersion
`d : Z ⟶ Y` of separated `k`-schemes of finite type and *any* isomorphism
`γ : Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!`, this file proves that the transpose
`β : Rd^! ⋙ red_Z ⟶ red_Y ⋙ Rd^!` of `γ⁻¹` under the adjunctions `Rd_! ⊣ Rd^!` is an isomorphism
(`ProEtale.CondensedRing.isIso_mateEquiv_etaleReduction_of_isClosedImmersion`). This is the second
half of `ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`.

## Strategy

At `K`, the mate `β_K` is the unit of the étale adjunction `Rd_! ⊣ Rd^!`, then `Rd^!` of `γ⁻¹`,
then `Rd^! red_Y (ε_K)`, for `ε` the counit of the condensed adjunction `Rd_! ⊣ Rd^!`
(`CategoryTheory.isIso_mateEquiv_app_of_isIso_map_counit`). The étale unit is invertible, `Rd_!`
being fully faithful (`Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`), so `γ` drops out
and it remains to see that `Rd^! red_Y (ε_K)` is an isomorphism.

1. On `Dᵇc(Y)⟦𝒪_E⟧`, the counit `ε_K` and the unit `K ⟶ Rj_* j^* K` of the open complement
   `j : U ⟶ Y` of `d` extend to a distinguished triangle (the supported localization triangle,
   `ProEtale.CondensedRing.exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit`),
   by the formal recollement argument `CategoryTheory.Pretriangulated.Recollement`: `Rd_! ≅ Rd_*`
   is fully faithful, `j^* Rd_* = 0`, and complexes killed by `j^*` come from `Z` by open–closed
   detection.
2. The reduction modulo `ℓⁿ` preserves the `j`-local objects `Rj_* L`
   (`isIso_derivedUpperStarLowerStarAdjunction_unit_app_integersModPowReduction`),
   and the finite-coefficient comparison `Φ` and `Rν_*` commute with `Rj_*`
   (`ProEtale.finiteCoefficientDerivedLowerStarIso`,
   `ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`); so `red_Y (Rj_* j^* K)` is an
   étale `Rj_* C`, which receives no maps from the shifts of `Rd_! B`
   (`Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`).
3. Hence composition with `red_Y (ε_K)` is bijective on morphisms out of `Rd_! B`, and
   `Rd^! red_Y (ε_K)` is an isomorphism by the Yoneda lemma along `Rd_! ⊣ Rd^!`
   (`CategoryTheory.Adjunction.isIso_map_of_bijective_comp`).

## Main results

- `ProEtale.CondensedRing.exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit`: the
  supported localization triangle `Rd_! Rd^! K ⟶ K ⟶ Rj_* j^* K ⟶` on bounded constructible
  `𝒪_E`-complexes, for a closed immersion `d` with open complement `j`.
- `ProEtale.CondensedRing.isIso_rightDerivedUpperShriek_map_etaleReduction_map_counit`: `Rd^!`
  inverts the reduction of the counit of `Rd_! ⊣ Rd^!`.
- `ProEtale.CondensedRing.isIso_mateEquiv_etaleReduction_of_isClosedImmersion`: the transpose of
  any isomorphism `Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-! ### The supported localization triangle on bounded constructible `𝒪_E`-complexes -/

section Triangle

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The supported localization triangle** on bounded constructible `𝒪_E`-complexes: for a
closed immersion `d : Z ⟶ Y` with open complement `j : U ⟶ Y`, the counit
`Rd_! Rd^! K ⟶ K` of `Rd_! ⊣ Rd^!` and the unit `K ⟶ Rj_* j^* K` of `j^* ⊣ Rj_*` extend to a
distinguished triangle. This is the formal recollement argument
(`CategoryTheory.Pretriangulated.Recollement.exists_distTriang_counit_unit`): `Rd_! ≅ Rd_*` is
fully faithful, `j^* Rd_* = 0`, `Rj_*` is fully faithful, and a complex `K` killed by `j^*` is
`Rd_* d^* K` by open–closed detection. -/
theorem exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit (d : Z ⟶ Y)
    [IsClosedImmersion d.left]
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ∃ w, Triangle.mk
      ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d).counit.app K)
      ((PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (overOpenComplement d)).unit.app K) w ∈ distTriang _ := by
  let e := boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E d
  have hdj := isCompl_range_overOpenComplement d
  let adjd := PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E d
  have := isIso_counit_of_isClosedImmersion_of_lowerStarCompatibility _ d.left adjd
    (PadicIntegersRingObj.boundedConstructibleLowerStarCompatibility ℓ E d)
  refine Recollement.exists_distTriang_counit_unit
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (overOpenComplement d))
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d)
    (adjd.fullyFaithfulROfIsIsoCounit.ofIso e.symm) (fun M ↦ ?_) (fun L hL ↦ ?_) K
  · exact (isZero_boundedConstructibleUpperStar_obj_of_upperStarAdjunction _ ℓ
      (overOpenComplement d) d adjd hdj.disjoint.symm M).of_iso
      ((boundedConstructibleUpperStar _ ℓ _).mapIso (e.app M))
  · have : IsIso (adjd.unit.app L) := by
      refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ d
        (overOpenComplement d) hdj _ ?_ (adjd.isIso_map_unit_app_of_isIso_counit L)
      exact ⟨0, hL.eq_of_src _ _, (isZero_boundedConstructibleUpperStar_obj_of_upperStarAdjunction
        _ ℓ (overOpenComplement d) d adjd hdj.disjoint.symm _).eq_of_src _ _⟩
    exact ⟨_, ⟨e.app _ ≪≫ (asIso (adjd.unit.app L)).symm⟩⟩

end Triangle

/-! ### The reduction of `j`-local objects, read on the étale site -/

section Etale

section Comparison

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The derived finite-coefficient comparison commutes with the shifts, being `D(Φ)` for the
exact equivalence `Φ = finiteCoefficientModEquivalence`. -/
noncomputable instance commShift_finiteCoefficientDerivedEquivalence_functor :
    (finiteCoefficientDerivedEquivalence X T).functor.CommShift ℤ :=
  inferInstanceAs (D((finiteCoefficientModEquivalence X T).functor).CommShift ℤ)

/-- The derived finite-coefficient comparison is triangulated, being `D(Φ)` for the exact
equivalence `Φ = finiteCoefficientModEquivalence`. -/
instance isTriangulated_finiteCoefficientDerivedEquivalence_functor :
    (finiteCoefficientDerivedEquivalence X T).functor.IsTriangulated :=
  inferInstanceAs (D((finiteCoefficientModEquivalence X T).functor).IsTriangulated)

end Comparison

/-- The reduction modulo `ℓⁿ` read on the small étale site, on the whole derived category of
`𝒪_{E,X}`-modules: `N ↦ Rν_* Φ(N ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ)`. On bounded constructible complexes it is
`etaleReduction` (`etaleReductionIsoDerivedEtaleReduction`). -/
noncomputable abbrev derivedEtaleReduction (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  L(Mod.extendScalars (integersModPowReduction X ℓ E n)) ⋙
    (finiteCoefficientDerivedEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

/-- `etaleReduction` is the restriction of `derivedEtaleReduction` to bounded constructible
complexes. -/
noncomputable def etaleReductionIsoDerivedEtaleReduction (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    etaleReduction ℓ E n Y ≅ (boundedConstructible _).ι ⋙ derivedEtaleReduction ℓ E n Y.left :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n)
      _ ≪≫ Functor.associator _ _ _

/-- The étale reading of the reduction is triangulated. -/
instance isTriangulated_derivedEtaleReduction (X : Scheme.{u}) :
    (derivedEtaleReduction ℓ E n X).IsTriangulated := by
  infer_instance

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **No maps from the closed part into the reduction of a `j`-local object.** Let `d` be a
closed immersion with open complement `j`, and `N ∈ D(Mod_{𝒪_{E,Y}})` with
`N ⟶ Rj_* Lj^* N` invertible. Then `Hom((Rd_! B)⟦m⟧, red_Y N) = 0` for every étale complex `B` on
`Z`: the reduction `N ⊗ᴸ 𝒪_E ⧸ ℓⁿ` is again `j`-local, and `Φ` and `Rν_*` commute with `Rj_*`,
so `red_Y N` is an étale `Rj_* C`. -/
theorem subsingleton_hom_shift_rightDerivedLowerShriek_derivedEtaleReduction_obj
    {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (d : Z ⟶ Y)
    [IsClosedImmersion d.left] [HasCompactification d.left]
    (B : DerivedCategory (Sheaf Z.left.smallEtaleTopology
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))))
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)))
    (hN : IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E)
      (overOpenComplement d).left).unit.app N)) (m : ℤ) :
    Subsingleton
      ((shiftFunctor _ m).obj ((Etale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left).obj B) ⟶
        (derivedEtaleReduction ℓ E n Y.left).obj N) := by
  let j := (overOpenComplement d).left
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let N' := L(Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).obj N
  have hN' := isIso_derivedUpperStarLowerStarAdjunction_unit_app_integersModPowReduction ℓ E n j
    N hN
  let M := (finiteCoefficientDerivedEquivalence _ (PadicAlgCl.integersModPow ℓ E n)).functor.obj
    (L((j)^*⟦Profinite.integersModPowRingObj ℓ E n⟧).obj N')
  let e : (derivedEtaleReduction ℓ E n Y.left).obj N ≅
      (R(Etale.lowerStar A j)).obj ((R(ν_*(_)[A])).obj M) :=
    (R(ν_*(Y.left)[A])).mapIso
      ((finiteCoefficientDerivedEquivalence _ (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
        (asIso ((derivedUpperStarLowerStarAdjunction _ j).unit.app N')) ≪≫
      ((finiteCoefficientDerivedLowerStarIso (PadicAlgCl.integersModPow ℓ E n) j).app _).symm) ≪≫
      (rightDerivedLowerStarCompComparisonLowerStarIso A j).app M
  have := Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar A d.left j
    (isCompl_range_overOpenComplement d).disjoint B ((R(ν_*(_)[A])).obj M) m
  exact (Iso.homCongr (Iso.refl _) e).subsingleton

end Etale

/-! ### The transpose of the compact-support comparison -/

section Main

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **`Rd^!` inverts the reduction of the counit of `Rd_! ⊣ Rd^!`** for a closed immersion `d`.
The reduction `red_Y` of the supported localization triangle
`Rd_! Rd^! K ⟶ K ⟶ Rj_* j^* K ⟶` is distinguished, and its third vertex receives no maps from
the shifts of `Rd_! B`, so composition with `red_Y (ε_K)` is bijective on morphisms out of
`Rd_! B`; conclude by the Yoneda lemma along the étale `Rd_! ⊣ Rd^!`. -/
theorem isIso_rightDerivedUpperShriek_map_etaleReduction_map_counit (d : Z ⟶ Y)
    [IsClosedImmersion d.left]
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    IsIso ((Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) d.left).map
      ((etaleReduction ℓ E n Y).map
        ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d).counit.app
          K))) := by
  obtain ⟨w, hT⟩ := exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit ℓ E d K
  have hT' := ((boundedConstructible _).ι ⋙ derivedEtaleReduction ℓ E n Y.left).map_distinguished
    _ hT
  have hN := ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E)
    (overOpenComplement d).left).isIso_unit_app_iff_of_iso_obj
      ((PadicIntegersRingObj.boundedConstructibleLowerStarCompatibility ℓ E
        (overOpenComplement d)).app
        ((boundedConstructibleUpperStar _ ℓ (overOpenComplement d)).obj K)).symm).2
      ((derivedUpperStarLowerStarAdjunction _
        (overOpenComplement d).left).isIso_unit_app_obj_of_isIso_counit_app _)
  have h := (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (etaleReductionIsoDerivedEtaleReduction ℓ E n Y)
    (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) d.left))
    ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d).counit.app K)).2
  refine h ((Etale.rightDerivedUpperShriekAdjunction _ d.left).isIso_map_of_bijective_comp _
    fun B ↦ bijective_comp_mor₁_of_subsingleton_shift hT' _ ?_ ?_)
  · have := subsingleton_hom_shift_rightDerivedLowerShriek_derivedEtaleReduction_obj ℓ E n d B _
      hN 0
    exact @Equiv.subsingleton _ _ ((shiftFunctorZero _ ℤ).app _).homFromEquiv.symm this
  · have := subsingleton_hom_shift_rightDerivedLowerShriek_derivedEtaleReduction_obj ℓ E n d B _
      hN 1
    exact @Equiv.subsingleton _ _
      ((shiftEquiv' _ (1 : ℤ) (-1) (by norm_num)).toAdjunction.homEquiv _ _).symm this

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with `Rd^!` for a closed
immersion `d`**: for *any* isomorphism `γ : Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!`, its transpose
`β : Rd^! ⋙ red_Z ⟶ red_Y ⋙ Rd^!` under the adjunctions `Rd_! ⊣ Rd^!` is an isomorphism. At `K`,
`β_K` is the étale unit (invertible, `Rd_!` being fully faithful), then `Rd^!` of `γ⁻¹`, then
`Rd^! red_Y (ε_K)` (`isIso_rightDerivedUpperShriek_map_etaleReduction_map_counit`). -/
theorem isIso_mateEquiv_etaleReduction_of_isClosedImmersion (d : Z ⟶ Y)
    [IsClosedImmersion d.left]
    (γ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E d ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left) :
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d)
      (Etale.rightDerivedUpperShriekAdjunction _ d.left) (TwoSquare.mk _ _ _ _ γ.inv)) := by
  have (Q : DerivedCategory (Sheaf Z.left.smallEtaleTopology
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)))) :=
    Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app _ d.left Q
  have : IsIso (Etale.rightDerivedUpperShriekAdjunction
      (integersModPowCoeff.{u} ℓ E n) d.left).unit :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (TwoSquare.mk _ _ _ _ γ.inv) := inferInstanceAs (IsIso γ.inv)
  have (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
    isIso_mateEquiv_app_of_isIso_map_counit
      (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d)
      (Etale.rightDerivedUpperShriekAdjunction _ d.left) (TwoSquare.mk _ _ _ _ γ.inv) K
      (isIso_rightDerivedUpperShriek_map_etaleReduction_map_counit ℓ E n d K)
  exact NatIso.isIso_of_isIso_app _

end Main

end AlgebraicGeometry.ProEtale.CondensedRing
