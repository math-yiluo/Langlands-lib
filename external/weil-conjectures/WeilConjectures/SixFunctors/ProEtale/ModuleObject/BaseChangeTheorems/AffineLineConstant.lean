/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.AffineLineUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AffineLineUnitLocal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection

/-!
# The affine line is acyclic with `ℚ̄_ℓ`-coefficients, for the constant sheaf

Let `k` be an algebraically closed field of characteristic `≠ ℓ`, `Y` a separated `k`-scheme of
finite type and `p : 𝔸¹_Y ⟶ Y` the affine line. This file proves that the unit
`ℚ̄_ℓ ⟶ Rp_* Lp^* ℚ̄_ℓ` of the derived adjunction `Lp^* ⊣ Rp_*` of module objects over the
condensed ring `ℚ̄_ℓ` is an isomorphism
(`ProEtale.CondensedRing.isIso_affineLineUnit_app_tensorUnit_padicAlgCl`).

The unit of `Lp^* ⊣ Rp_*` is the base change morphism of the commutative, non-cartesian, square
with sides `p`, `p`, `𝟙`, `𝟙` (`ProEtale.CondensedRing.isIso_unit_app_of_isIso_baseChangeMap_app`,
`ProEtale.isIso_derivedBaseChangeMap_app_of_isIso_unit_app`), so the passages between coefficient
rings of base change morphisms apply to it, none of which needs the square to be cartesian:

1. from `ℚ̄_ℓ` to `𝒪_E` by flat extension of scalars
   (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`), the unit
   `ℚ̄_ℓ` being the extension of scalars of the unit `𝒪_E`;
2. from `𝒪_E` to `𝔽_E` by derived Nakayama for derived complete complexes
   (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_isIso_derivedReduction`);
3. the first derived reduction of the unit `𝒪_E` is the constant pro-étale sheaf `𝔽_E`
   (`ProEtale.CondensedRing.derivedReductionTensorUnitIso`), at which the finite-coefficient
   unit is invertible by the acyclicity of the affine line on the étale site
   (`AlgebraicGeometry.ProEtale.isIso_unit_affineLine_singleFunctor_tensorUnit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The unit as a base change morphism, finite coefficients.** For `p : Y ⟶ X`, if the unit of
`Lp^* ⊣ Rp_*` is invertible at `K`, then so is the base change morphism of the commutative square
with sides `p`, `p`, `𝟙 X`, `𝟙 X`: it is the unit, up to the unit of `L𝟙^* ⊣ R𝟙_*`. -/
lemma isIso_derivedBaseChangeMap_app_of_isIso_unit_app (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    [IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app K)] :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (⟨rfl⟩ : CommSq p p (𝟙 X) (𝟙 X))).app K) := by
  have : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).Full :=
    Functor.Full.of_iso (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).symm
  have : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).Faithful :=
    Functor.Faithful.of_iso (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).symm
  have : IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).unit :=
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).unit_isIso_of_L_fully_faithful
  let e := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app K
  have hK : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app K) :=
    inferInstance
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
      ((L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _ e).2 hK
  have := Adjunction.isIso_mateEquiv_app_of_isIso_unit_app
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) (⟨rfl⟩ : CommSq p p (𝟙 X) (𝟙 X))).hom K
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 this

namespace CondensedRing

section Degenerate

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The unit as a base change morphism.** For `p : Y ⟶ X`, the unit of `Lp^* ⊣ Rp_*` is
invertible at `K` as soon as the base change morphism of the commutative square with sides `p`,
`p`, `𝟙 X`, `𝟙 X` is: up to the unit of `L𝟙^* ⊣ R𝟙_*`, the latter is the former. -/
lemma isIso_unit_app_of_isIso_baseChangeMap_app {X Y : Scheme.{u}} (p : Y ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : IsIso ((baseChangeMap Λ (⟨rfl⟩ : CommSq p p (𝟙 X) (𝟙 X))).app K)) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ p).unit.app K) := by
  have : (L((𝟙 X)^*⟦Λ⟧)).Full := Functor.Full.of_iso (leftDerivedUpperStarId Λ X).symm
  have : (L((𝟙 X)^*⟦Λ⟧)).Faithful := Functor.Faithful.of_iso (leftDerivedUpperStarId Λ X).symm
  have : IsIso (derivedUpperStarLowerStarAdjunction Λ (𝟙 X)).unit :=
    (derivedUpperStarLowerStarAdjunction Λ (𝟙 X)).unit_isIso_of_L_fully_faithful
  let e := (leftDerivedUpperStarId Λ X).app K
  have hb := (NatTrans.isIso_app_iff_of_iso _ e).2 h
  rw [baseChangeMap] at hb
  have := (Adjunction.isIso_map_unit_app_iff_of_isIso_exchangeRight_app
    (derivedUpperStarLowerStarAdjunction Λ (𝟙 X)) (derivedUpperStarLowerStarAdjunction Λ p)
    (pullbackSquareComparison Λ (⟨rfl⟩ : CommSq p p (𝟙 X) (𝟙 X))) K).1 inferInstance
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 this

end Degenerate

section ExtendScalars

variable {Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁] [IsCommMonObj Λ₁]
  [MonObj Λ₂] [IsCommMonObj Λ₂] (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (X : Scheme.{u})

/-- The derived extension of scalars along a morphism of condensed coefficient rings sends the
unit to the unit: it is monoidal. -/
noncomputable def leftDerivedExtendScalarsTensorUnitIso :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  letI := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorMonoidal
  (Functor.Monoidal.εIso (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor).symm

end ExtendScalars

section Integral

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- **Base change with integral coefficients from the first derived reduction.** For a
commutative square `e ≫ g = h ≫ p` of quasi-compact quasi-separated schemes with `W` noetherian,
the base change morphism `Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is invertible at a
bounded constructible `K` as soon as the pro-étale base change morphism with coefficients `𝔽_E` is
invertible at the first derived reduction of `K`: both sides are derived complete, and the first
derived reduction of the integral base change morphism is the one with coefficients `𝔽_E`
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`). The square need
not be cartesian. -/
theorem isIso_baseChangeMap_app_padicIntegers_of_isIso_derivedReduction
    {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsNoetherian W] (sq : CommSq e h g p)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W) K)
    (hred : IsIso ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq).app ((derivedReduction W ℓ E).obj K))) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq).app K) := by
  have hK₀ : derivedCompleteIntegers ℓ E W K := derivedCompleteIntegers_of_boundedConstructible hK
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj p
    (derivedCompleteIntegers_rightDerivedLowerStar_obj g hK₀)
  have htgt := derivedCompleteIntegers_rightDerivedLowerStar_obj h
    (derivedCompleteIntegers_leftDerivedUpperStar_obj e hK₀)
  have : K.IsGE hK.1.1.choose := hK.1.1.choose_spec
  have α := (nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E sq K
    hK.1.1.choose).some
  have r₁ := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).2 hred
  have hsrc' : derivedCompleteIntegers ℓ E X ((R((g)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      L((p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]
    exact hsrc
  have htgt' : derivedCompleteIntegers ℓ E X ((L((e)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      R((h)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]
    exact htgt
  have r₃ : IsIso ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) g)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) h)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq)).app K) :=
    isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map _ hsrc' htgt' r₁
  have t := isIso_baseChangeMap_app_of_isIso_exchangeRight
    (Profinite.padicIntegersRingObj ℓ E) sq K
  -- the two statements carry different proofs of `Precoherent Profinite`
  revert r₃ t
  normalize_precoherent
  intro r₃ t
  exact t r₃

variable (ℓ E) in
/-- **The first derived reduction of the unit**: the first derived reduction of the unit `𝒪_E`
of `D(Mod_{𝒪_{E,X}})` is the constant pro-étale sheaf `𝔽_E` placed in degree `0`. The derived
extension of scalars `- ⊗ᴸ_{𝒪_E} 𝔽_E` is monoidal, and `ProEtale.residueFieldModuleSheaf` is the
equivalence `ProEtale.finiteCoefficientModEquivalence`, which preserves the units. -/
noncomputable def derivedReductionTensorUnitIso (X : Scheme.{u}) :
    (derivedReduction X ℓ E).obj (𝟙_ _) ≅ (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
  (residueFieldModuleSheaf X ℓ E).mapDerivedCategory.mapIso
      (leftDerivedExtendScalarsTensorUnitIso (Profinite.padicIntegersRingObjToResidueField ℓ E) X ≪≫
        (DerivedCategory.singleFunctorObjUnitIso _).symm) ≪≫
    ((residueFieldModuleSheaf X ℓ E).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).app _ ≪≫
        finiteCoefficientModEquivalenceUnitIso X (PadicAlgCl.integersResidueField ℓ E))

end Integral

section Constant

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

include aY in
/-- **The affine line is acyclic for the constant `ℚ̄_ℓ`-sheaf.** For the affine line
`p : 𝔸¹_Y ⟶ Y` over a separated scheme `Y` of finite type over an algebraically closed field `k`
in which `ℓ` is invertible, the unit `ℚ̄_ℓ ⟶ Rp_* Lp^* ℚ̄_ℓ` of the derived adjunction
`Lp^* ⊣ Rp_*` of module objects over `ℚ̄_ℓ` is an isomorphism. -/
theorem isIso_affineLineUnit_app_tensorUnit_padicAlgCl (hℓ : IsUnit (ℓ : k)) :
    IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (𝟙_ _)) := by
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  let p := 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let sq : CommSq p p (𝟙 Y) (𝟙 Y) := ⟨rfl⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : IsNoetherian Y := {}
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  have : CompactSpace 𝔸(ULift.{u} (Fin 1); Y) := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); Y) :=
    quasiSeparatedSpace_of_quasiSeparated (p ≫ aY)
  let Λ := ResidueFieldCoeff.{u} ℓ E.1
  have : Finite Λ :=
    inferInstanceAs (Finite (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨ℓ, (Fact.out : ℓ.Prime).pos, natCast_eq_zero_residueFieldCoeff ℓ E.1,
      by simpa using hℓ.map (ΓSpecIso (.of k)).inv.hom⟩
  have hfin := ProEtale.isIso_unit_affineLine_singleFunctor_tensorUnit Λ aY
  have : IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
      ((derivedReduction Y ℓ E.1).obj (𝟙_ _))) :=
    (NatTrans.isIso_app_iff_of_iso _ (derivedReductionTensorUnitIso ℓ E.1 Y)).2 hfin
  have hred := ProEtale.isIso_derivedBaseChangeMap_app_of_isIso_unit_app Λ p
    ((derivedReduction Y ℓ E.1).obj (𝟙_ _))
  have hK := boundedConstructible_tensorUnit (Profinite.padicIntegersRingObj ℓ E.1) Y
  have hint := isIso_baseChangeMap_app_padicIntegers_of_isIso_derivedReduction sq (𝟙_ _) hK hred
  have hrat := isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers ℓ E sq (𝟙_ _)
    hK.1.1.choose hK.1.1.choose_spec hint
  refine isIso_unit_app_of_isIso_baseChangeMap_app _ p _ ?_
  let e := (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      Y)).leftDerivedFunctor.mapIso (leftDerivedExtendScalarsTensorUnitIso
        (padicIntegersRingObjToContinuousMapRingObj ℓ E) Y) ≪≫
    leftDerivedExtendScalarsTensorUnitIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 hrat

end Constant

end CondensedRing

end AlgebraicGeometry.ProEtale
