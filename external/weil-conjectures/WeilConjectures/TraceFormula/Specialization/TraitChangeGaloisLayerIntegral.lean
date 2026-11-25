/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.IntegralSplit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange

/-!
# The change of geometric generic fibre over a change of trait splits, `𝒪_E`-coefficients

Let `φ : M ⟶ N` be a morphism of models over a change of strictly henselian traits
`Spec R ⟶ Spec R₁` such that `Spec(Ω₁ ⊗_{R₁} R)` is a single point. The change of geometric generic
fibres factors as `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms and `q` the base
change of the pro-Galois `Spec L^sep ⟶ Spec L`
(`NearbyCyclesModel.Hom.traitChangeInsepMap_comp_traitChangeGaloisMap_comp`). If the degrees of
the finite Galois subextensions of `L^sep/L` are prime to `ℓ`, the unit of `Lg^* ⊣ Rg_*` with
`𝒪_E`-coefficients is a split monomorphism at the restriction of every derived complete complex
`C` on `Y` whose reductions modulo `ℓⁿ⁺¹` are bounded below of étale origin
(`NearbyCyclesModel.Hom.isSplitMono_unit_toCartesian_generic_of_traitChange_padicIntegers`), by
`ProEtale.CondensedRing.isSplitMono_derivedUnit_galois_padicIntegers`. Consequently the base
change morphism of `Rj_*` restricted to the special fibre is a split monomorphism
(`NearbyCyclesModel.Hom.isSplitMono_map_exchangeRight_app_toCartesian_of_isSplitMono_unit`):
this is the integral form of SGA 4½, [Th. finitude], Lemme 3.4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- The reductions modulo `ℓⁿ` of the derived pullback of an `𝒪_E`-complex whose reduction is
bounded below of étale origin are bounded below of étale origin. -/
lemma plusEtaleOrigin_extendScalars_integersModPow_leftDerivedUpperStar_obj {ℓ : ℕ}
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) {W Y : Scheme.{u}} (f : W ⟶ Y)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hC : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersModPow ℓ E.1 n)).functor.obj
        (L(Mod.extendScalars (integersModPowReduction Y ℓ E.1 n)).obj C))) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) W
      ((finiteCoefficientDerivedEquivalence W (integersModPow ℓ E.1 n)).functor.obj
        (L(Mod.extendScalars (integersModPowReduction W ℓ E.1 n)).obj
          ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj C))) :=
  ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedEquivalence W (integersModPow ℓ E.1 n)).functor.mapIso
      ((derivedUpperStarExtendScalarsIso
        (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 n) f).app C).symm)
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj _ f hC)

end AlgebraicGeometry.ProEtale.CondensedRing

/-- A functor maps the component of a natural transformation `β' = β` at `x` to a split
monomorphism if `β.app x` is one. -/
lemma CategoryTheory.isSplitMono_map_app_of_eq {C D E : Type*} [Category C] [Category D]
    [Category E] {F G : C ⥤ D} (β β' : F ⟶ G) (h : β' = β) (H : D ⥤ E) (x : C)
    (hβ : IsSplitMono (β.app x)) : IsSplitMono (H.map (β'.app x)) := by
  subst h
  infer_instance

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Transport of a split unit along an equality of morphisms of schemes. -/
lemma isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hf : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ f).unit.app G)) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ g).unit.app G) := by
  subst h
  exact hf

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme

section Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

-- the mate is matched against the large types of the nearby cycles functors
/-- **The restricted base change morphism of the change of geometric generic fibre is split by
the unit**: `Li^*` of the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of `φ.toCartesian` is
a split monomorphism at `Lε'^* C` as soon as the unit of `Lg^* ⊣ Rg_*`,
`g = φ.toCartesian.generic`, is one at `Lε'^* C`. -/
theorem isSplitMono_map_exchangeRight_app_toCartesian_of_isSplitMono_unit
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic).unit.app
      ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((L((M.i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ φ.cartesianModel.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.toCartesian.commSq_j)).app
        ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) := by
  have e : L((φ.toCartesian.total)^*⟦Λ⟧) ≅ 𝟭 _ := by
    rw [toCartesian_total]
    exact leftDerivedUpperStarId Λ _
  have key := Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit
    (derivedUpperStarLowerStarAdjunction Λ φ.cartesianModel.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j)
    (derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic) e
    (pullbackSquareComparison Λ φ.toCartesian.commSq_j).hom
    ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C)
  have hβ := (baseChangeMap_eq_exchangeRight Λ φ.toCartesian.commSq_j).symm.trans
    (φ.toCartesian.baseChangeMap_commSq_j_eq_mateEquiv Λ)
  exact isSplitMono_map_app_of_eq _ _ hβ _ _ key

end Abstract

section Integral

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {φ : M.Hom N f f'}
  {q : M.total ⟶ Spec (.of R)} {g : M.generic ⟶ Spec (.of Ω)}
  {q₁ : N.total ⟶ Spec (.of R₁)} {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

open PadicAlgCl in
/-- **The change of geometric generic fibre over a change of trait is split by the unit,
`𝒪_E`-coefficients.** Let `φ : M ⟶ N` be a morphism of models over the traits
`Spec R ⟶ Spec R₁`, with geometric generic points `Spec Ω ⟶ Spec Ω₁`, such that
`Spec(Ω₁ ⊗_{R₁} R)` is a single point and the degrees of the finite Galois subextensions of
`L^sep / L` (`L = Ω₁(R)`) are prime to `ℓ`. For a derived complete `𝒪_E`-complex `C` on `Y` whose
reductions modulo `ℓⁿ⁺¹` are bounded below of étale origin, the unit of `Lg^* ⊣ Rg_*`,
`g = φ.toCartesian.generic`, is a split monomorphism at `Lε'^* C`. -/
theorem isSplitMono_unit_toCartesian_generic_of_traitChange_padicIntegers [IsAlgClosed Ω]
    [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))]
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω)))
    (hp : ∀ L' : FiniteGaloisIntermediateField (traitTensorCompositum R Ω₁ Ω)
      (traitTensorCompositumSep R Ω₁ Ω), ¬ ℓ ∣ Module.finrank (traitTensorCompositum R Ω₁ Ω) L')
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace φ.cartesianModel.generic]
    [QuasiSeparatedSpace φ.cartesianModel.generic]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (hC : derivedCompleteIntegers ℓ E Y C) (m : ℤ) [C.IsGE m]
    (hred : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 (n + 1)))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersModPow ℓ E.1 (n + 1))).functor.obj
        (L(Mod.extendScalars (integersModPowReduction Y ℓ E.1 (n + 1))).obj C))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      φ.toCartesian.generic).unit.app
        ((L((φ.cartesianModel.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj C)) := by
  have := isUniversalHomeomorphism_traitChangeInsepMap hq hM hN hg
  have : QuasiSeparatedSpace (φ.traitChangeGaloisBase Ω q q₁ g₁ hN.w hq) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  refine isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_eq _
    (traitChangeInsepMap_comp_traitChangeGaloisMap_comp hN.w hq hM.w hg) _ ?_
  refine isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp₃ _
    (φ.traitChangeInsepMap Ω q g q₁ g₁ hN.w hq hM.w hg) (φ.traitChangeGaloisMap Ω q q₁ g₁ hN.w hq)
    (φ.traitChangeThickening Ω q q₁ g₁ hN.w hq) _ ?_
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1)
    φ.cartesianModel.ε C m
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1)
    (φ.traitChangeThickening Ω q q₁ g₁ hN.w hq)
    ((L((φ.cartesianModel.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj C) m
  exact isSplitMono_derivedUnit_galois_padicIntegers E (φ.traitChangeResidue Ω q q₁ g₁ hN.w hq)
    hp _
    (derivedCompleteIntegers_leftDerivedUpperStar_obj _
      (derivedCompleteIntegers_leftDerivedUpperStar_obj _ hC)) m
    (fun n ↦ plusEtaleOrigin_extendScalars_integersModPow_leftDerivedUpperStar_obj E _ _
      (plusEtaleOrigin_extendScalars_integersModPow_leftDerivedUpperStar_obj E _ _ (hred n)))

end Integral

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom
