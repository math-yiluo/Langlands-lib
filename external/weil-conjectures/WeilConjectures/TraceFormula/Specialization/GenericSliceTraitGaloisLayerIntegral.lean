/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayerIntegral
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeSplitMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible

/-!
# The averaging splitting (M2) on the generic slice trait

This file proves (M2), the averaging splitting of the slice step of Deligne's finiteness theorem
(SGA 4½, [Th. finitude], Lemme 3.4,
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`): for the
morphism of models `σ` over a generic slice trait `S' ⟶ S` and a bounded constructible
`ℚ̄_ℓ`-complex `B`, the pullback exchange of `σ.toCartesian` is a split monomorphism at `B`.

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, `K = k'(x)^alg`,
`T = Spec K⟦t⟧`, and let `φ = NearbyCyclesModel.affineSpaceSliceHom k' n i` be the morphism of
geometric models over the coordinate generic slice `h : 𝔸ⁿ_T ⟶ 𝔸ⁿ⁺¹_S = X`. Following Deligne
(SGA 4½, [Th. finitude], proof of 3.3), `φ` factors through the strict localization `S'` of `𝔸¹_S`
at the generic point of its special fibre (`AlgebraicGeometry.GenericSliceTrait`), with
`X' = X ×_{𝔸¹_S} S'`:
```
(𝔸ⁿ_T over T) ──τ──→ (X' over S') ──σ──→ (X over S)
```
* `τ` (`NearbyCyclesModel.genericSliceTraitChangeHom`) is the change of strictly henselian trait
  `T ⟶ S'`; its pullback exchange is invertible by the invariance of nearby cycles under change
  of trait (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, SGA 4½,
  [Th. finitude], 3.7).
* `σ` (`NearbyCyclesModel.genericSliceTraitHom`) factors through its cartesian model
  (`NearbyCyclesModel.Hom.cartesianModel`), with generic fibre `X' ×_S Spec Ω`. The second factor
  is weakly étale base change along `X' ⟶ X`, an isomorphism
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_fromCartesian_of_weaklyEtale`). The first factor
  is the change of generic fibres `π : X' ×_{S'} Spec Ω' ⟶ X' ×_S Spec Ω`, whose pullback exchange
  is, up to the extension from an algebraic closure `k̄₀` to `Ω'` (which does not change
  cohomology), the inclusion of the invariants under the pro-`p` group `P = Gal(k̄₀/k₀)`,
  `k₀ = Ω ⊗_{η} η'`
  (Th. finitude, Lemme 3.4), split by averaging
  (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`, (M2)).

The strict localization is a generic slice trait
(`AlgebraicGeometry.nonempty_genericSliceTrait`).

The proof passes to an integral model `K₀` of `B` (derived complete and bounded constructible on
the noetherian `𝔸ⁿ⁺¹_S`, `ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`).
Over a slice trait the change of geometric generic fibres is a pro-`p` Galois layer up to universal
homeomorphisms (`AlgebraicGeometry.SliceTrait.exists_finrank_eq_pow`), so the unit of its
adjunction with `𝒪_E`-coefficients splits
(`NearbyCyclesModel.Hom.isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers`), hence
the restricted base change morphism with `𝒪_E`-coefficients splits, and the splitting passes to
`E` and `ℚ̄_ℓ`
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_isSplitMono_padicIntegers`).
The reductions of `K₀` modulo `ℓⁿ⁺¹` are bounded constructible, hence of étale origin.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- On a noetherian scheme, the reductions modulo `ℓⁿ` of a bounded constructible `𝒪_E`-complex
are bounded below of étale origin. -/
lemma plusEtaleOrigin_extendScalars_integersModPow_of_boundedConstructible {ℓ : ℕ}
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) {Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hC : boundedConstructible _ C) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 n))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersModPow ℓ E.1 n)).functor.obj
        (L(Mod.extendScalars (integersModPowReduction Y ℓ E.1 n)).obj C)) :=
  (isEtaleOrigin_of_isConstructible _
    (boundedConstructible_derivedExtendScalars_integersModPowReduction Y ℓ E.1 n C
      hC)).plusEtaleOrigin

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme IsLocalRing

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)
  [IsAlgClosed Ω₁] (ha₁ : Function.Injective a₁)
  (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  {q : M.total ⟶ Spec (.of D.R)} {g : M.generic ⟶ Spec (.of D.Ω)}
  {q₁ : N.total ⟶ Spec (.of R₁)} {g₁ : N.generic ⟶ Spec (.of Ω₁)}

include ha₁ halg in
open PadicAlgCl in
/-- **The change of geometric generic fibres over a slice trait is split by the unit,
`𝒪_E`-coefficients** (SGA 4½, [Th. finitude], Lemme 3.4). Let `φ : M ⟶ N` be a morphism of models
over the slice trait `Spec R ⟶ Spec R₁`, compatible with the geometric generic points, and `p ≠ ℓ`
a prime such that every natural number vanishing in the residue field of `R₁` is divisible by `p`.
For a derived complete `𝒪_E`-complex `C` on `Y` whose reductions modulo `ℓⁿ⁺¹` are bounded below of
étale origin, the unit of `Lg^* ⊣ Rg_*`, `g = φ.toCartesian.generic`, is a split monomorphism at
`Lε'^* C`. -/
theorem isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers
    (hM : IsPullback M.j g q (Spec.map (CommRingCat.ofHom D.a)))
    (hN : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)))
    (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom D.φ))
    (hg : φ.generic ≫ g₁ = g ≫ Spec.map (CommRingCat.ofHom D.ωS))
    {p : ℕ} [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ) (E : PadicAlgCl.FiniteIntermediateField ℓ)
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
  have hsub := D.subsingleton_primeSpectrum ha₁ halg
  have hdeg := D.exists_finrank_eq_pow hp
  let := D.φ.toAlgebra
  let := a₁.toAlgebra
  let := D.a.toAlgebra
  let := D.ωS.toAlgebra
  let : Algebra R₁ D.Ω := (D.a.comp D.φ).toAlgebra
  have : IsScalarTower R₁ D.R D.Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₁ Ω₁ D.Ω := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun D.ωS_comp x).symm
  have : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  have : Algebra.IsAlgebraic D.R D.Ω := D.isAlgebraic_a
  refine isSplitMono_unit_toCartesian_generic_of_traitChange_padicIntegers (φ := φ) E hM hN hq
    hg (fun L' hdvd ↦ ?_) C hC m hred
  obtain ⟨k, hk⟩ := hdeg L'
  rw [hk] at hdvd
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
    ((Fact.out : ℓ.Prime).dvd_of_dvd_pow hdvd)).symm

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

-- the integral splitting is matched against the large types of the slice models
/-- **(M2) The pro-`p` averaging splitting on the generic slice trait** (SGA 4½, [Th. finitude],
Lemme 3.4): for a bounded constructible complex `B` on `X = 𝔸ⁿ⁺¹_S`, the pullback exchange of the
first factor `toCartesian` of the morphism of models `σ : (X ×_{𝔸¹_S} S' over S') ⟶ (X over S)`
is a split monomorphism at `B`. -/
theorem isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom
    (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((genericSliceTraitHom D n i).toCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have : IsNoetherian (affineSpaceModel k' (n + 1)).total :=
    (isTraitModel_affineSpaceModel (k' := k') (n + 1)).isNoetherian_total
  -- all the schemes of the slice are affine
  have : IsAffine (affineSpaceModel k' (n + 1)).total :=
    inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin (n + 1)); trait k'))
  have : IsAffine (affineSpaceModel k' (n + 1)).geometric.total :=
    inferInstanceAs (IsAffine (affineSpaceModel k' (n + 1)).total)
  have : IsAffine (affineSpaceModel k' (n + 1)).geometric.generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitModel D n i).total := inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitModel D n i).generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine
      (pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b))) :=
    inferInstance
  have : IsAffine (genericSliceTraitHom D n i).cartesianModel.generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitHom D n i).cartesianModel.total :=
    inferInstanceAs (IsAffine (genericSliceTraitModel D n i).total)
  obtain ⟨E, K₀, n₀, hK₀, hn₀, hK₀c, ⟨e⟩⟩ := exists_derivedCompleteIntegers_iso_integralModel ℓ hB
  have hp : ∀ m : ℕ, (m : IsLocalRing.ResidueField (PowerSeries k')) = 0 → ringChar k' ∣ m :=
    fun m hm ↦ (ringChar.spec k' m).1
      ((PowerSeries.residueFieldEquiv k').injective (by rw [map_natCast, hm, map_zero]))
  have hunit := Hom.isSplitMono_unit_toCartesian_generic_of_sliceTrait_padicIntegers
    D.toSliceTrait (algebraMap_traitGenericField_injective k') (isAlgebraic_traitGenericField k')
    (genericSliceTraitHom D n i) (N := (affineSpaceModel k' (n + 1)).geometric)
    (q := genericSliceTraitStructure D n i) (g := pullback.snd _ _)
    (q₁ := 𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (g₁ := pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) ?_ ?_ hp
    (Fact.out : ringChar k' ≠ ℓ) E K₀ hK₀ n₀
    (fun m ↦ plusEtaleOrigin_extendScalars_integersModPow_of_boundedConstructible E (m + 1) hK₀c)
  · have h𝒪 := Hom.isSplitMono_map_exchangeRight_app_toCartesian_of_isSplitMono_unit _ _ K₀ hunit
    exact Hom.isSplitMono_pullbackExchange_app_of_isSplitMono_padicIntegers
      (genericSliceTraitHom D n i).toCartesian E K₀ n₀ e (by exact_mod_proofs h𝒪)
  · change genericSliceTraitProj D n i ≫ _ = _
    rw [genericSliceTraitProj, genericSliceTrait_fst_comp_over]
    exact congrArg (genericSliceTraitStructure D n i ≫ ·) D.spec_φ.symm
  · exact pullback.lift_snd _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
