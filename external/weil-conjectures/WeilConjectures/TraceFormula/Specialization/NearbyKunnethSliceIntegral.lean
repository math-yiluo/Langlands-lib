/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance

/-!

# Invariance of nearby cycles under change of trait with `𝒪_E`- and `𝔽_E`-coefficients

Deligne's theorem on the invariance of nearby cycles under change of strictly henselian trait
(SGA 4½, [Th. finitude], Prop. 3.7) is proved in
`WeilConjectures.SixFunctors.NearbyCycles.TraitChange` with `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`), through the cases of
the coefficients `𝔽_E = 𝒪_E/ϖ` (Deligne's induction, `NearbyCyclesModel.traitChangeInvariance`)
and `𝒪_E` (derived Nakayama). This file extracts these two intermediate statements for the
pullback exchange itself:

* with `𝒪_E`-coefficients, the pullback exchange `α : Lf'^* Ψ_N B₀ ⟶ Ψ_M (Lf^* B₀)` is invertible
  as soon as `Lε^* B₀` is bounded constructible
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers`): the
  base change morphism of `Rj_*` restricted to the special fibre is invertible at the derived
  complete `Lε^* B₀`, since it is after reduction modulo `ϖ`;
* with `𝔽_E`-coefficients, it is invertible as soon as `Lε^* B` is bounded below of étale origin
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_residueField`), which is
  Deligne's statement for torsion coefficients.

The case of the change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` of a model of finite type over
`Spec k'⟦t⟧` follows
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_padicIntegers`,
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_residueField`); it is the
coefficient-generic form of the first "fact about traits" of the blueprint proof of
`proposition-external-kunneth-formula-nearby-cycles`, needed by the induction with
`𝒪_E`-coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ₁ κ₂ : Type u} [Field κ₁] [IsSepClosed κ₁] [Field κ₂] [IsSepClosed κ₂]
  {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Invariance of nearby cycles under change of strictly henselian trait, the restricted base
change morphism with `𝒪_E`-coefficients** (SGA 4½, [Th. finitude], Prop. 3.7). In the situation
of `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, the base change
morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres with
`𝒪_E`-coefficients, restricted to the special fibre of `M`, is invertible at every bounded
constructible `𝒪_E`-complex `K₀` on the geometric generic fibre of `N`: `K₀` is derived complete,
and the morphism is invertible after reduction modulo `ϖ`
(`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isPullback_trait_residueField`), hence by
derived Nakayama. -/
theorem isIso_map_exchangeRight_app_of_isPullback_trait_padicIntegers [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))}
    (hK₀ : boundedConstructible _ K₀) :
    IsIso ((L((M.i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) N.j)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) M.j)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) φ.commSq_j)).app
        K₀)) := by
  -- finiteness and separation properties of the fibres, by base change
  have hq₂ : QuasiCompact q₂ := MorphismProperty.of_isPullback hφ ‹_›
  have hq₂' : QuasiSeparated q₂ := MorphismProperty.of_isPullback hφ inferInstance
  have : QuasiCompact g₁ := MorphismProperty.of_isPullback hNj ‹_›
  have : QuasiSeparated g₁ := MorphismProperty.of_isPullback hNj inferInstance
  have : LocallyOfFiniteType g₁ := MorphismProperty.of_isPullback hNj ‹_›
  have : QuasiCompact g₂ := MorphismProperty.of_isPullback hMj hq₂
  have : QuasiSeparated g₂ := MorphismProperty.of_isPullback hMj hq₂'
  have : QuasiCompact p₂ := MorphismProperty.of_isPullback hMi hq₂
  have : QuasiSeparated p₂ := MorphismProperty.of_isPullback hMi hq₂'
  have := QuasiCompact.compactSpace_of_compactSpace q₁
  have := quasiSeparatedSpace_of_quasiSeparated q₁
  have := QuasiCompact.compactSpace_of_compactSpace q₂
  have := quasiSeparatedSpace_of_quasiSeparated q₂
  have := QuasiCompact.compactSpace_of_compactSpace g₁
  have := quasiSeparatedSpace_of_quasiSeparated g₁
  have := QuasiCompact.compactSpace_of_compactSpace g₂
  have := quasiSeparatedSpace_of_quasiSeparated g₂
  have := QuasiCompact.compactSpace_of_compactSpace p₂
  have := quasiSeparatedSpace_of_quasiSeparated p₂
  have : IsNoetherian N.generic := isNoetherian_of_locallyOfFiniteType g₁
  have : K₀.IsGE hK₀.1.1.choose := hK₀.1.1.choose_spec
  have hres := isIso_map_exchangeRight_app_of_isPullback_trait_residueField hι hun ha₁ ha₂
    halg₁ halg₂ hc hb₁ hb₂ φ q₁ g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen E hK₀
  have h := isIso_map_baseChangeMap_app_padicIntegers_of_residueField ℓ E φ.commSq_j M.i K₀
    hK₀.1.1.choose (derivedCompleteIntegers_of_boundedConstructible hK₀)
    (by exact_mod_proofs hres)
  exact_mod_proofs h

/-- **Invariance of nearby cycles under change of strictly henselian trait, `𝒪_E`-coefficients**
(SGA 4½, [Th. finitude], Prop. 3.7). In the situation of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, the pullback exchange
`α : Lf'^* Ψ_N B₀ ⟶ Ψ_M (Lf^* B₀)` with `𝒪_E`-coefficients is an isomorphism for every `B₀` whose
restriction `Lε^* B₀` to the geometric generic fibre of `N` is bounded constructible
(`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isPullback_trait_padicIntegers`). -/
theorem isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hB₀ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic)
      (L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀)) :
    IsIso ((φ.pullbackExchange (Profinite.padicIntegersRingObj ℓ E.1)).app B₀) := by
  have h := isIso_map_exchangeRight_app_of_isPullback_trait_padicIntegers hι hun ha₁ ha₂ halg₁
    halg₂ hc hb₁ hb₂ φ q₁ g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen E hB₀
  have h' := isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app
    (Profinite.padicIntegersRingObj ℓ E.1) φ B₀ (by exact_mod_proofs h)
  exact_mod_proofs h'

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
-- the special fibre of `N` over `κ₁` (`hNi`) does not enter the base change morphism; it is kept
-- for the uniformity of the statement with
-- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers`
/-- **Invariance of nearby cycles under change of strictly henselian trait, the restricted base
change morphism with `𝔽_E`-coefficients** (SGA 4½, [Th. finitude], Prop. 3.7, for the torsion
coefficients `𝔽_E = 𝒪_E/ϖ`). In the situation of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres with `𝔽_E`-coefficients,
restricted to the special fibre of `M`, is invertible at every complex `K` on the geometric
generic fibre of `N` which is bounded below of étale origin.

This is `NearbyCyclesModel.traitChangeInvariance`, with the chart dimension of `N`, after
replacing the special fibre of `N` by its fibre over `κ₂`, which does not affect the base change
morphism. -/
theorem isIso_map_exchangeRight_app_of_isPullback_trait_residueField_of_plusEtaleOrigin
    [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1)) N.generic))}
    (hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj K)) :
    IsIso ((L((M.i)^*⟦Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1)⟧)).map
      ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1)) N.j)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1)) M.j)
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1))
            φ.commSq_j)).app K)) := by
  -- the prime `p`, which is the residual characteristic if it is positive
  refine (exists_prime_ne_dvd_of_natCast_eq_zero κ₁ ‹Fact (ringChar κ₁ ≠ ℓ)›.out).elim
    fun p hp ↦ ?_
  have : Fact p.Prime := ⟨hp.1⟩
  have hp₁ (n : ℕ) (hn : (n : ResidueField R₁) = 0) : p ∣ n := by
    rw [← map_natCast (IsLocalRing.residue R₁), IsLocalRing.residue_eq_zero_iff, ← hb₁,
      RingHom.mem_ker, map_natCast] at hn
    exact hp.2.2 n hn
  -- the chart dimension
  refine (Scheme.Hom.exists_locallyEmbedsInAffineSpace q₁).elim fun m hm ↦ ?_
  -- the model `N` with special fibre over `κ₂`
  have hw : (M.i ≫ φ.total) ≫ q₁ = p₂ ≫ Spec.map (CommRingCat.ofHom (b₂.comp ι)) := by
    rw [Category.assoc, hφ.w, reassoc_of% hMi.w, CommRingCat.ofHom_comp, Spec.map_comp]
  have h := (traitChangeInvariance (PadicAlgCl.integersResidueField ℓ E.1) m).isIso ι hι hun p
    hp₁ (isUnit_natCast_integersResidueField E.1 hp.1 hp.2.1) a₁ a₂ c ha₁ ha₂ halg₁ halg₂ hc b₂
    hb₂ (φ.toGenericWithSpecial (pullback.fst _ _) (pullback.lift (M.i ≫ φ.total) p₂ hw)
      (pullback.lift_fst _ _ _)) q₁ inferInstance inferInstance inferInstance hm g₁ hNj
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _) q₂ g₂ hMj p₂ hMi hφ hgen
    (pullback.lift_snd _ _ _) _ hK
  have h' :=
    isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial _ φ _ _ _ _ h
  transport_exact h'

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
-- the special fibre of `N` over `κ₁` (`hNi`) does not enter the pullback exchange; it is kept for
-- the uniformity of the statement with
-- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers`
/-- **Invariance of nearby cycles under change of strictly henselian trait, `𝔽_E`-coefficients**
(SGA 4½, [Th. finitude], Prop. 3.7, for the torsion coefficients `𝔽_E = 𝒪_E/ϖ`). In the situation
of `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, the pullback exchange
`α : Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` with `𝔽_E`-coefficients is an isomorphism for every `B` whose
restriction `Lε^* B` to the geometric generic fibre of `N` is bounded below of étale origin
(`isIso_map_exchangeRight_app_of_isPullback_trait_residueField_of_plusEtaleOrigin`). -/
theorem isIso_pullbackExchange_app_of_isPullback_trait_residueField [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1)) Y))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj
          (L((N.ε)^*⟦Profinite.continuousMapRingObj.{u}
            (PadicAlgCl.integersResidueField ℓ E.1)⟧).obj B))) :
    IsIso ((φ.pullbackExchange (Profinite.continuousMapRingObj.{u}
      (PadicAlgCl.integersResidueField ℓ E.1))).app B) := by
  have h := isIso_map_exchangeRight_app_of_isPullback_trait_residueField_of_plusEtaleOrigin hι
    hun ha₁ ha₂ halg₁ halg₂ hc hb₁ hb₂ φ q₁ g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen E hB
  have h' := isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app
    (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1)) φ B
    (by exact_mod_proofs h)
  exact_mod_proofs h'

end NearbyCyclesModel.Hom

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {Y : Scheme.{u}}
  {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y Y'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

variable [IsSepClosed k'] [IsSepClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Invariance of nearby cycles under change of trait, `𝒪_E`-coefficients** (SGA 4½,
[Th. finitude], Prop. 3.7): for a model `N` of finite type over `S = Spec k'⟦t⟧` and the change of
trait `Spec K⟦t⟧ ⟶ S` to a separably closed extension `K`, the pullback exchange with
`𝒪_E`-coefficients to the nearby cycles of the base change `N ×_S Spec K⟦t⟧` is an isomorphism at
every `B₀` whose restriction to the geometric generic fibre is bounded constructible. This is the
case `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers`. -/
theorem isIso_pullbackExchange_baseChangeHom_traitMap_padicIntegers
    (hN : N.IsTraitModelOver qN gN) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hB₀ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic)
      (L((N.ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀)) :
    IsIso (((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' K)
      (Category.comp_id _)).pullbackExchange (Profinite.padicIntegersRingObj ℓ E.1)).app B₀) := by
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  have := hN.isSeparated
  have hT := IsTraitModelOver.baseChange hN qN (Category.comp_id qN) (traitMap k' K)
    (Category.comp_id _)
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers
    (PowerSeries.map_injective _ (algebraMap k' K).injective)
    (maximalIdeal_powerSeries_eq_map k' K) (algebraMap_traitGenericField_injective k')
    (algebraMap_traitGenericField_injective K) (isAlgebraic_traitGenericField k')
    (isAlgebraic_traitGenericField K) (traitGenericFieldMap_comp_algebraMap k' K)
    PowerSeries.ker_coeff_eq_max_ideal PowerSeries.ker_coeff_eq_max_ideal _ qN gN
    hN.isPullback_j Y'.hom hN.isPullback_i _ _ hT.isPullback_j _ hT.isPullback_i
    (IsPullback.of_hasPullback qN (traitMap k' K))
    (baseChangeGenericMap_g hN qN (Category.comp_id qN) (traitMap k' K) (Category.comp_id _))
    E hB₀

/-- **Invariance of nearby cycles under change of trait, `𝔽_E`-coefficients** (SGA 4½,
[Th. finitude], Prop. 3.7): for a model `N` of finite type over `S = Spec k'⟦t⟧` and the change of
trait `Spec K⟦t⟧ ⟶ S` to a separably closed extension `K`, the pullback exchange with
`𝔽_E`-coefficients to the nearby cycles of the base change `N ×_S Spec K⟦t⟧` is an isomorphism at
every `B` whose restriction to the geometric generic fibre is bounded below of étale origin. This
is the case `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_residueField`. -/
theorem isIso_pullbackExchange_baseChangeHom_traitMap_residueField
    (hN : N.IsTraitModelOver qN gN) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1)) Y))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj
          (L((N.ε)^*⟦Profinite.continuousMapRingObj.{u}
            (PadicAlgCl.integersResidueField ℓ E.1)⟧).obj B))) :
    IsIso (((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' K)
      (Category.comp_id _)).pullbackExchange (Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1))).app B) := by
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  have := hN.isSeparated
  have hT := IsTraitModelOver.baseChange hN qN (Category.comp_id qN) (traitMap k' K)
    (Category.comp_id _)
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait_residueField
    (PowerSeries.map_injective _ (algebraMap k' K).injective)
    (maximalIdeal_powerSeries_eq_map k' K) (algebraMap_traitGenericField_injective k')
    (algebraMap_traitGenericField_injective K) (isAlgebraic_traitGenericField k')
    (isAlgebraic_traitGenericField K) (traitGenericFieldMap_comp_algebraMap k' K)
    PowerSeries.ker_coeff_eq_max_ideal PowerSeries.ker_coeff_eq_max_ideal _ qN gN
    hN.isPullback_j Y'.hom hN.isPullback_i _ _ hT.isPullback_j _ hT.isPullback_i
    (IsPullback.of_hasPullback qN (traitMap k' K))
    (baseChangeGenericMap_g hN qN (Category.comp_id qN) (traitMap k' K) (Category.comp_id _))
    E hB

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
