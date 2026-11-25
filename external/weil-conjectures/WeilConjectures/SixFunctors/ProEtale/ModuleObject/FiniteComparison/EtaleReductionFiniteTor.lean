/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueReductionBounded

/-!
# Reduction modulo `ℓⁿ`, read on the étale site, preserves `Dctf`

For a bounded constructible `𝒪_E`-complex `K` on `X_proét`, the reduction modulo `ℓⁿ` read on the
small étale site, `Rν_* Φ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`, is bounded constructible of finite Tor amplitude over
`A = 𝒪_E ⧸ ℓⁿ` (`ProEtale.CondensedRing.boundedConstructibleFiniteTor_etaleReduction_of_components`;
this is `ProEtale.CondensedRing.boundedConstructibleFiniteTor_etaleReduction`, stated before the
composite functor is named). This is blueprint `lemma-extension-scalars-preserves-dctf` (3) for the
coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site.

* `Φ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` is `ν^* K'` for a bounded constructible étale complex `K'`
  (`ProEtale.isEtaleOrigin_of_isConstructible`, blueprint
  `theorem-comparison-constructible-sheaves`), and `Rν_* ν^* K' ≅ K'`, so the étale reading is
  bounded constructible.
* Tor amplitude is reflected by `ν^*`
  (`ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`) and is tested on the residue
  field `κ = A ⧸ ϖ` of `A`
  (`ProEtale.DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor`, blueprint
  `theorem-f-shriek-finite-coefficients--1`). Now `(K ⊗ᴸ_{𝒪_E} A) ⊗ᴸ_A κ` is, with scalars
  restricted to `A`, the derived reduction `K ⊗ᴸ_{𝒪_E} 𝔽_E`
  (`ProEtale.nonempty_iso_derivedRestrictScalars_derivedExtendScalars`,
  `ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso`,
  `CategoryTheory.Mod.derivedExtendScalarsCompIso`), which is bounded because `𝒪_E` is a discrete
  valuation ring (`ProEtale.bounded_derivedExtendScalars_integersModPowToResidueField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- **Reduction modulo `ℓⁿ`, read on the étale site, preserves `Dctf`**, stated for the composite
`Rν_* ∘ Φ ∘ ι ∘ red` (see `boundedConstructibleFiniteTor_etaleReduction`): for a bounded
constructible `𝒪_E`-complex `K`, the étale reading `Rν_* Φ (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)` of its reduction is
bounded constructible of finite Tor amplitude. -/
theorem boundedConstructibleFiniteTor_etaleReduction_of_components
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Etale.DerivedCategory.boundedConstructibleFiniteTor
      (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n)) Y.left
      ((R(ν_*(Y.left)[ModuleCat.{u + 1}
          (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))])).obj
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj K)))) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n))
  let red := boundedConstructibleIntegersModPowReduction Y.left ℓ E n
  let Φ := finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)
  let KA := (boundedConstructible _).ι.obj (red.obj K)
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ _).1
    (isEtaleOrigin_of_isConstructible _ (red.obj K).property)
  have := isIso_derivedComparisonAdjunction_unit_app A Y.left K' hK'.1.1
  let e' : (R(ν_*(Y.left)[A])).obj (Φ.functor.obj KA) ≅ K' :=
    (R(ν_*(Y.left)[A])).mapIso e.symm ≪≫
      (asIso ((derivedComparisonAdjunction A Y.left).unit.app K')).symm
  refine ⟨(Etale.DerivedCategory.boundedConstructible A Y.left).prop_of_iso e'.symm hK',
    (Etale.DerivedCategory.finiteTorAmplitude A Y.left).prop_of_iso e'.symm ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · -- for `n = 0` the coefficient ring is zero, and so is every complex
    have : Subsingleton (PadicAlgCl.integersModPow ℓ E 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])
    refine ⟨0, 0, fun F ↦ ?_⟩
    have hZ : IsZero (K' ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
      rw [IsZero.iff_id_eq_zero, ← one_nsmul (𝟙 _)]
      exact Etale.nsmul_id_eq_zero_of_natCast_eq_zero (Subsingleton.elim _ _) _
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_isZero hZ 0,
      _root_.DerivedCategory.TStructure.t.isLE_of_isZero hZ 0⟩
  have : NeZero n := ⟨hn⟩
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  let ρ := PadicAlgCl.integersModPowToResidueField ℓ E n
  have hρ := PadicAlgCl.integersModPowToResidueField_surjective ℓ E n
  let a : ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n) :=
    ULift.up (PadicAlgCl.integersModPowMk ℓ E n ϖ)
  have ha : RingHom.ker ρ.ulift = Ideal.span {a} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    have hx := (Ideal.mem_span_singleton' (x := x.down)).symm.trans
      (Ideal.ext_iff.1 (PadicAlgCl.ker_integersModPowToResidueField ℓ E n hϖ) x.down).symm
    rw [RingHom.mem_ker] at hx
    refine ULift.ext_iff.trans (hx.symm.trans ⟨fun ⟨c, hc⟩ ↦ ⟨ULift.up c, ULift.ext hc⟩,
      fun ⟨c, hc⟩ ↦ ⟨c.down, congrArg ULift.down hc⟩⟩)
  have : (Ideal.span {a}).IsMaximal :=
    ha ▸ RingHom.ker_isMaximal_of_surjective _ fun y ↦ ⟨⟨(hρ y.down).choose⟩,
      ULift.ext (hρ y.down).choose_spec⟩
  have hnil : IsNilpotent a := by
    obtain ⟨m, hm⟩ := PadicAlgCl.isNilpotent_integersModPowMk_of_mem_maximalIdeal ℓ E n
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
    exact ⟨m, ULift.ext hm⟩
  -- `Φ (K ⊗ᴸ A) ⊗ᴸ κ` is bounded
  let ψ := coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ continuous_of_discreteTopology)
    Y.left
  have hKA : _root_.DerivedCategory.TStructure.t.bounded
      ((Mod.extendScalars ψ).leftDerivedFunctor.obj KA) :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((Mod.extendScalars ψ).leftDerivedFunctor.mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n).app K).symm)
      (bounded_derivedExtendScalars_integersModPowToResidueField Y.left ℓ E n K.obj K.property.1)
  let i := (nonempty_iso_derivedRestrictScalars_derivedExtendScalars
    (fun y ↦ ⟨⟨(hρ y.down).choose⟩, ULift.ext (hρ y.down).choose_spec⟩) ha Y.left
    (Φ.functor.obj KA)).some
  have hB := _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y.left) ρ.ulift).mapIso
      ((finiteCoefficientDerivedEquivalenceExtendScalarsIso Y.left hρ ha).app KA).symm ≪≫ i ≪≫
      whiskerLeftIso _ ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheaf (Scheme.ProEt.topology Y.left) A).mapIso
          (Submodule.quotEquivOfEq _ _ ha).toModuleIso)))
    ((Sheaf.restrictScalars (Scheme.ProEt.topology Y.left) ρ.ulift).bounded_mapDerivedCategory_obj
      ((finiteCoefficientModEquivalence Y.left
        (PadicAlgCl.integersResidueField ℓ E)).functor.bounded_mapDerivedCategory_obj hKA))
  obtain ⟨c, d, hcd⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 hB
  refine ⟨c, d, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d K').1 ?_⟩
  exact (DerivedCategory.torAmplitudeIn A Y.left c d).prop_of_iso e.symm
    ((DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor a hnil c d _).2 hcd)

end AlgebraicGeometry.ProEtale.CondensedRing
