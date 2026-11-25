/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFrobeniusTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientIntegralTrace
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionUniformizerPow
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree

/-! # The integral trace on module sheaves

For the completed coefficient map `𝒪_E^∧ ⟶ 𝒪_F^∧`, the Frobenius unit
`K ⟶ 𝒪_F^∧ ⊗_{𝒪_E^∧} Res K`, `k ↦ ∑ᵢ bᵢ ⊗ cᵢ k`, followed by the multiplication counit
`𝒪_F^∧ ⊗_{𝒪_E^∧} Res K ⟶ K` is multiplication by the constant `∑ᵢ bᵢ cᵢ ∈ 𝒪_F`, which is
nonzero. After a further multiplication it becomes multiplication by a nonzero integer.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- The integral trace on module sheaves: natural maps
`σ : K ⟶ 𝒪_F^∧ ⊗_{𝒪_E^∧} Res K` and `τ : 𝒪_F^∧ ⊗_{𝒪_E^∧} Res K ⟶ K` whose composite is
multiplication by a nonzero integer `N`.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Tag 090W.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).

Proof: `τ` is the counit of extension ⊣ restriction, `s ⊗ k ↦ s k`. For a Frobenius system
`(t, (bᵢ), (cᵢ))` of the completed coefficient map, the Frobenius unit `k ↦ ∑ᵢ bᵢ ⊗ cᵢ k`
followed by `τ` is multiplication by the constant section of `w = ∑ᵢ bᵢ cᵢ ∈ 𝒪_F`, and
`w ≠ 0`. Since `w ∣ ℓ ^ k` in the discrete valuation ring `𝒪_F`, precomposing with
multiplication by `ℓ ^ k / w` gives multiplication by `N = ℓ ^ k`. -/
theorem rationalScalarIntegral_unit_comp_counit :
    ∃ (N : ℕ) (σ : 𝟭 (scalarReductionSource l F W) ⟶
        rationalScalarModuleRestriction l E F ι W ⋙ integralOrdinaryScalar l E F ι W)
      (τ : rationalScalarModuleRestriction l E F ι W ⋙ integralOrdinaryScalar l E F ι W ⟶
        𝟭 (scalarReductionSource l F W)),
      (N : Padic.coefficientExtensionIntegers l F) ≠ 0 ∧
        ∀ M, σ.app M ≫ τ.app M = N • 𝟙 M := by
  classical
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} W
  let : (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} W
  let := ι.toAlgebra
  have hRes : rationalScalarModuleRestriction l E F ι W = SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E F ι W)) := by
    rw [← completedCoefficientMap_eq_integralCompletedScalarMap l E W F ι]
    rfl
  rw [hRes]
  obtain ⟨d, Φ, κ, hκ, -, ⟨w, hw0, hw⟩, -⟩ :=
    integralCompletedScalarMap_frobeniusSystem_trace l E F ι W
  obtain ⟨k, v, hv⟩ := Padic.exists_mul_eq_natCast_pow l F hw0
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E W F ι
    (integralCompletedScalarMap l E F ι W)
    (integralCompletedScalarMap_existsUnique l E F ι W).exists.choose_spec
  obtain ⟨hobj, hmap, -⟩ := (integralOrdinaryScalarWitness l E F ι W).choose_spec
  let adjF := (Φ.adjunction e.symm).ofNatIsoRight
    (NatIso.ofComponents (fun M ↦ eqToIso (hobj M).symm) fun f ↦ by
      simp [hmap, SheafOfModules.changeOfRingsFunctor])
  obtain ⟨-, -, hO⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E F ι W)
  obtain ⟨a, ha⟩ := hO (integralOrdinaryScalar l E F ι W) hobj hmap
  refine ⟨l ^ k, SheafOfModules.smulSections (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted l F W) (fun V ↦ κ V v) (fun g ↦ hκ g v) ≫
      adjF.unit,
    a.counit, ?_, fun M ↦ ?_⟩
  · intro h
    have h' := congrArg (fun x : Padic.coefficientExtensionIntegers l F ↦ (x : F)) h
    have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[l] F).injective
    exact pow_ne_zero k (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  · let R₀ := SheafOfModules.restrictScalars ((sheafCompose
        (AlgebraicGeometry.Scheme.ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (integralCompletedScalarMap l E F ι W))
    let g := eqToHom (hobj (R₀.obj M)).symm ≫ a.counit.app M
    have hu : adjF.unit.app M = Φ.unitHom M ≫ eqToHom (hobj _).symm := by
      rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
      rfl
    have hg (U : (AlgebraicGeometry.Scheme.ProEt W)ᵒᵖ) (x : M.val.obj U) :
        g.val.app U ((SheafOfModules.toChangeOfRings
          (φ := integralCompletedScalarMap l E F ι W) (R₀.obj M)).app U
          (ModuleCat.FrobeniusData.tmulRes ((integralCompletedScalarMap l E F ι W).hom.app U).hom
            (M.val.obj U) 1 x)) = x := by
      refine (ha (R₀.obj M) M g U x).symm.trans ?_
      rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Adjunction.homEquiv_unit,
        Adjunction.right_triangle_components]
      rfl
    have hkey : adjF.unit.app M ≫ a.counit.app M = Φ.unitHom M ≫ g := by
      rw [hu, Category.assoc]
    rw [NatTrans.comp_app, Category.assoc, hkey]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    erw [SheafOfModules.nsmul_val_app]
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    erw [Φ.unitHom_comp_val_app M g hg U]
    have hs : (∑ i, (Φ.data U).basis i * (Φ.data U).dual i) * κ U v = ((l ^ k : ℕ) : _) := by
      rw [hw U, ← map_mul, hv, map_natCast]
    exact (smul_smul _ _ x).trans ((congrArg (fun r : ((sheafCompose
      (AlgebraicGeometry.Scheme.ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l F W)).obj.obj U ↦ r • x) hs).trans
          (Nat.cast_smul_eq_nsmul _ _ x))

end WeilConjectures
