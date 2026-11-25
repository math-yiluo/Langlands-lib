/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.KernelPullbackDeformation
public import WeilConjectures.TraceFormula.Specialization.UniversalKernelFirst
public import WeilConjectures.Tactic.TransportExact

/-!

# The section defined by the specialized correspondence

For a correspondence `c` contracting at `y`, with compact-support exchanges `ν_c` of the support
and `ν_{p₁}` of the first projection, this file restates the identities of blueprint
`lemma-section-specialized-correspondence` of `KernelPullbackDeformation` with the first
universal-kernel identity `𝔥 S(λ_K) = λ_{K'} ρ` discharged by
`ProEtale.CondensedRing.map_kunnethVerdierMap_comp_eq`, for the exceptional exchange
`β_{p₁}` of `ν_{p₁}` and the specialization `𝔥` of the internal hom
(`ProEtale.CondensedRing.homSpecialization`). The remaining hypotheses are the compatibility
`hκ` of `β_{p₁}` with the exceptional Künneth maps (blueprint
`lemma-base-change-maps-external-duality--1`) and the compatibility `hβ` of `β_c` with the
projection formula (blueprint `lemma-compatibilities-base-change-maps` (2)). The section of the
specialized coefficient is written with the specialization unit `σ_C` of the support, as in the
blueprint: `k_{u_s} = c_s^! ρ β_c Ψ_C(k_u) σ_C`.

## Main results

- `ProEtale.CondensedRing.map_kunnethVerdierMap_comp_homSpecialization`: the first
  universal-kernel identity `𝔥 S(λ_K) = λ_{K'} ρ` for `𝔥 = homSpecialization ν_{p₁} K`.
- `IsContractingAt.map_exceptionalHomIso_inv_comp_supportHomSpecialization_of_kunneth`:
  `𝔥_c Ψ_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`.
- `IsContractingAt.curry_comp_eq_supportSpecializationUnit_comp_map_comp`:
  the section of `u_s` is `c_s^! ρ β_c Ψ_C(k_u) σ_C`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] specializationLaxMonoidal specializationProdLaxMonoidal
  boundedConstructibleBraiding

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {x : RationalPoint X}

/-- **Nearby cycles of the universal kernel**, first identity (blueprint
`lemma-nearby-cycles-universal-kernel`), for the specialization `𝔥` of the internal hom built from
the exceptional exchange `β_{p₁}` of a compact-support exchange `ν_{p₁}`: `𝔥 Sp(λ_K) = λ_{K'} ρ`,
given the compatibility `hκ` of `β_{p₁}` with the exceptional Künneth maps (blueprint
`lemma-base-change-maps-external-duality--1`). -/
theorem map_kunnethVerdierMap_comp_homSpecialization
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' x)
    (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hκ : ((specializationFstExchange k' x).app K ⊗ₘ
        (specializationSndExchange k' x).app (dualizingComplex' ℓ X)) ≫
        Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
        (specializationProd k' x).map (exceptionalKunnethMap ℓ K) ≫
          (exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K =
      _ ◁ (boundedConstructibleUpperStar _ ℓ _).map
          (D.θ (isTraitModelOfBase_deformationModel k' x)) ≫
        exceptionalKunnethMap ℓ ((specialization k' x).obj K)) :
    (specializationProd k' x).map (kunnethVerdierMap ℓ K K) ≫ homSpecialization νp K =
      universalKernelSpecialization k' x D K ≫
        kunnethVerdierMap ℓ ((specialization k' x).obj K) ((specialization k' x).obj K) := by
  have h𝔥 : MonoidalClosed.uncurry (homSpecialization νp K) =
      (prodSndPullbackExchange (ℓ := ℓ) k' x).app K ▷ _ ≫
        Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
        (specializationProd k' x).map ((ihom.ev _).app _) ≫
        (exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K := by
    unfold homSpecialization
    exact MonoidalClosed.uncurry_curry _
  exact map_kunnethVerdierMap_comp_eq k' x D K (exceptionalExchange ℓ prod.fst prod.fst νp) hκ
    (homSpecialization νp K) (by transport_exact h𝔥)

end

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} {hc : c.IsContractingAt y} {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

set_option quotPrecheck false in
local notation "𝐀" => (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
  (prod.snd : X ⨯ X ⟶ X)).obj K
set_option quotPrecheck false in
local notation "𝐁" => (boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K
set_option quotPrecheck false in
local notation "𝐇" => (ihom 𝐀).obj 𝐁
set_option quotPrecheck false in
local notation "𝐊'" => (specialization k' (y ≫ c.c₁)).obj K
set_option quotPrecheck false in
local notation "𝐀'" => (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
  (prod.snd : deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⨯
    deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⟶ _)).obj 𝐊'
set_option quotPrecheck false in
local notation "𝐁'" => (boundedConstructibleUpperShriek ℓ
  (prod.fst : deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⨯
    deformationSpecialFibre X (y ≫ c.c₁).left.ker k' ⟶ _)).obj 𝐊'
set_option quotPrecheck false in
local notation "𝐋" => boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.support
set_option quotPrecheck false in
local notation "𝐔" => boundedConstructibleUpperShriek ℓ c.support
set_option quotPrecheck false in
local notation "𝛄" => prod.lift (hc.specialLeg₁ k') (hc.specialLeg₂ k')
set_option quotPrecheck false in
local notation "𝐋'" => boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
  (𝛄)
set_option quotPrecheck false in
local notation "𝐔'" => boundedConstructibleUpperShriek ℓ (𝛄)
set_option quotPrecheck false in
local notation "𝐒" => specialization (ℓ := ℓ) k' y

set_option quotPrecheck false in
local notation "𝛃" => exceptionalExchange ℓ c.support (𝛄)
set_option quotPrecheck false in
local notation "𝐒𝐏" => specializationProd (ℓ := ℓ) k' (y ≫ c.c₁)

/-- **The specialized coefficient as a section of the kernel** (blueprint
`lemma-section-specialized-correspondence`, (E.19)):
`𝔥_c Ψ_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`. This is
`map_exceptionalHomIso_inv_comp_supportHomSpecialization` with the first universal-kernel identity
discharged by `map_kunnethVerdierMap_comp_homSpecialization`; the remaining hypotheses are the
compatibility `hκ` of `β_{p₁}` with the exceptional Künneth maps and the compatibility `hβ` of
`β_c` with the projection formula. -/
theorem map_exceptionalHomIso_inv_comp_supportHomSpecialization_of_kunneth
    (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' (y ≫ c.c₁))
    (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)
    (hκ : ((specializationFstExchange k' (y ≫ c.c₁)).app K ⊗ₘ
        (specializationSndExchange k' (y ≫ c.c₁)).app (dualizingComplex' ℓ X)) ≫
        Functor.LaxMonoidal.μ 𝐒𝐏 _ _ ≫ 𝐒𝐏.map (exceptionalKunnethMap ℓ K) ≫
          (exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K =
      _ ◁ (boundedConstructibleUpperStar _ ℓ _).map
          (D.θ (isTraitModelOfBase_deformationModel k' (y ≫ c.c₁))) ≫
        exceptionalKunnethMap ℓ 𝐊')
    (hβ : (hc.supportPullbackExchange k').app 𝐀 ▷ 𝐒.obj (𝐔.obj 𝐇) ≫
        Functor.LaxMonoidal.μ 𝐒 (𝐋.obj 𝐀) (𝐔.obj 𝐇) ≫
        𝐒.map (Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ c.support)
          (boundedConstructibleExceptionalProjection ℓ c.support) 𝐀 𝐇) ≫
        (𝛃 νc).app (𝐀 ⊗ 𝐇) =
      𝐋'.obj (𝐒𝐏.obj 𝐀) ◁ (𝛃 νc).app 𝐇 ≫
        Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ (𝛄))
          (boundedConstructibleExceptionalProjection ℓ (𝛄)) (𝐒𝐏.obj 𝐀) (𝐒𝐏.obj 𝐇) ≫
        𝐔'.map (Functor.LaxMonoidal.μ 𝐒𝐏 𝐀 𝐇)) :
    𝐒.map (𝐔.map (kunnethVerdierMap ℓ K K) ≫ (c.exceptionalHomIso 𝐀 𝐁).inv) ≫
        supportHomSpecialization νc νp =
      (𝛃 νc).app (externalProduct ℓ K (verdierDual ℓ K)) ≫
        𝐔'.map (universalKernelSpecialization k' (y ≫ c.c₁) D K) ≫
        𝐔'.map (kunnethVerdierMap ℓ 𝐊' 𝐊') ≫ specialExceptionalHomInv :=
  map_exceptionalHomIso_inv_comp_supportHomSpecialization νc νp D
    (map_kunnethVerdierMap_comp_homSpecialization νp D K hκ) hβ

/-- **The section defined by the specialized correspondence** (blueprint
`lemma-section-specialized-correspondence`, second part): if `u : c^* p₂^* K ⟶ c^! p₁^! K`
corresponds to the section `k_u : ℚ̄_ℓ ⟶ c^! (K ⊠ D K)`, then the specialized coefficient
`u_s = β_{c₁} ∘ Ψ_C(u) ∘ α_{c₂}` corresponds to the section
`k_{u_s} = c_s^! ρ ∘ β_c ∘ Ψ_C(k_u) ∘ σ_C`, with `σ_C` the specialization unit of the support.
This is `curry_comp_eq_unit_comp_map_comp` with the first universal-kernel identity discharged by
`map_kunnethVerdierMap_comp_homSpecialization` and the unit `ε` of the lax monoidal structure
rewritten as `σ_C` (`laxMonoidal_ε_specialization`). -/
theorem curry_comp_eq_supportSpecializationUnit_comp_map_comp
    (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' (y ≫ c.c₁))
    (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)
    (hκ : ((specializationFstExchange k' (y ≫ c.c₁)).app K ⊗ₘ
        (specializationSndExchange k' (y ≫ c.c₁)).app (dualizingComplex' ℓ X)) ≫
        Functor.LaxMonoidal.μ 𝐒𝐏 _ _ ≫ 𝐒𝐏.map (exceptionalKunnethMap ℓ K) ≫
          (exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K =
      _ ◁ (boundedConstructibleUpperStar _ ℓ _).map
          (D.θ (isTraitModelOfBase_deformationModel k' (y ≫ c.c₁))) ≫
        exceptionalKunnethMap ℓ 𝐊')
    (hβ : (hc.supportPullbackExchange k').app 𝐀 ▷ 𝐒.obj (𝐔.obj 𝐇) ≫
        Functor.LaxMonoidal.μ 𝐒 (𝐋.obj 𝐀) (𝐔.obj 𝐇) ≫
        𝐒.map (Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ c.support)
          (boundedConstructibleExceptionalProjection ℓ c.support) 𝐀 𝐇) ≫
        (𝛃 νc).app (𝐀 ⊗ 𝐇) =
      𝐋'.obj (𝐒𝐏.obj 𝐀) ◁ (𝛃 νc).app 𝐇 ≫
        Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ (𝛄))
          (boundedConstructibleExceptionalProjection ℓ (𝛄)) (𝐒𝐏.obj 𝐀) (𝐒𝐏.obj 𝐇) ≫
        𝐔'.map (Functor.LaxMonoidal.μ 𝐒𝐏 𝐀 𝐇))
    (u : 𝐋.obj 𝐀 ⟶ 𝐔.obj 𝐁) (ku : 𝟙_ _ ⟶ 𝐔.obj (externalProduct ℓ K (verdierDual ℓ K)))
    (hk : ku ≫ 𝐔.map (kunnethVerdierMap ℓ K K) ≫ (c.exceptionalHomIso 𝐀 𝐁).inv =
      MonoidalClosed.curry ((ρ_ (𝐋.obj 𝐀)).hom ≫ u)) :
    MonoidalClosed.curry ((ρ_ (𝐋'.obj 𝐀')).hom ≫
        (𝐋'.map ((prodSndPullbackExchange (ℓ := ℓ) k' (y ≫ c.c₁)).app K) ≫
          (hc.supportPullbackExchange k').app 𝐀) ≫ 𝐒.map u ≫
        ((𝛃 νc).app 𝐁 ≫
          𝐔'.map ((exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K))) =
      supportSpecializationUnit (ℓ := ℓ) (y := y) k' ≫ 𝐒.map ku ≫
        (𝛃 νc).app (externalProduct ℓ K (verdierDual ℓ K)) ≫
        𝐔'.map (universalKernelSpecialization k' (y ≫ c.c₁) D K) ≫
        𝐔'.map (kunnethVerdierMap ℓ 𝐊' 𝐊') ≫ specialExceptionalHomInv := by
  have h := curry_comp_eq_unit_comp_map_comp νc νp D
    (map_kunnethVerdierMap_comp_homSpecialization νp D K hκ) hβ u ku hk
  exact h.trans (eq_whisker laxMonoidal_ε_specialization _)

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
