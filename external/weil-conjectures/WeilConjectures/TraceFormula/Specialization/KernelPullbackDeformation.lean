/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.KernelPullback
public import WeilConjectures.TraceFormula.Specialization.UniversalKernel
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.Tactic.FirstOrderApply

/-!

# The specialized coefficient as a section of the kernel, on the deformation

For a correspondence `c` contracting at `y`, with compact-support exchanges `ν_c` of the support
and `ν_{p₁}` of the first projection, this file defines the specializations
`𝔥 : Ψ_{X×X} RHom(p₂^* K, p₁^! K) ⟶ RHom(p₂'^* K', p₁'^! K')` (`homSpecialization`) and
`𝔥_c` on the support (`IsContractingAt.supportHomSpecialization`), and proves the identity

`𝔥_c S_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`

of blueprint `lemma-section-specialized-correspondence`
(`IsContractingAt.map_exceptionalHomIso_inv_comp_supportHomSpecialization`), from the first identity
of blueprint `lemma-nearby-cycles-universal-kernel` and the compatibility of `β_c` with the
projection formula (blueprint `lemma-compatibilities-base-change-maps` (2)), taken as hypotheses.
It also identifies the unit of the lax monoidal structure of nearby cycles with the
specialization unit (`NearbyCyclesModel.nearbyCyclesLaxMonoidal_ε`,
`IsContractingAt.laxMonoidal_ε_specialization`), the form in which `σ_C` enters the section of the
specialized coefficient, proved under the same hypotheses
(`IsContractingAt.curry_comp_eq_unit_comp_map_comp`).

The special support is written `prod.lift γ₁ γ₂` rather than `(specialCorrespondence k').support`:
both have the same value, but the second has source `(specialCorrespondence k').C`, and mixing the
two spellings of the special fibre in one composite makes the unifier compare the monoidal
structures of the two categories of complexes, which does not terminate in reasonable time.

-/

@[expose] public section
universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

-- the unit comparisons of the derived pullbacks are identified by unfolding
/-- The unit of the lax monoidal structure of nearby cycles is the specialization unit. -/
lemma nearbyCyclesLaxMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (M.nearbyCycles Λ) (M.nearbyCyclesLaxMonoidal Λ) =
      M.unit Λ := by
  have hε (Y Z : Scheme.{u}) (f : Y ⟶ Z) :
      Functor.LaxMonoidal.ε (f)^*⟦Λ⟧.leftDerivedFunctor =
        (leftDerivedUpperStarUnitIso Λ f).inv := rfl
  unfold nearbyCyclesLaxMonoidal
  erw [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_ε,
    Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  simp only [hε, unit, Functor.comp_map, Functor.map_comp, Category.assoc]
  congr 4

end

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k] [Field k'] [Fact (ringChar k ≠ ℓ)]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

/-- The lax monoidal structure of nearby cycles on bounded constructible complexes. -/
@[instance_reducible]
noncomputable def boundedConstructibleNearbyCyclesLaxMonoidal
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    (boundedConstructibleNearbyCycles hP).LaxMonoidal :=
  @ObjectProperty.laxMonoidalLift _ _ _ _ _ _ (boundedConstructible _) _
    (boundedConstructible _) _ (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (M.nearbyCyclesLaxMonoidal (Profinite.padicAlgClRingObj ℓ)) _

omit [IsSeparated X.hom] [IsSeparated X'.hom] in
/-- The unit of the lax monoidal structure of nearby cycles on bounded constructible complexes is
the specialization unit. -/
lemma boundedConstructibleNearbyCyclesLaxMonoidal_ε
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (boundedConstructibleNearbyCycles hP)
      (boundedConstructibleNearbyCyclesLaxMonoidal hP) = boundedConstructibleUnit ℓ hP :=
  ObjectProperty.hom_ext _ (nearbyCyclesLaxMonoidal_ε _ M)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal

section

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

/-- The lax monoidal structure of the specialization. -/
@[instance_reducible]
noncomputable def specializationLaxMonoidal : (specialization (ℓ := ℓ) k' x).LaxMonoidal :=
  NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal _

/-- The lax monoidal structure of the specialization of `X ⨯ X`. -/
@[instance_reducible]
noncomputable def specializationProdLaxMonoidal :
    (specializationProd (ℓ := ℓ) k' x).LaxMonoidal :=
  NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal _

end

attribute [local instance] specializationLaxMonoidal specializationProdLaxMonoidal
  boundedConstructibleBraiding

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

/-- The pullback exchange `α_c : c_s^* Ψ_{X×X} ⟶ Ψ_C c^*` of the support. -/
noncomputable def supportPullbackExchange :
    specializationProd (ℓ := ℓ) k' (y ≫ c.c₁) ⋙
        boundedConstructibleUpperStar _ ℓ (prod.lift (hc.specialLeg₁ k') (hc.specialLeg₂ k')) ⟶
      boundedConstructibleUpperStar _ ℓ c.support ⋙ specialization k' y :=
  (deformationProdLiftModelHom k' c.c₁ hc.ker_map_le_c₁ c.c₂ hc.ker_map_le_c₂
    (C := c.C) (K := y.left.ker)).boundedConstructiblePullbackExchange ℓ
    (f := c.support) (f' := (prod.lift (hc.specialLeg₁ k') (hc.specialLeg₂ k')))
    ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel c.C y.left.ker k')
      (deformationModel_exists_comp_ε c.C y.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
      (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k'))


end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] specializationLaxMonoidal specializationProdLaxMonoidal
  boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

/-- The pullback exchange `α_{p₂} : Lp₂'^* Ψ_X ⟶ Ψ_{X×X} Lp₂^*` of the second projection. -/
noncomputable def prodSndPullbackExchange :
    specialization (ℓ := ℓ) k' x ⋙ boundedConstructibleUpperStar _ ℓ
        (prod.snd : deformationSpecialFibre X x.left.ker k' ⨯
          deformationSpecialFibre X x.left.ker k' ⟶ _) ⟶
      boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X) ⋙ specializationProd k' x :=
  (deformationProdSndModelHom X x.left.ker X x.left.ker k').boundedConstructiblePullbackExchange ℓ
    (f := prod.snd) (f' := prod.snd)
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))

/-- A compact-support exchange `ν_{p₁} : Rp₁'_! Ψ_{X×X} ⟶ Ψ_X Rp₁_!` for the first projections. -/
abbrev ProdFstCompactSupportExchange :=
  specializationProd (ℓ := ℓ) k' x ⋙ boundedConstructibleLowerShriek ℓ
      (prod.fst : deformationSpecialFibre X x.left.ker k' ⨯
        deformationSpecialFibre X x.left.ker k' ⟶ _) ⟶
    boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ X ⟶ X) ⋙ specialization k' x

variable {k' x}

/-- The specialization `𝔥 : Ψ_{X×X} RHom(p₂^* K, p₁^! K) ⟶ RHom(p₂'^* K', p₁'^! K')` of the
internal hom (blueprint `lemma-nearby-cycles-universal-kernel`): the mate of `Ψ(ev) ∘ μ`,
precomposed with `α_{p₂}` and postcomposed with the exceptional exchange `β_{p₁}` of `ν_{p₁}`. -/
noncomputable def homSpecialization (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' x)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specializationProd k' x).obj
        ((ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ prod.snd).obj ((specialization k' x).obj K))).obj
        ((boundedConstructibleUpperShriek ℓ prod.fst).obj ((specialization k' x).obj K)) :=
  MonoidalClosed.curry ((prodSndPullbackExchange (ℓ := ℓ) k' x).app K ▷ _ ≫
    Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
    (specializationProd k' x).map ((ihom.ev _).app _) ≫
    (exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] specializationLaxMonoidal specializationProdLaxMonoidal
  boundedConstructibleBraiding

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

/-- The specialization
`𝔥_c : Ψ_C RHom(c^* p₂^* K, c^! p₁^! K) ⟶ RHom(c_s^* p₂'^* K', c_s^! p₁'^! K')`
on the support: the mate of `Ψ_C(ev) ∘ μ`, precomposed with `α_{c₂} = α_c ∘ c_s^* α_{p₂}` and
postcomposed with `β_{c₁} = c_s^! β_{p₁} ∘ β_c`. -/
noncomputable def supportHomSpecialization (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' (y ≫ c.c₁)) :
    𝐒.obj ((ihom (𝐋.obj 𝐀)).obj (𝐔.obj 𝐁)) ⟶ (ihom (𝐋'.obj 𝐀')).obj (𝐔'.obj 𝐁') :=
  MonoidalClosed.curry ((𝐋'.map ((prodSndPullbackExchange (ℓ := ℓ) k' (y ≫ c.c₁)).app K) ≫
      (hc.supportPullbackExchange k').app 𝐀) ▷ 𝐒.obj ((ihom (𝐋.obj 𝐀)).obj (𝐔.obj 𝐁)) ≫
    Functor.LaxMonoidal.μ 𝐒 (𝐋.obj 𝐀) ((ihom (𝐋.obj 𝐀)).obj (𝐔.obj 𝐁)) ≫
    𝐒.map ((ihom.ev (𝐋.obj 𝐀)).app (𝐔.obj 𝐁)) ≫
    (exceptionalExchange ℓ c.support (𝛄) νc).app 𝐁 ≫
    𝐔'.map ((exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K))

set_option quotPrecheck false in
local notation "𝛃" => exceptionalExchange ℓ c.support (𝛄)
set_option quotPrecheck false in
local notation "𝐒𝐏" => specializationProd (ℓ := ℓ) k' (y ≫ c.c₁)

/-- The inverse `τ_{c_s} : c_s^! RHom(A', B') ⟶ RHom(c_s^* A', c_s^! B')` of the exceptional
internal hom exchange of the special support. -/
noncomputable def specialExceptionalHomInv :
    𝐔'.obj ((ihom 𝐀').obj 𝐁') ⟶ (ihom (𝐋'.obj 𝐀')).obj (𝐔'.obj 𝐁') :=
  haveI := Verdier.isIso_exceptionalHomMap_of_isIso
    (boundedConstructibleUpperShriekAdjunction ℓ (𝛄))
    (boundedConstructibleExceptionalProjection ℓ (𝛄)) 𝐀' 𝐁'
  inv (Verdier.exceptionalHomMap
    (boundedConstructibleUpperShriekAdjunction ℓ (𝛄))
    (boundedConstructibleExceptionalProjection ℓ (𝛄)) 𝐀' 𝐁')

-- matching the abstract lemma against the concrete composites
/-- **The specialized coefficient as a section of the kernel** (blueprint
`lemma-section-specialized-correspondence`, the displayed identity
`𝔥_c S_C(λ_{c_η,K}) = λ_{c_s,K'} c_s^! ρ β_c(P_X)`), for compact-support exchanges `ν_c` of the
support and `ν_{p₁}` of the first projection and dualizing data `D`, given the first identity
`𝔥 S(λ_K) = λ_{K'} ρ` of blueprint `lemma-nearby-cycles-universal-kernel` (`h₁`) and the
compatibility of `β_c` with the projection formula (blueprint
`lemma-compatibilities-base-change-maps` (2), `hβ`). Here `λ_c = τ_c ∘ c^! κ_{K,K}`, for `τ_c` the
inverse of the exceptional internal hom exchange. -/
theorem map_exceptionalHomIso_inv_comp_supportHomSpecialization
    (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' (y ≫ c.c₁))
    (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)
    (h₁ : 𝐒𝐏.map (kunnethVerdierMap ℓ K K) ≫ homSpecialization νp K =
      universalKernelSpecialization k' (y ≫ c.c₁) D K ≫ kunnethVerdierMap ℓ 𝐊' 𝐊')
    (hβ : (hc.supportPullbackExchange k').app 𝐀 ▷ 𝐒.obj (𝐔.obj 𝐇) ≫
        Functor.LaxMonoidal.μ 𝐒 (𝐋.obj 𝐀) (𝐔.obj 𝐇) ≫
        𝐒.map (Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ c.support)
          (boundedConstructibleExceptionalProjection ℓ c.support) 𝐀 𝐇) ≫
        (𝛃 νc).app (𝐀 ⊗ 𝐇) =
      𝐋'.obj (𝐒𝐏.obj 𝐀) ◁ (𝛃 νc).app 𝐇 ≫
        Verdier.exceptionalTensorMap (boundedConstructibleUpperShriekAdjunction ℓ
            (𝛄))
          (boundedConstructibleExceptionalProjection ℓ
            (𝛄)) (𝐒𝐏.obj 𝐀) (𝐒𝐏.obj 𝐇) ≫
        𝐔'.map (Functor.LaxMonoidal.μ 𝐒𝐏 𝐀 𝐇)) :
    𝐒.map (𝐔.map (kunnethVerdierMap ℓ K K) ≫ (c.exceptionalHomIso 𝐀 𝐁).inv) ≫
        supportHomSpecialization νc νp =
      (𝛃 νc).app (externalProduct ℓ K (verdierDual ℓ K)) ≫
        𝐔'.map (universalKernelSpecialization k' (y ≫ c.c₁) D K) ≫
        𝐔'.map (kunnethVerdierMap ℓ 𝐊' 𝐊') ≫ specialExceptionalHomInv := by
  fo_have hX := Verdier.map_inv_exceptionalHomMap_comp_eq using
    (boundedConstructibleUpperShriekAdjunction ℓ c.support),
    (boundedConstructibleExceptionalProjection ℓ c.support),
    (boundedConstructibleUpperShriekAdjunction ℓ (𝛄)),
    (boundedConstructibleExceptionalProjection ℓ (𝛄)),
    (hc.supportPullbackExchange k'), (𝛃 νc), 𝐀, 𝐁, 𝐀', 𝐁',
    ((prodSndPullbackExchange (ℓ := ℓ) k' (y ≫ c.c₁)).app K),
    ((exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K), hβ
  unfold homSpecialization at h₁
  unfold supportHomSpecialization specialExceptionalHomInv Correspondence.exceptionalHomIso
  fo_apply map_externalDuality_comp_eq using _, _, _, _, _, hX, _, _, _, h₁

/-- The unit `ε` of the lax monoidal structure of the specialization of `C` is the specialization
unit `σ_C`. -/
lemma laxMonoidal_ε_specialization :
    Functor.LaxMonoidal.ε 𝐒 = supportSpecializationUnit (ℓ := ℓ) (y := y) k' :=
  NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal_ε _

-- matching the abstract lemma against the concrete composites
/-- **The section of the specialized coefficient** (blueprint
`lemma-section-specialized-correspondence`, second part): if `u : c^* p₂^* K ⟶ c^! p₁^! K`
corresponds to the section `k_u : ℚ̄_ℓ ⟶ c^! (K ⊠ D K)`, that is `λ_c ∘ k_u` is the name of `u`,
then the specialized coefficient `u_s = β_{c₁} ∘ Ψ_C(u) ∘ α_{c₂}` corresponds to
`c_s^! ρ ∘ β_c ∘ Ψ_C(k_u) ∘ σ_C`, under the same hypotheses as
`map_exceptionalHomIso_inv_comp_supportHomSpecialization`. The specialization unit `σ_C` appears as
the unit `ε` of the lax monoidal structure (`laxMonoidal_ε_specialization`). -/
theorem curry_comp_eq_unit_comp_map_comp
    (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
    (νp : ProdFstCompactSupportExchange (ℓ := ℓ) k' (y ≫ c.c₁))
    (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)
    (h₁ : 𝐒𝐏.map (kunnethVerdierMap ℓ K K) ≫ homSpecialization νp K =
      universalKernelSpecialization k' (y ≫ c.c₁) D K ≫ kunnethVerdierMap ℓ 𝐊' 𝐊')
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
      Functor.LaxMonoidal.ε 𝐒 ≫ 𝐒.map ku ≫ (𝛃 νc).app (externalProduct ℓ K (verdierDual ℓ K)) ≫
        𝐔'.map (universalKernelSpecialization k' (y ≫ c.c₁) D K) ≫
        𝐔'.map (kunnethVerdierMap ℓ 𝐊' 𝐊') ≫ specialExceptionalHomInv := by
  fo_have hX := Verdier.map_inv_exceptionalHomMap_comp_eq using
    (boundedConstructibleUpperShriekAdjunction ℓ c.support),
    (boundedConstructibleExceptionalProjection ℓ c.support),
    (boundedConstructibleUpperShriekAdjunction ℓ (𝛄)),
    (boundedConstructibleExceptionalProjection ℓ (𝛄)),
    (hc.supportPullbackExchange k'), (𝛃 νc), 𝐀, 𝐁, 𝐀', 𝐁',
    ((prodSndPullbackExchange (ℓ := ℓ) k' (y ≫ c.c₁)).app K),
    ((exceptionalExchange ℓ (prod.fst : X ⨯ X ⟶ X) prod.fst νp).app K), hβ
  unfold homSpecialization at h₁
  unfold specialExceptionalHomInv Correspondence.exceptionalHomIso at *
  fo_apply curry_comp_eq_of_section using _, _, _, _, _, _, _,
    (by exact MonoidalClosed.uncurry_curry _), hX, _, _, _, h₁, _, _, hk

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
