/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# The pullback exchange of nearby cycles along open immersions

The pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a morphism of nearby cycles models whose
morphism of total spaces is weakly étale and whose square of geometric generic fibres is cartesian
is an isomorphism (blueprint `prose-E-03` (1);
`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`). This file records the open
immersion case on bounded constructible complexes and applies it to the deformation to the normal
cone: for an open immersion `f : X ⟶ Y` of `k`-schemes and `J = f⁻¹ I`, the morphism of models
`deformationModelHom f hJ k'` satisfies these hypotheses.

## Main results

- `NearbyCyclesModel.Hom.isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion`: the
  restricted pullback exchange along an open immersion of models is an isomorphism.
- `isPullback_deformationGenericMap`: the square of geometric generic fibres of
  `deformationModelHom` is always cartesian.
- `isOpenImmersion_deformationTotalMap`: for an open immersion `f` and `J = f⁻¹ I`, the morphism of
  total spaces is an open immersion.
- `isIso_deformationModelHom_pullbackExchange`: the pullback exchange of the deformation model
  along an open immersion is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- **The pullback exchange along an open immersion of models, on bounded constructible
complexes**: if the morphism of total spaces is an open immersion and the square of geometric
generic fibres is cartesian, the restricted pullback exchange is an isomorphism. -/
theorem isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion [IsOpenImmersion φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hM hN) :=
  φ.isIso_boundedConstructiblePullbackExchange_of_weaklyEtale ℓ hM hN hj

end NearbyCyclesModel.Hom

/-! ### The deformation to the normal cone along an open immersion -/

section Deformation

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')
  (k' : Type u) [Field k'] [Algebra k k']

/-- The square of total spaces over the square of deformation spaces is cartesian:
`𝒳 = D_J X ×_{D_I Y} 𝒴`. -/
lemma isPullback_deformationTotalMap :
    IsPullback (deformationTotalMap f hJ k') (deformationTotalToSpace X J k')
      (deformationTotalToSpace Y I k') (IdealSheafData.deformationSpaceMap f.left I J hJ) := by
  refine IsPullback.of_right ?_ (deformationTotalMap_toSpace f hJ k')
    (isPullback_deformationTotal Y I k').flip
  rw [deformationTotalMap_toTrait, deformationSpaceMap_deformationSpaceToAffineLine]
  exact (isPullback_deformationTotal X J k').flip

/-- The square of geometric generic fibres of `deformationModelHom` is cartesian. -/
lemma isPullback_deformationGenericMap :
    IsPullback (deformationGenericMap f hJ k') (deformationGenericToTotal X J k')
      (deformationGenericToTotal Y I k') (deformationTotalMap f hJ k') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := deformationTotalToTrait Y I k') ?_
    (deformationGenericMap_toTotal f hJ k') (IsPullback.of_hasPullback _ _).flip
  have e : deformationGenericMap f hJ k' ≫ pullback.snd _ _ =
      pullback.snd (deformationTotalToTrait X J k') (traitGenericPoint k') :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, deformationTotalMap_toTrait]
  exact (IsPullback.of_hasPullback _ _).flip

/-- For an open immersion `f` and `J = f⁻¹ I`, the morphism of deformation spaces
`D_J X ⟶ D_I Y` is an open immersion. -/
lemma isOpenImmersion_deformationSpaceMap [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    IsOpenImmersion (IdealSheafData.deformationSpaceMap f.left I J hJ) :=
  MorphismProperty.of_isPullback
    (IdealSheafData.isPullback_deformationSpaceMap_of_flat f.left I J hJ hJI).flip inferInstance

/-- For an open immersion `f` and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` is an open
immersion. -/
lemma isOpenImmersion_deformationTotalMap [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsOpenImmersion (deformationTotalMap f hJ k') :=
  have := isOpenImmersion_deformationSpaceMap f hJ hJI
  MorphismProperty.of_isPullback (isPullback_deformationTotalMap f hJ k').flip inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The pullback exchange of the deformation to the normal cone along an open immersion**
(blueprint `prose-E-03` (1)): for an open immersion `f : X ⟶ Y` and
`J = f⁻¹ I`, the pullback exchange of `deformationModelHom f hJ k'` is an isomorphism. -/
theorem isIso_deformationModelHom_pullbackExchange [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsIso ((deformationModelHom f hJ k').pullbackExchange Λ) := by
  have : IsOpenImmersion (deformationModelHom f hJ k').total :=
    isOpenImmersion_deformationTotalMap f hJ k' hJI
  exact (deformationModelHom f hJ k').isIso_pullbackExchange_of_isOpenImmersion Λ
    (isPullback_deformationGenericMap f hJ k')

end Deformation

end AlgebraicGeometry.ProEtale.CondensedRing
