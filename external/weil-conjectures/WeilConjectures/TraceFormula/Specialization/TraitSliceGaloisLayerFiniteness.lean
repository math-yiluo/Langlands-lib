/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsionModels

/-!

# Finiteness of the nearby cycles of the Galois layer of a base change model

Let `M` be a model of finite type over `S = Spec k'⟦t⟧` whose identification factors through the
total space (`ε = j ≫ e`), `M''` its base change to `Spec K⟦t⟧` (`NearbyCyclesModel.baseChange`)
with `K` separably closed, and `N''_{L^sep}` the Galois layer of the change of traits
`M'' ⟶ M` (`NearbyCyclesModel.baseChangeGaloisLayer`). Let `T₀` be a finite discrete ring in which
the characteristic exponent `p` of `k'` is invertible and whose exponent is invertible in `k'`.

* `M''` is a model of finite type over the strictly henselian trait `Spec K⟦t⟧` whose
  identification factors through its total space, so its nearby cycles preserve bounded
  constructible complexes of `T̲₀`-modules (Deligne's finiteness theorem,
  `NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel_of_finite`):
  `NearbyCyclesModel.preservesBoundedConstructible_baseChange_of_finite`.
* The morphism of models `ρ : M'' ⟶ N''_{L^sep}` has invertible pullback exchange
  (`NearbyCyclesModel.isIso_pullbackExchange_baseChangeToGaloisLayer`), hence so do the nearby
  cycles of the Galois layer
  (`NearbyCyclesModel.preservesBoundedConstructible_baseChangeGaloisLayer_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {py : Y ⟶ trait k'}
  (hb : b ≫ py = q) (v : trait K ⟶ Y) (hv : v ≫ py = traitMap k' K)
  (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
  [Finite T₀]

/-- If the identification of `M` factors through its total space, so does that of its base
change `M''`. -/
lemma baseChange_exists_comp_eq_ε (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    ∃ e : (baseChange hM b hb v hv).total ⟶ X,
      (baseChange hM b hb v hv).j ≫ e = (baseChange hM b hb v hv).ε := by
  obtain ⟨e, he⟩ := hε
  refine ⟨pullback.fst b v ≫ e, ?_⟩
  rw [baseChange_ε, ← he, baseChangeGenericMap_j_assoc, baseChange_j]

/-- The morphism of geometric models `M''.geometric ⟶ P.geometric` from the base change to the
Galois layer `P = (N''.toGenericWithSpecial N''.i)_{L^sep}` of the model of the generic fibre of
`N''`: the identity of total spaces and the generic part of `ρ : M'' ⟶ N''_{L^sep}` on generic
fibres. -/
noncomputable def baseChangeGeometricToGaloisLayer :
    (baseChange hM b hb v hv).geometric.Hom
      (((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
        (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
          (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
            (traitGenericField k') (traitGenericField K))).geometric
      (𝟙 (baseChange hM b hb v hv).total) (𝟙 _) where
  total := 𝟙 _
  generic := (baseChangeToGaloisLayer hM b hb v hv).generic
  comm_j := (baseChangeToGaloisLayer hM b hb v hv).comm_j
  comm_i := (baseChangeToGaloisLayer hM b hb v hv).comm_i
  comm_ε := (baseChangeToGaloisLayer hM b hb v hv).comm_j

/-- The pullback exchange of `M''.geometric ⟶ P.geometric` is invertible: it is the identity on
total spaces and a universal homeomorphism on generic fibres. -/
theorem isIso_pullbackExchange_baseChangeGeometricToGaloisLayer
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (baseChange hM b hb v hv).total)
      Ab.{u + 1}) (condensedRingObj Λ (baseChange hM b hb v hv).total))) :
    IsIso (((baseChangeGeometricToGaloisLayer hM b hb v hv).pullbackExchange Λ).app B) :=
  Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
        (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
          (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
            (traitGenericField k') (traitGenericField K))).geometric
    (baseChangeToGaloisLayer hM b hb v hv).generic (baseChange hM b hb v hv).geometric
    (by
      have hj : (baseChange hM b hb v hv).j = (baseChangeToGaloisLayer hM b hb v hv).generic ≫
          (baseChangeGaloisLayer hM b hb v hv).j :=
        (Category.comp_id _).symm.trans (baseChangeToGaloisLayer hM b hb v hv).comm_j.symm
      exact congrArg (fun j ↦ (⟨(baseChange hM b hb v hv).total,
        (baseChange hM b hb v hv).generic, j, (baseChange hM b hb v hv).i,
        (baseChange hM b hb v hv).j⟩ : NearbyCyclesModel _ _)) hj)
    (baseChangeGeometricToGaloisLayer hM b hb v hv) HEq.rfl HEq.rfl B

variable [IsSepClosed K] [HasInvertibleExponent (ULift.{u + 1} T₀) (Spec (.of k'))] {p : ℕ}
  [Fact p.Prime]

/-- **Deligne's finiteness theorem for the base change `M''`, finite coefficients**: the nearby
cycles of `M''` preserve bounded constructible complexes of `T̲₀`-modules. -/
theorem preservesBoundedConstructible_baseChange_of_finite [IsSeparated py]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T₀))
    (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    (baseChange hM b hb v hv).PreservesBoundedConstructible
      (Profinite.continuousMapRingObj T₀) := by
  have : HasInvertibleExponent (ULift.{u + 1} T₀) (Spec (.of K)) :=
    HasInvertibleExponent.of_hom (Spec.map (CommRingCat.ofHom (algebraMap k' K)))
  refine preservesBoundedConstructible_of_isTraitModel_of_finite T₀ (k' := K) (fun m hm ↦ hp m ?_)
    hpT _ (hM.baseChange b hb v hv).isTraitModel (baseChange_exists_comp_eq_ε hM b hb v hv hε)
  rw [← map_natCast (algebraMap k' K)] at hm
  exact (map_eq_zero_iff _ (algebraMap k' K).injective).1 hm

/-- **Finiteness of the nearby cycles of the Galois layer, finite coefficients**: the nearby
cycles of the Galois layer `N''_{L^sep}` preserve bounded constructible complexes of
`T̲₀`-modules. Indeed `Ψ_{N''_{L^sep}} C ≅ L(𝟙)^* Ψ_{N''_{L^sep}} C ≅ Ψ_{M''} (L(𝟙)^* C)` by the
invertible exchange of `ρ : M'' ⟶ N''_{L^sep}`. -/
theorem preservesBoundedConstructible_baseChangeGaloisLayer_of_finite [IsSeparated py]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T₀))
    (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    (baseChangeGaloisLayer hM b hb v hv).PreservesBoundedConstructible
      (Profinite.continuousMapRingObj T₀) := by
  intro C hC
  have h₁ := preservesBoundedConstructible_baseChange_of_finite hM b hb v hv T₀ hp hpT hε _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 X) C hC)
  have := isIso_pullbackExchange_baseChangeToGaloisLayer hM b hb v hv
    (Profinite.continuousMapRingObj T₀) C
  have h₂ := (boundedConstructible _).prop_of_iso (asIso (((baseChangeToGaloisLayer hM b hb v
    hv).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C)).symm h₁
  exact (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId
    (Profinite.continuousMapRingObj T₀) _).app _) h₂

section Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Bounded constructibility along an invertible exchange**: if `φ : Q ⟶ P` is a morphism of
models over `f` and the identity of special fibres whose pullback exchange is invertible at `B`,
and `Ψ_Q (Lf^* B)` is bounded constructible, so is `Ψ_P B`. -/
lemma boundedConstructible_nearbyCycles_obj_of_isIso_pullbackExchange {W W₁ W' : Scheme.{u}}
    {Q : NearbyCyclesModel W₁ W'} {P : NearbyCyclesModel W W'} {f : W₁ ⟶ W}
    (φ : Q.Hom P f (𝟙 W'))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)))
    (hφ : IsIso ((φ.pullbackExchange Λ).app B))
    (hQ : boundedConstructible (condensedRingObj Λ W')
      ((Q.nearbyCycles Λ).obj (L((f)^*⟦Λ⟧).obj B))) :
    boundedConstructible (condensedRingObj Λ W') ((P.nearbyCycles Λ).obj B) :=
  (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarId Λ W').app _)
    ((boundedConstructible _).prop_of_iso (asIso ((φ.pullbackExchange Λ).app B)).symm hQ)

/-- **Nearby cycles of a pullback from the total space are geometric nearby cycles**: for a model
`P` and `ψ : Z ⟶ 𝒳` with `ε ≫ ψ = j`, `Ψ_P (L(𝟙)^* Lψ^* B) ≅ Li^* Rj_* Lj^* B`; in particular the
former is bounded constructible if the latter is. -/
lemma boundedConstructible_nearbyCycles_obj_of_geometric {Z Z' : Scheme.{u}}
    (P : NearbyCyclesModel Z Z') (ψ : Z ⟶ P.total) (hψ : P.ε ≫ ψ = P.j)
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P.total) Ab.{u + 1})
      (condensedRingObj Λ P.total)))
    (hB : boundedConstructible (condensedRingObj Λ Z') ((P.geometric.nearbyCycles Λ).obj B)) :
    boundedConstructible (condensedRingObj Λ Z')
      ((P.nearbyCycles Λ).obj (L((𝟙 Z)^*⟦Λ⟧).obj (L((ψ)^*⟦Λ⟧).obj B))) :=
  (boundedConstructible _).prop_of_iso
    (((L((P.i)^*⟦Λ⟧)).mapIso ((R((P.j)_*⟦Λ⟧)).mapIso
      (((leftDerivedUpperStarComp Λ P.ε ψ).app B).symm ≪≫
        (nonempty_leftDerivedUpperStar_obj_iso_of_eq Λ hψ B).some))).symm ≪≫
      (P.nearbyCycles Λ).mapIso ((leftDerivedUpperStarId Λ Z).app _).symm) hB

end Abstract

/-- **Finiteness of the nearby cycles of the Galois layer of the generic fibre, finite
coefficients**: let `P = (N''.toGenericWithSpecial N''.i)_{L^sep}` be the Galois layer, along
`Z₂ ⟶ Spec L` and `L^sep / L`, of the model of the generic fibre `Z₂` of `N''`. For every bounded
constructible complex `B` of `T̲₀`-modules on the total space `𝒳''` of `M''`, the nearby cycles
`Ψ_P (L(𝟙)^* Lj^* B)` of the pullback of `B` to `Z₂` are bounded constructible. Indeed they are
the geometric nearby cycles of `P`, which agree with those of `M''` through the universal
homeomorphism of generic fibres `ρ`, and Deligne's finiteness theorem applies to `M''` over
the trait `Spec K⟦t⟧`. -/
theorem boundedConstructible_nearbyCycles_galoisLayer_baseChangeGaloisModel_of_finite
    [IsSeparated py] (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T₀))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (baseChange hM b hb v hv).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T₀)
        (baseChange hM b hb v hv).total)))
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T₀)
        (baseChangeSpecial b v).left)
      (((((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
        (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
          (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
            (traitGenericField k') (traitGenericField K))).nearbyCycles
              (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 (baseChangeGaloisModel hM b hb v hv).generic)^*⟦Profinite.continuousMapRingObj
          T₀⟧).obj (L(((baseChangeGaloisModel hM b hb v hv).j)^*⟦Profinite.continuousMapRingObj
            T₀⟧).obj B))) := by
  have : HasInvertibleExponent (ULift.{u + 1} T₀) (Spec (.of K)) :=
    HasInvertibleExponent.of_hom (Spec.map (CommRingCat.ofHom (algebraMap k' K)))
  have hpK : ∀ m : ℕ, (m : K) = 0 → p ∣ m := fun m hm ↦ hp m (by
    rw [← map_natCast (algebraMap k' K)] at hm
    exact (map_eq_zero_iff _ (algebraMap k' K).injective).1 hm)
  have h₁ := boundedConstructible_geometricNearbyCycles_obj_of_finite T₀ (k' := K) hpK hpT _
    (hM.baseChange b hb v hv).isTraitModel
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 _) B hB)
  have h₂ := boundedConstructible_nearbyCycles_obj_of_isIso_pullbackExchange _
    (baseChangeGeometricToGaloisLayer hM b hb v hv) B
    (isIso_pullbackExchange_baseChangeGeometricToGaloisLayer hM b hb v hv _ B) h₁
  exact boundedConstructible_nearbyCycles_obj_of_geometric _
    (((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
      (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K)))
    (baseChangeGaloisModel hM b hb v hv).j
    ((Category.assoc _ _ _).trans (congrArg _ (Category.id_comp _))) B h₂

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
