/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralFactor
public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisSquare

/-!

# The slice over a generic slice trait as a Galois layer

Let `M` be a model of finite type over `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, `D` a
generic slice trait `S' = Spec R` of `𝔸¹_S` (`AlgebraicGeometry.GenericSliceTrait`) and
`σ : M_{S'} ⟶ M` the slice of `M` over `S'` on the models of the geometric generic fibres
(`NearbyCyclesModel.coordinateSliceTraitHom`). With the algebra structures given by `D`
(`AlgebraicGeometry.GenericSliceTrait.algebraR` etc.), the change of geometric generic fibres of
`σ` is, up to universal homeomorphisms, the Galois layer of the pro-`p` extension `L^sep / L`,
`L = Ω(R) ⊆ Ω'` (`NearbyCyclesModel.Hom.traitChangeModel`). This file records, directly in terms of
`D` (statements through `GenericSliceTrait.toSliceTrait` are very slow to check):

* the model `M₁` (`NearbyCyclesModel.coordinateSliceGaloisModel`) with generic fibre over `Spec L`
  (`NearbyCyclesModel.coordinateSliceGaloisResidue`) and its Galois layer `M₁^{L^sep}`;
* the morphism `ρ : M_{S'} ⟶ M₁^{L^sep}` (`NearbyCyclesModel.coordinateSliceToGaloisLayer`) and
  the morphism `ψ : M₁ ⟶ M` (`NearbyCyclesModel.coordinateSliceGaloisModelHom`), both with
  invertible pullback exchanges;
* the facts on `D` used: `Spec(Ω ⊗_{k'⟦t⟧} R)` is a point and `L^sep / L` is pro-`p`
  (`AlgebraicGeometry.GenericSliceTrait.subsingleton_primeSpectrum`,
  `AlgebraicGeometry.GenericSliceTrait.exists_finrank_eq_pow`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] [IsSepClosed k'] (D : GenericSliceTrait k')

/-- The algebra structure `k'⟦t⟧ ⟶ R` of a generic slice trait. -/
noncomputable abbrev algebraR : Algebra (PowerSeries k') D.R := D.φ.toAlgebra

/-- The algebra structure `R ⟶ Ω'` of a generic slice trait. -/
noncomputable abbrev algebraΩ : Algebra D.R D.Ω := D.a.toAlgebra

/-- The algebra structure `Ω ⟶ Ω'` of a generic slice trait. -/
noncomputable abbrev algebraBaseΩ : Algebra (traitGenericField k') D.Ω := D.ωS.toAlgebra

/-- The algebra structure `k'⟦t⟧ ⟶ Ω'` of a generic slice trait. -/
noncomputable abbrev algebraRΩ : Algebra (PowerSeries k') D.Ω := (D.a.comp D.φ).toAlgebra

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

instance isScalarTower_R : IsScalarTower (PowerSeries k') D.R D.Ω :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance isScalarTower_Ω : IsScalarTower (PowerSeries k') (traitGenericField k') D.Ω :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun D.ωS_comp_algebraMap x).symm

instance faithfulSMul : FaithfulSMul D.R D.Ω :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a

instance isAlgebraic : Algebra.IsAlgebraic D.R D.Ω := D.isAlgebraic_a

omit [IsSepClosed k'] in
/-- The algebra structure of `Ω` over `k'⟦t⟧` is the one given by its structure map. -/
lemma algebra_traitGenericField_eq :
    (algebraMap (PowerSeries k') (traitGenericField k')).toAlgebra =
      (inferInstance : Algebra (PowerSeries k') (traitGenericField k')) :=
  Algebra.algebra_ext _ _ fun _ ↦ rfl

/-- **The geometric generic fibre of `S' ⟶ S` is a single point**: `Spec(Ω ⊗_{k'⟦t⟧} R)` has at
most one point. -/
instance subsingleton_primeSpectrum :
    Subsingleton (PrimeSpectrum (traitGenericField k' ⊗[PowerSeries k'] D.R)) := by
  have h := D.toSliceTrait.subsingleton_primeSpectrum (algebraMap_traitGenericField_injective k')
    (isAlgebraic_traitGenericField k')
  rwa [algebra_traitGenericField_eq] at h

-- the module structure of the finite subextensions goes through the local algebra instances
/-- **The Galois extension `L^sep / L` of a generic slice trait is pro-`p`**, `p` the
characteristic of `k'`: every finite Galois subextension has degree a power of `p`. -/
theorem exists_finrank_eq_pow [Fact (ringChar k').Prime]
    (L' : FiniteGaloisIntermediateField (traitTensorCompositum D.R (traitGenericField k') D.Ω)
      (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)) :
    ∃ n : ℕ, Module.finrank (traitTensorCompositum D.R (traitGenericField k') D.Ω) L' =
      ringChar k' ^ n := by
  have hp : ∀ m : ℕ, (m : IsLocalRing.ResidueField (PowerSeries k')) = 0 → ringChar k' ∣ m :=
    fun m hm ↦ (ringChar.spec k' m).1
      ((PowerSeries.residueFieldEquiv k').injective (by rw [map_natCast, hm, map_zero]))
  have h := D.toSliceTrait.exists_finrank_eq_pow hp
  exact h L'

end AlgebraicGeometry.GenericSliceTrait

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme GenericSliceTrait

attribute [local instance] GenericSliceTrait.algebraR GenericSliceTrait.algebraΩ
  GenericSliceTrait.algebraBaseΩ GenericSliceTrait.algebraRΩ

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-- The slice `σ` lies over the structure map `k'⟦t⟧ ⟶ R` of the generic slice trait. -/
lemma coordinateSliceTraitHom_total_comp :
    (coordinateSliceTraitHom hM b hb D).total ≫ q =
      pullback.snd b D.toAffineLine ≫
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') D.R)) := by
  rw [coordinateSliceTraitHom_total, coordinateSliceTrait_fst_comp b D hb]
  exact congrArg (pullback.snd b D.toAffineLine ≫ ·) D.spec_φ.symm

/-- The model `M₁` with the total space and special fibre of the slice `X'` of `M` over the
generic slice trait, and generic fibre `Z₂ = (X' ×_{S'} T) ×_T Spec L`
(`NearbyCyclesModel.Hom.traitChangeModel`), `T = Spec(Ω ⊗_{k'⟦t⟧} R)`, `L = Ω(R) ⊆ Ω'`. -/
noncomputable abbrev coordinateSliceGaloisModel : NearbyCyclesModel M.generic
    (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b))) :=
  (coordinateSliceTraitHom hM b hb D).traitChangeModel D.Ω (pullback.snd b D.toAffineLine) q g
    hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D)

/-- The structure map `Z₂ ⟶ Spec L` of the generic fibre of `M₁`. -/
noncomputable abbrev coordinateSliceGaloisResidue :
    (coordinateSliceGaloisModel hM b hb D).generic ⟶
      Spec (.of (traitTensorCompositum D.R (traitGenericField k') D.Ω)) :=
  (coordinateSliceTraitHom hM b hb D).traitChangeResidue D.Ω (pullback.snd b D.toAffineLine) q g
    hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D)

/-- The Galois layer `M₁^{L^sep}` of `M₁` along `Z₂ ⟶ Spec L` and `L^sep / L`. -/
noncomputable abbrev coordinateSliceGaloisLayer : NearbyCyclesModel M.generic
    (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b))) :=
  (coordinateSliceGaloisModel hM b hb D).galoisLayer (coordinateSliceGaloisResidue hM b hb D)
    (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)

/-- The morphism of models `ρ : M_{S'} ⟶ M₁^{L^sep}` from the slice to the Galois layer: the
identity of total spaces and the purely inseparable part `r₁` on generic fibres. -/
noncomputable abbrev coordinateSliceToGaloisLayer :
    (coordinateSliceTraitModel b D).Hom (coordinateSliceGaloisLayer hM b hb D)
      (coordinateSliceTraitGeneric hM b hb D) (𝟙 _) :=
  (coordinateSliceTraitHom hM b hb D).toTraitChangeGaloisLayer D.Ω (pullback.snd b D.toAffineLine)
    (pullback.snd _ _) q g hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D)
    pullback.condition (IsPullback.lift_snd _ _ _ _)

/-- The morphism of models `ψ : M₁ ⟶ M`: the nilpotent thickening `r₂` of generic fibres followed
by the weakly étale cartesian part of the slice. -/
noncomputable abbrev coordinateSliceGaloisModelHom :
    (coordinateSliceGaloisModel hM b hb D).Hom M.toGeneric (𝟙 _ ≫ 𝟙 _)
      (𝟙 _ ≫ coordinateSliceTraitSpecial hM b hb D) :=
  ((coordinateSliceTraitHom hM b hb D).traitChangeModelHom D.Ω (pullback.snd b D.toAffineLine) q g
    hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D)).comp
    (coordinateSliceTraitHom hM b hb D).fromCartesian

variable [IsSepClosed k']

/-- The pullback exchange of `ψ : M₁ ⟶ M` is invertible: the nilpotent thickening is a universal
homeomorphism, and the cartesian part is weakly étale base change. -/
theorem isIso_pullbackExchange_coordinateSliceGaloisModelHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic))) :
    IsIso (((coordinateSliceGaloisModelHom hM b hb D).pullbackExchange Λ).app C) :=
  Hom.isIso_pullbackExchange_traitChangeModelHom_comp_fromCartesian_of_eq (Ω := D.Ω)
    (coordinateSliceTraitHom hM b hb D) (pullback.snd b D.toAffineLine) q g hM.isPullback_j.w
    (coordinateSliceTraitHom_total_comp hM b hb D) Λ (coordinateSliceGaloisModel hM b hb D) rfl
    (coordinateSliceGaloisModelHom hM b hb D) HEq.rfl C

omit [IsSepClosed k'] in
/-- The pullback exchange of `ρ : M_{S'} ⟶ M₁^{L^sep}` is invertible: it is the identity of total
spaces and the universal homeomorphism `r₁`, base change of `Spec Ω' ⟶ Spec L^sep`, on generic
fibres. -/
theorem isIso_pullbackExchange_coordinateSliceToGaloisLayer
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic))) :
    IsIso (((coordinateSliceToGaloisLayer hM b hb D).pullbackExchange Λ).app C) := by
  have : IsUniversalHomeomorphism (coordinateSliceToGaloisLayer hM b hb D).generic :=
    (coordinateSliceTraitHom hM b hb D).isUniversalHomeomorphism_traitChangeInsepMap
      (coordinateSliceTraitHom_total_comp hM b hb D) (IsPullback.of_hasPullback _ _)
      hM.isPullback_j (IsPullback.lift_snd _ _ _ _)
  have hj : (coordinateSliceTraitModel b D).j =
      (coordinateSliceToGaloisLayer hM b hb D).generic ≫ (coordinateSliceGaloisLayer hM b hb D).j :=
    by simpa using (coordinateSliceToGaloisLayer hM b hb D).comm_j.symm
  have hM₀ : coordinateSliceTraitModel b D = ⟨(coordinateSliceGaloisLayer hM b hb D).total,
      (coordinateSliceTraitModel b D).generic,
      (coordinateSliceToGaloisLayer hM b hb D).generic ≫ (coordinateSliceGaloisLayer hM b hb D).j,
      (coordinateSliceGaloisLayer hM b hb D).i, 𝟙 _⟩ := by
    rw [← hj]
    rfl
  exact Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (coordinateSliceGaloisLayer hM b hb D) (coordinateSliceToGaloisLayer hM b hb D).generic
    (coordinateSliceTraitModel b D) hM₀ (coordinateSliceToGaloisLayer hM b hb D) HEq.rfl
    HEq.rfl C

omit [IsSepClosed k'] in
/-- The first components of the purely inseparable part `r₁`: `r₁ ≫ q ≫ r₂` is the change of
generic fibres of the cartesian model. -/
@[reassoc]
lemma coordinateSliceToGaloisLayer_generic_fst_fst :
    (coordinateSliceToGaloisLayer hM b hb D).generic ≫
        pullback.fst (coordinateSliceGaloisResidue hM b hb D)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum D.R (traitGenericField k') D.Ω)
            (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)))) ≫
        pullback.fst ((coordinateSliceTraitHom hM b hb D).cartesianModelTensor
          (pullback.snd b D.toAffineLine) q g hM.isPullback_j.w
          (coordinateSliceTraitHom_total_comp hM b hb D))
          (traitTensorCompositumPoint (PowerSeries k') D.R (traitGenericField k') D.Ω) =
      (coordinateSliceTraitHom hM b hb D).toCartesian.generic :=
  (coordinateSliceTraitHom hM b hb D).traitChangeInsepMap_comp_traitChangeGaloisMap_comp
    hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D) pullback.condition
    (IsPullback.lift_snd _ _ _ _)

omit [IsSepClosed k'] in
/-- The component of `r₁` in `Spec L`. -/
@[reassoc]
lemma coordinateSliceToGaloisLayer_generic_fst_snd :
    (coordinateSliceToGaloisLayer hM b hb D).generic ≫
        pullback.fst (coordinateSliceGaloisResidue hM b hb D)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum D.R (traitGenericField k') D.Ω)
            (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)))) ≫
        pullback.snd ((coordinateSliceTraitHom hM b hb D).cartesianModelTensor
          (pullback.snd b D.toAffineLine) q g hM.isPullback_j.w
          (coordinateSliceTraitHom_total_comp hM b hb D))
          (traitTensorCompositumPoint (PowerSeries k') D.R (traitGenericField k') D.Ω) =
      pullback.snd _ _ ≫ traitTensorSepPoint D.R (traitGenericField k') D.Ω ≫
        traitTensorCompositumGalois D.R (traitGenericField k') D.Ω :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

omit [IsSepClosed k'] in
/-- The component of `r₁` in `Spec L^sep`. -/
@[reassoc]
lemma coordinateSliceToGaloisLayer_generic_snd :
    (coordinateSliceToGaloisLayer hM b hb D).generic ≫
        pullback.snd (coordinateSliceGaloisResidue hM b hb D)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum D.R (traitGenericField k') D.Ω)
            (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)))) =
      pullback.snd _ _ ≫ traitTensorSepPoint D.R (traitGenericField k') D.Ω :=
  pullback.lift_snd _ _ _

omit [IsSepClosed k'] in
/-- The composite `M_{S'} ⟶ M₁^{L^sep} ⟶ M₁ ⟶ M` of `ρ`, the projection of the Galois layer and
`ψ` is the slice `σ`, on generic fibres. -/
lemma coordinateSliceToGaloisLayer_generic_comp_galoisModelHom_generic :
    (coordinateSliceToGaloisLayer hM b hb D).generic ≫
        ((coordinateSliceGaloisModel hM b hb D).galoisLayerHom
          (coordinateSliceGaloisResidue hM b hb D)
          (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)).generic ≫
        (coordinateSliceGaloisModelHom hM b hb D).generic =
      (coordinateSliceTraitHom hM b hb D).generic := by
  rw [galoisLayerHom_generic, Hom.comp_generic, Hom.traitChangeModelHom_generic,
    Hom.traitChangeThickening, coordinateSliceToGaloisLayer_generic_fst_fst_assoc]
  exact pullback.lift_fst _ _ _

omit [IsSepClosed k'] in
/-- The inclusion of the geometric generic fibre of a model of finite type over the trait is
quasi-compact and quasi-separated. -/
lemma IsTraitModelOver.quasiCompact_j (h : M.IsTraitModelOver q g) : QuasiCompact M.j :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) h.isPullback_j.flip
    (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k') (traitGenericField k'))))))

omit [IsSepClosed k'] in
@[inherit_doc IsTraitModelOver.quasiCompact_j]
lemma IsTraitModelOver.quasiSeparated_j (h : M.IsTraitModelOver q g) : QuasiSeparated M.j :=
  MorphismProperty.of_isPullback (P := @QuasiSeparated) h.isPullback_j.flip
    (inferInstanceAs (QuasiSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k') (traitGenericField k'))))))

/-- The inclusion of the generic fibre of `M₁` is quasi-compact. -/
instance quasiCompact_coordinateSliceGaloisModel_j :
    QuasiCompact (coordinateSliceGaloisModel hM b hb D).j := by
  have := hM.quasiCompact_j
  rw [Hom.traitChangeModel_j, Hom.traitChangeThickening, Hom.cartesianModel_j]
  have : QuasiCompact (pullback.snd M.j (coordinateSliceTraitHom hM b hb D).total) :=
    inferInstance
  infer_instance

/-- The inclusion of the generic fibre of `M₁` is quasi-separated. -/
instance quasiSeparated_coordinateSliceGaloisModel_j :
    QuasiSeparated (coordinateSliceGaloisModel hM b hb D).j := by
  have := hM.quasiSeparated_j
  rw [Hom.traitChangeModel_j, Hom.traitChangeThickening, Hom.cartesianModel_j]
  have : QuasiSeparated (pullback.snd M.j (coordinateSliceTraitHom hM b hb D).total) :=
    inferInstance
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
