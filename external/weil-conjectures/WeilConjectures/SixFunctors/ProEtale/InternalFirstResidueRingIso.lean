/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import Mathlib.CategoryTheory.Sites.LocallyBijective

set_option linter.privateModule false

/-! # The coefficient isomorphism for the first residue -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

-- The comparison is made on the point, before pulling coefficients back to a scheme.
open IntegralModelsStacks

private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse A)

private abbrev constantContinuousMap (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj A ⟶ continuousAb A :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous A)

private instance constantContinuousMap_mon (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : IsMonHom (constantContinuousMap A) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) (constantToContinuous A)

private theorem constantContinuousMap_isIso (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (constantContinuousMap A) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (FiniteDiscreteOrdinary.pointConstants A) :=
    J.W_of_isLocallyBijective (FiniteDiscreteOrdinary.pointConstants A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map
      (FiniteDiscreteOrdinary.pointConstants A)) := (J.W_iff _).mp hφ
  have h : IsIso (FiniteConstantModel.scalarToContinuous A) := by
    change IsIso ((presheafToSheaf J Ab.{u + 1}).map
      (FiniteDiscreteOrdinary.pointConstants A) ≫
        (sheafificationAdjunction J Ab.{u + 1}).counit.app (continuousAb A))
    infer_instance
  have hc := IntegralModelsStacks.pointConstantAbIso_scalar A
  have : IsIso ((IntegralModelsStacks.pointConstantAbIso A).hom ≫
      constantContinuousMap A) := by rw [hc]; exact h
  have heq : constantContinuousMap A =
      (IntegralModelsStacks.pointConstantAbIso A).inv ≫
        FiniteConstantModel.scalarToContinuous A := by
    rw [← hc, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

private theorem constantContinuousMap_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    constantContinuousMap A ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (show Profinite.continuousMapRingSheafOfUniverse A ⟶
          Profinite.continuousMapRingSheafOfUniverse B from
          ⟨{ app := fun S ↦ RingCat.ofHom
              (ULift.ringEquiv.symm.toRingHom.comp
                ((f.compLeftContinuous S.unop hf).comp ULift.ringEquiv.toRingHom))
             naturality := fun _ _ _ ↦ rfl }⟩) =
      discreteMap f ≫ constantContinuousMap B := by
  let J := coherentTopology Profinite.{u}
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V := GrothendieckTopology.instPreservesSheafification _ _
  let g : CommRingCat.of (ULift.{u + 1} A) ⟶
      CommRingCat.of (ULift.{u + 1} B) := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hn := (constantCommuteCompose J V).inv.naturality g
  have hp : (IntegralModelsStacks.pointConstantAbIso A).hom ≫ discreteMap f =
      (constantSheaf J Ab.{u + 1}).map (V.map g) ≫
        (IntegralModelsStacks.pointConstantAbIso B).hom := hn.symm
  apply (cancel_epi (IntegralModelsStacks.pointConstantAbIso A).hom).mp
  rw [← Category.assoc, IntegralModelsStacks.pointConstantAbIso_scalar]
  rw [← Category.assoc, hp]
  rw [Category.assoc, IntegralModelsStacks.pointConstantAbIso_scalar]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (continuousAb B).property
  have hA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (continuousAb A)).apply_symm_apply (FiniteConstantModel.constantFunctions A)
  have hB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (continuousAb B)).apply_symm_apply (FiniteConstantModel.constantFunctions B)
  rw [Adjunction.homEquiv_unit] at hA hB
  change toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous A).hom = _ at hA
  change toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous B).hom = _ at hB
  change _ ≫ ((FiniteConstantModel.scalarToContinuous A).hom ≫ _) =
    _ ≫ (((constantSheaf J Ab.{u + 1}).map (V.map g)).hom ≫
      (FiniteConstantModel.scalarToContinuous B).hom)
  simp only [← Category.assoc]
  have hn' := toSheafify_naturality J
    ((Functor.const Profinite.{u}ᵒᵖ).map (V.map g))
  change (Functor.const Profinite.{u}ᵒᵖ).map (V.map g) ≫
      toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} B))) =
    toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
        ((constantSheaf J Ab.{u + 1}).map (V.map g)).hom at hn'
  rw [hA]
  erw [← hn']
  rw [Category.assoc, hB]
  ext S a
  rfl

private abbrev coefficientAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] := Profinite.continuousCoefficientRingObj A

private theorem continuousMonEq (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Mon.mk (continuousAb A) = Mon.mk (coefficientAb A) := by
  rfl

private def constantCoefficientMap (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj A ⟶ coefficientAb A :=
  constantContinuousMap A ≫ (Mon.forget _).map (eqToHom (continuousMonEq A))

private instance constantCoefficientMap_mon (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : IsMonHom (constantCoefficientMap A) := by
  change IsMonHom (constantContinuousMap A)
  exact constantContinuousMap_mon A

private theorem constantCoefficientMap_isIso (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (constantCoefficientMap A) := by
  let := constantContinuousMap_isIso A
  unfold constantCoefficientMap
  infer_instance

private theorem constantCoefficientMap_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    constantCoefficientMap A ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (show Profinite.continuousCoefficientRingSheaf A ⟶
          Profinite.continuousCoefficientRingSheaf B from
          ⟨{ app := fun S ↦ RingCat.ofHom
              (ULift.ringEquiv.symm.toRingHom.comp
                ((f.compLeftContinuous S.unop hf).comp ULift.ringEquiv.toRingHom))
             naturality := fun _ _ _ ↦ rfl }⟩) =
      discreteMap f ≫ constantCoefficientMap B := by
  have h := constantContinuousMap_naturality f hf
  convert h using 1 <;> rfl

private theorem constantContinuousMap_topology (A : Type u) [CommRing A]
    (t₁ t₂ : TopologicalSpace A) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing A t₁ _) (h₂ : @IsTopologicalRing A t₂ _)
    (he : @continuousAb A _ t₁ h₁ = @coefficientAb A _ t₂ h₂) :
    @constantContinuousMap A _ t₁ h₁ ≫ eqToHom he =
      @constantCoefficientMap A _ t₂ h₂ := by
  subst t₂
  simp only [constantCoefficientMap, eqToHom_map]

private theorem scalarPointMap_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    scalarPointMap l E =
      let := spectralNorm.normedField (Padic l) E
      constantContinuousMap (Padic.coefficientExtensionIntegers l E) := by
  rfl

private theorem mon_eqToIso_inv {C : Type*} [Category C] [MonoidalCategory C]
    {M N : Mon C} (h : M = N) :
    (eqToIso h).inv.hom = eqToHom (congrArg Mon.X h.symm) := by
  subst N
  rfl

private theorem scalarPointMap_absolute (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    scalarPointMap l E ≫ (IntegralConstantModel.pointComparison l E).inv.hom =
      let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      constantCoefficientMap (Padic.coefficientExtensionIntegers l E) := by
  have ht := DerivedNakayama.coefficientTopology l E
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hpc : (IntegralConstantModel.pointComparison l E).inv.hom =
      eqToHom (congrArg Mon.X (IntegralConstantModel.pointEquality l E).symm) :=
    mon_eqToIso_inv (IntegralConstantModel.pointEquality l E)
  rw [scalarPointMap_eq, hpc]
  exact constantContinuousMap_topology (Padic.coefficientExtensionIntegers l E)
    _ _ hti
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (congrArg Mon.X (IntegralConstantModel.pointEquality l E).symm)

private def firstResidueIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
      Mon.mk (discreteObj (Padic.coefficientExtensionRing l E 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := DerivedNakayama.quotientDiscrete l E 1
  let := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let := constantCoefficientMap_isIso (Padic.coefficientExtensionRing l E 1)
  exact (Mon.mkIso' (asIso (constantCoefficientMap
    (Padic.coefficientExtensionRing l E 1)))).symm

private theorem firstResidueIso_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (scalarPointMap l E ≫ (IntegralConstantModel.pointComparison l E).inv.hom) ≫
      DerivedNakayama.reductionRing l E 1 ≫ (firstResidueIso l E).hom.hom =
        discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := DerivedNakayama.quotientDiscrete l E 1
  let := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let := constantCoefficientMap_isIso (Padic.coefficientExtensionRing l E 1)
  rw [scalarPointMap_absolute]
  have h := constantCoefficientMap_naturality
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) continuous_quot_mk
  change constantCoefficientMap _ ≫ DerivedNakayama.reductionRing l E 1 =
    _ ≫ constantCoefficientMap _ at h
  rw [← Category.assoc, h, Category.assoc]
  change _ ≫ (constantCoefficientMap _ ≫ inv (constantCoefficientMap _)) = _
  rw [IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProEtale
