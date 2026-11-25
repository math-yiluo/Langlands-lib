/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralTensorTower
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The coefficient portion of the strict open tensor square

Source: Stacks Project, Tags 0E8I, 0GL1 and 0941.
(blueprint: lem-sf-open-quotient-coefficient-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing normalized tensor-tower comparison supplies balancing on every pair
of complexes. Source: Stacks 03EL, 07A4 and 0941. -/
theorem balanced_nonempty (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    Nonempty (Balanced l E W P Q) := by
  obtain ⟨d, hd⟩ := normalizedIntegralTensorTower l E W
  have h : IntegralOnSlice.tower l E W none = reductionTower l E W :=
    IntegralOnSlice.globalTower_eq l E W
  let e : constructibleTensorTotal l E W ⋙ reductionTower l E W ≅
      integralOperationsTensorTowerFunctor l E W :=
    Functor.isoWhiskerLeft (constructibleTensorTotal l E W) (eqToIso h).symm ≪≫ d
  refine ⟨{ iso := e.app (P, Q), coefficients := ?_ }⟩
  intro n p q V x y a
  exact hd P Q n p q V a x y

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsTensorTowerFunctor integralOperationsTensorLevel
  integralOperationsTensorComposite coefficientTotalTensor
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingProjectionUnrestricted scalarReductionExistence scalarReductionExtension

private theorem lift_iso_eq {A B : Type*} [Category A] [Category B]
    (R : A ⥤ B) [R.Full] [R.Faithful] {P Q : A} {H : B}
    (g : R.obj P ≅ H) (k : R.obj Q ≅ H) :
    R.map (R.preimageIso (g ≪≫ k.symm)).hom ≫ k.hom = g.hom := by
  change R.map (R.preimage (g ≪≫ k.symm).hom) ≫ k.hom = _
  rw [Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem restrictionFull
    {D : Type*} [Category D] {J : GrothendieckTopology D}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    [Presheaf.IsLocallySurjective J f.hom] :
    (SheafOfModules.restrictScalars f).Full where
  map_surjective {M N} g := by
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := J) (M₁ := M.val) f.hom N.isSheaf
    refine ⟨⟨e.symm g.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply g.val

private theorem scalarRestrictionFull (W : Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction l E W n).Full := by
  let f := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
  let : Presheaf.IsLocallySurjective (ProEt.topology W) f.hom :=
    completedProjection_locallySurjective l E W n
  exact restrictionFull f

private theorem scalarRestrictionFaithful (W : Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction l E W n).Faithful where
  map_injective := by
    intro M N f g h
    ext V x
    exact congrArg (fun a ↦ a.val.app V x) h

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)
  (tc : OpenSemilinearTensor.TotalComparison l E j o)
  (sc : ScalarCompatibility l E j o)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (r : ScalarComparison l E j o sc st)
  (Q : CochainComplex (scalarReductionSource l E U) ℤ)
  (F : CochainComplex (scalarReductionSource l E X) ℤ)
  (balancingX : Balanced l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F)
  (balancingU : Balanced l E U Q ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))

/-- The finite coefficient data, before adjoining any scalar-unit augmentation.
Source: Stacks 0E8I and 0GL1. -/
structure CoefficientComparisons where
  gamma : (integralOperationsTensorTowerFunctor l E X).obj
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F) ≅
    (extendTower l E j o).obj ((integralOperationsTensorTowerFunctor l E U).obj
      (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
  finiteGamma : ∀ n : ℕ,
    (finiteTotal l E X n).obj
      ((unrestrictedIntegralFiniteComplex l E X n).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q),
       (unrestrictedIntegralFiniteComplex l E X n).obj F) ≅
    ((IntegralOpenReduction.finiteExtension l E j o n).mapHomologicalComplex (.up ℤ)).obj
      ((finiteTotal l E U n).obj
        ((unrestrictedIntegralFiniteComplex l E U n).obj Q,
         (unrestrictedIntegralFiniteComplex l E U n).obj
           ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
  finiteGammaRestriction : ∀ (n : ℕ) (i : ℤ),
    HEq ((gamma.hom.app (op n)).f i)
      ((scalarReductionRestriction l E X n).map ((finiteGamma n).hom.f i) ≫
        (sc.finite n).hom.app
          (((finiteTotal l E U n).obj
            ((unrestrictedIntegralFiniteComplex l E U n).obj Q,
             (unrestrictedIntegralFiniteComplex l E U n).obj
               ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))).X i))
  reduction : ∀ (n : ℕᵒᵖ) (i : ℤ),
    HEq (((balancingX.iso.hom.app n).f i) ≫ ((gamma.hom.app n).f i))
      (((unrestrictedIntegralComplexFunctor l E X n.unop).map (tc.chain Q F).hom).f i ≫
        ((r.iso.hom.app ((OpenSemilinearTensor.total l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).app n).f i ≫
        (IntegralOpenReduction.extension l E j o).map ((balancingU.iso.hom.app n).f i))

/-- Normalized balancing and finite coefficient interchange for the fixed ordinary
open tensor comparison. The assertion has no augmentation, Roos presentation, or
square of augmented maps.

Source: Stacks Project, Modules on Sites, Tag 0E8I; Cohomology on Sites, Tag 0GL1;
cochain coefficient coherence, Tag 03EK; strict systems, Tag 0941.
(blueprint: lem-sf-open-quotient-coefficient-comparisons).

Proof: define gamma by conjugation: inverse balancing on X, reduction of the
fixed integral total comparison, r, and extension of balancing on U. Cancelling
the first balancing isomorphism gives the reduction equation as an equality of
strict tower maps, hence also in every degree and level.

The completed coefficient projection is locally surjective. Scalar restriction
on sheaf modules is therefore full, by local lifting of coefficients, and faithful.
Its functor on complexes is also fully faithful. At each level, compose gamma
with the inverse of the complex comparison induced by sc.finite. Lift that
isomorphism uniquely through scalar restriction to define finiteGamma. Applying
scalar restriction to the lift and cancelling the inverse comparison gives
finiteGammaRestriction. No transition compatibility of finiteGamma beyond the
already strict gamma tower is required by its type. The construction works for
unbounded complexes, including negative degrees, zero complexes and empty opens. -/
theorem openQuotientCoefficientComparisons :
    Nonempty (CoefficientComparisons l E j o tc sc st r Q F balancingX balancingU) := by
  let H := (OpenSemilinearTensor.total l E U).obj
    (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)
  let g := balancingX.iso.symm ≪≫ (reductionTower l E X).mapIso (tc.chain Q F) ≪≫
    r.iso.app H ≪≫ (extendTower l E j o).mapIso balancingU.iso
  have hred : balancingX.iso.hom ≫ g.hom =
      (reductionTower l E X).map (tc.chain Q F).hom ≫ r.iso.hom.app H ≫
        (extendTower l E j o).map balancingU.iso.hom := by
    simp only [g, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.hom_inv_id_assoc]
  let R := fun n ↦ (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let A := fun n ↦ (finiteTotal l E U n).obj
    ((unrestrictedIntegralFiniteComplex l E U n).obj Q,
      (unrestrictedIntegralFiniteComplex l E U n).obj
        ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))
  let k (n : ℕ) :
      (R n).obj
        (((IntegralOpenReduction.finiteExtension l E j o n).mapHomologicalComplex
          (.up ℤ)).obj (A n)) ≅
      (OpenSemilinearTensor.extensionComplex l E j o).obj
        (((scalarReductionRestriction l E U n).mapHomologicalComplex (.up ℤ)).obj (A n)) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (sc.finite n).app ((A n).X i))
      (fun i k _ ↦ ((sc.finite n).hom.naturality ((A n).d i k)).symm)
  let : ∀ n : ℕ, (R n).Faithful := fun n ↦ by
    let : (scalarReductionRestriction l E X n).Faithful := scalarRestrictionFaithful l E X n
    let : (scalarReductionRestriction l E X n).Additive :=
      scalarReductionRestrictionAdditive l E X n
    change ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).Faithful
    infer_instance
  let : ∀ n : ℕ, (R n).Full := fun n ↦ by
    let : (scalarReductionRestriction l E X n).Faithful := scalarRestrictionFaithful l E X n
    let : (scalarReductionRestriction l E X n).Full := scalarRestrictionFull l E X n
    let : (scalarReductionRestriction l E X n).Additive :=
      scalarReductionRestrictionAdditive l E X n
    change ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).Full
    infer_instance
  let fg := fun n ↦ (R n).preimageIso (g.app (op n) ≪≫ (k n).symm)
  refine ⟨{ gamma := g
            finiteGamma := fg
            finiteGammaRestriction := ?_
            reduction := ?_ }⟩
  · intro n i
    have he := lift_iso_eq (R n) (g.app (op n)) (k n)
    exact heq_of_eq (congrArg (fun f ↦ f.f i) he.symm)
  · intro n i
    exact heq_of_eq (congrArg (fun f ↦ (f.app n).f i) hred)

end WeilConjectures.OpenTensorQuotient
