/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionComparisonDescent
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-! Source: Stacks Tags 099M, 09BL and 09BM; blueprint: lem-fix-qcqs-completion-unit-restriction.
This is a separately stated component of the locality argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
private theorem ordinaryCoefficientMap_projection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{t}} (r : S ⟶ T) (n : ℕ) :
    ordinaryCoefficientMap l E r ≫
        limit.π (integralCoefficientSheafSystem l E S) (op n) =
      (ordinaryRingInverse.{t, u} r).map
          (limit.π (integralCoefficientSheafSystem l E T) (op n)) ≫
        ((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} r)).homEquiv _ _).symm
          (ordinaryFiniteRingMap l E r n) := by
  let a := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} r)
  calc
    _ = (a.homEquiv _ _).symm
        (ordinaryCompletedRingMap l E r ≫ (ordinaryRingPush.{t, u} r).map
          (limit.π (integralCoefficientSheafSystem l E S) (op n))) :=
      (a.homEquiv_naturality_right_symm _ _).symm
    _ = (a.homEquiv _ _).symm
        (limit.π (integralCoefficientSheafSystem l E T) (op n) ≫
          ordinaryFiniteRingMap l E r n) :=
      congrArg _ ((ordinaryCompletedRingMap_existsUnique l E r).exists.choose_spec n)
    _ = _ := by
      exact a.homEquiv_naturality_left_symm
        (limit.π (integralCoefficientSheafSystem l E T) (op n))
        (ordinaryFiniteRingMap l E r n)

private theorem ordinaryGood_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{t}) {P Q : Cx l E S none} (e : P ≅ Q)
    (hQ : Good l E S none Q) : Good l E S none P := by
  let R := completedIntegralCommRingSheafUnrestricted l E S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  refine ⟨?_, ?_⟩
  · intro F hF
    exact (hQ.1 F hF).of_iso
      (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e.symm)
  · intro n
    let en := (HomologicalComplex.eval _ _ n).mapIso e
    let et := SheafOfModules.siteSheafTensorRightIso R (P.X n) ≪≫
      (MonoidalCategory.curriedTensor _).flip.mapIso en ≪≫
      (SheafOfModules.siteSheafTensorRightIso R (Q.X n)).symm
    exact (exactFunctor _ _).prop_of_iso et.symm (hQ.2 n)

private theorem ordinaryPull_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{t}} (r : S ⟶ T) (P : (Good l E T none).FullSubcategory) :
    Good l E S none ((ordinaryComplexPull l E r).obj P.obj) :=
  ordinaryGood_of_iso l E S ((ordinaryAmbientComplexIso l E r).app P.obj)
    (IntegralAmbient.pull_good l E r P.obj P.property)

attribute [local irreducible] ordinaryPull ordinaryDerivedPull
  ordinaryComplexCounit ordinaryCoefficientMap tower completion
  completionComparison completionUnit

/-- A normalized restriction comparison carries the specified unit to the specified
unit and consequently preserves completeness.

Source: Stacks Tags 09BL, 09BM, 06YY, 0941 and Bhatt--Scholze Lemma 6.5.8
(blueprint: lem-fix-qcqs-completion-unit-restriction).
Proof: factor a weakly etale map through the identity immersion, and a closed
immersion after the identity weakly etale map. Apply the normalized restriction
models. The finite coefficient projection identity follows by the two naturality
identities for the ring inverse-image adjunction and the defining finite projections
of the completed ring map. The two Roos coordinates imply chain-unit compatibility;
localization on good representatives then gives derived-unit compatibility.
An invertible source unit stays invertible under restriction and the completion
comparison. The canonical-unit criterion on the source and target gives preservation
of derived completeness. -/
theorem qcqsCompletionUnitRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    (∀ (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S] (r : S ⟶ T),
      (WeaklyEtale r ∨ (IsClosedImmersion r ∧ IsCompact ((Set.range r.base)ᶜ))) →
      PreservesFiniteLimits (ordinaryPull l E r) ∧
      PreservesFiniteColimits (ordinaryPull l E r) ∧
      IsIso (ordinaryCoefficientMap l E r) ∧
      (∀ n : ℕ, ordinaryCoefficientMap l E r ≫
          limit.π (integralCoefficientSheafSystem l E S) (op n) =
        (ordinaryRingInverse.{t, u} r).map
            (limit.π (integralCoefficientSheafSystem l E T) (op n)) ≫
          ((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} r)).homEquiv _ _).symm
              (ordinaryFiniteRingMap l E r n)) ∧
      (∃ (τ : tower l E T none ⋙
          (Functor.whiskeringRight ℕᵒᵖ (Cx l E T none) (Cx l E S none)).obj
            (ordinaryComplexPull l E r) ≅
          ordinaryComplexPull l E r ⋙ tower l E S none)
        (χ : roos l E T none ⋙ ordinaryComplexPull l E r ≅
          ordinaryComplexPull l E r ⋙ roos l E S none)
        (hgood : ∀ P : (Good l E T none).FullSubcategory,
          Good l E S none ((ordinaryComplexPull l E r).obj P.obj))
        (α : completion l E T none ⋙ ordinaryDerivedPull l E r ≅
          ordinaryDerivedPull l E r ⋙ completion l E S none),
        (∀ (P : Cx l E T none) (n : ℕ),
          (ordinaryComplexPull l E r).map (((augmentation l E T none).app P).app (op n)) ≫
              (τ.hom.app P).app (op n) =
            ((augmentation l E S none).app ((ordinaryComplexPull l E r).obj P)).app (op n)) ∧
        (∀ P : Cx l E T none,
          χ.hom.app P ≫ CochainComplex.mappingCocone.fst
              (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P)) =
            (ordinaryComplexPull l E r).map
                (CochainComplex.mappingCocone.fst (ordinaryRoosEndomorphism l E P)) ≫
              piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n)) ≫
              Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))) ∧
        (∀ (P : Cx l E T none) (i : ℤ),
          (χ.hom.app P).f i ≫
              (CochainComplex.mappingCocone.snd
                (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P))).v
                  i (i + -1) rfl =
            (ordinaryPull l E r).map
                ((CochainComplex.mappingCocone.snd (ordinaryRoosEndomorphism l E P)).v
                  i (i + -1) rfl) ≫
              (piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n))).f (i + -1) ≫
              (Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))).f (i + -1)) ∧
        (∀ P : (Good l E T none).FullSubcategory,
          (ordinaryDerivedPull l E r).map ((completionComparison l E T none).hom.app P) ≫
              ordinaryComplexCounit l E r ((roos l E T none).obj P.obj) ≫
              DerivedCategory.Q.map (χ.hom.app P.obj) =
            α.hom.app ((qGood l E T none).obj P) ≫
              (completion l E S none).map (ordinaryComplexCounit l E r P.obj) ≫
              (completionComparison l E S none).hom.app
                ⟨(ordinaryComplexPull l E r).obj P.obj, hgood P⟩) ∧
        (∀ H : D l E T none,
          (ordinaryDerivedPull l E r).map ((completionUnit l E T none).app H) ≫
              α.hom.app H =
            (completionUnit l E S none).app ((ordinaryDerivedPull l E r).obj H))) ∧
      (∀ H : D l E T none, IsComplete l E T none H →
        IsComplete l E S none ((ordinaryDerivedPull l E r).obj H)))
 := by
  intro S _ _ r hr
  obtain ⟨V, hVqc, hVqs, s, i, hs, hi, heq⟩ :
      ∃ (V : Scheme.{t}), CompactSpace V ∧ QuasiSeparatedSpace V ∧
        ∃ (s : S ⟶ V) (i : V ⟶ T), WeaklyEtale s ∧ IsImmersion i ∧ s ≫ i = r := by
    rcases hr with h | ⟨h, _⟩
    · exact ⟨T, inferInstance, inferInstance, r, 𝟙 T, h, inferInstance,
        Category.comp_id r⟩
    · let := h
      exact ⟨S, inferInstance, inferInstance, 𝟙 S, r, inferInstance, inferInstance,
        Category.id_comp r⟩
  let := hVqc
  let := hVqs
  let := hs
  let := hi
  have hm := qcqsOrdinaryRestrictionModels l E s i
  rw [heq] at hm
  obtain ⟨hlim, hcol, hcoeff, τ, χ, haug, hfst, hsnd⟩ := hm
  let := hlim
  let := hcol
  have hgood := ordinaryPull_good l E r
  obtain ⟨α, hα⟩ := ordinaryCompletionComparison_exists l E r χ hgood
  have hu := ordinaryCompletionComparison_unit l E r τ χ haug hfst hsnd hgood α hα
  refine ⟨hlim, hcol, hcoeff, ordinaryCoefficientMap_projection l E r,
    ⟨τ, χ, hgood, α, haug, hfst, hsnd, hα, hu⟩, ?_⟩
  intro H hc
  apply (canonicalCompletionUnitCriterion l E S _).mp
  have := (canonicalCompletionUnitCriterion l E T H).mpr hc
  rw [← hu]
  infer_instance

/-- The actual unit on a composite weakly etale/immersion restriction is invertible
exactly when the pulled original unit is invertible.
Source: Bhatt--Scholze Lemma 6.5.8; Stacks 0941
(blueprint: lem-fix-qcqs-completion-unit-restriction).
Proof: use the normalized models for the composite, and the proved unit equation.
Postcomposition with the component of the completion comparison, which is an
isomorphism, preserves and reflects invertibility. -/
theorem ordinaryCompositeCompletionUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace T] [QuasiSeparatedSpace T]
    (s : S ⟶ V) (i : V ⟶ T) [WeaklyEtale s] [IsImmersion i]
    (H : D l E T none) :
    IsIso ((ordinaryDerivedPull l E (s ≫ i)).map
        ((completionUnit l E T none).app H)) ↔
      IsIso ((completionUnit l E S none).app
        ((ordinaryDerivedPull l E (s ≫ i)).obj H)) := by
  obtain ⟨hlim, hcol, _, τ, χ, haug, hfst, hsnd⟩ :=
    qcqsOrdinaryRestrictionModels l E s i
  let := hlim
  let := hcol
  have hgood := ordinaryPull_good l E (s ≫ i)
  obtain ⟨α, hα⟩ := ordinaryCompletionComparison_exists l E (s ≫ i) χ hgood
  have hu := ordinaryCompletionComparison_unit l E (s ≫ i) τ χ haug hfst hsnd
    hgood α hα H
  have hh := isIso_comp_right_iff
    ((ordinaryDerivedPull l E (s ≫ i)).map ((completionUnit l E T none).app H))
    (α.hom.app H)
  rw [hu] at hh
  exact hh.symm

end WeilConjectures.IntegralOnSlice
