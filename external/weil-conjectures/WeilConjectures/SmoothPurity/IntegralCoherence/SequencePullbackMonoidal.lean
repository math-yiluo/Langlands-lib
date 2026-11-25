/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
public import WeilConjectures.SmoothPurity.IntegralCoherence.SitePullbackMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapCochainComplexCoherence

/-! # Monoidal strict comparisons for the sequence-site pullback

Source: Stacks 07A4 and 0D6D; integral coherence, strict-model step.

The sequence-site pullback is the left adjoint of the actual sectionwise direct image.
Its pure-tensor normalized ordinary comparison makes it monoidal; the termwise functor
on unbounded cochain complexes inherits the comparison, its Koszul symmetry and the
compatibility with the adjunction-normalized compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
open CategoryTheory.CochainPullback (moduleTmul)

namespace WeilConjectures.IntegralCoherence

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance] sequenceMonoidal sequencePreadditive sequenceColimits
  sequenceLeftColim sequenceRightColim sequenceTensor sequenceFour sequenceLeft sequenceRight
  complexMonoidal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Base change on the sequence site is representably flat. -/
theorem sequenceBaseChange_representablyFlat {X Y : Scheme.{t}} (f : X ⟶ Y) :
    RepresentablyFlat (integralComparisonSequenceBaseChange f) := by
  have : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  constructor
  intro U
  exact IsCofiltered.of_equivalence
    (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (Scheme.proEtaleBaseChange f)).symm

attribute [local instance] sequenceBaseChange_representablyFlat

/-- The sequence-site pullback adjunction, with the direct image written as a pushforward
along the coefficient map. -/
def sequenceAdjunction {X Y : Scheme.{t}} (f : X ⟶ Y) :
    integralComparisonSequencePullback l E f ⊣ SheafOfModules.pushforward.{max u (t + 1)}
      (SitePullbackMonoidal.ringMap (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (integralComparisonSequenceBaseChange f)
        (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
        (integralComparisonSequenceRingMap l E f)) :=
  Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)

/-- The monoidal structure of the sequence-site module pullback. -/
@[instance_reducible]
def sequencePullbackMonoidal {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Monoidal :=
  SitePullbackMonoidal.monoidal (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (integralComparisonSequenceBaseChange f)
    (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
    (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
    (sequenceAdjunction l E f)

/-- The sequence-site pullback preserves the coproducts of total tensor products. -/
instance sequencePullback_preservesCoproducts {X Y : Scheme.{t}} (f : X ⟶ Y) (j : ℤ) :
    PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j}))
      (integralComparisonSequencePullback l E f) := by
  have : PreservesColimitsOfSize.{0, 0} (integralComparisonSequencePullback l E f) :=
    (Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E f)).leftAdjoint_preservesColimits
  infer_instance


/-- The compositor sends unit images to restricted iterated unit images. -/
theorem sequenceComposition_unit {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (V : ℕ × Y.ProEt) (x : M.val.obj (op V)) :
    ((integralComparisonSequenceComposition l E h f).hom.app M).val.app
        (op ((integralComparisonSequenceBaseChange (h ≫ f)).obj V))
        (((Adjunction.ofIsRightAdjoint
          (integralComparisonSequenceDirectImage l E (h ≫ f))).unit.app M).val.app (op V) x) =
      ((integralComparisonSequencePullback l E h).obj
          ((integralComparisonSequencePullback l E f).obj M)).val.map
        (CategoryTheory.Prod.mkHom (𝟙 V.1)
          ((MorphismProperty.Over.pullbackComp h f).hom.app V.2)).op
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)).unit.app
            ((integralComparisonSequencePullback l E f).obj M)).val.app
          (op ((integralComparisonSequenceBaseChange f).obj V))
          (((Adjunction.ofIsRightAdjoint
            (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app (op V) x)) := by
  obtain ⟨d, hd, hsec⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h f).exists.choose_spec
  have hu := unit_conjugateEquiv
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).comp
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f)))
    (integralComparisonSequenceComposition l E h f).hom M
  have hd' : conjugateEquiv
      ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).comp
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f)))
      (integralComparisonSequenceComposition l E h f).hom = d.hom :=
    congrArg Iso.hom hd
  rw [hd', Adjunction.comp_unit_app] at hu
  have hx := congrArg (fun g ↦ g.val.app (op V) x) hu
  have hs := hsec ((integralComparisonSequencePullback l E h).obj
    ((integralComparisonSequencePullback l E f).obj M)) V.1 V.2
    ((((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)).unit.app
            ((integralComparisonSequencePullback l E f).obj M)).val.app
          (op ((integralComparisonSequenceBaseChange f).obj V))
          (((Adjunction.ofIsRightAdjoint
            (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app (op V) x)))
  exact hx.symm.trans hs

/-- The ordinary comparisons are compatible with the sequence-site compositor. -/
theorem sequenceOrdinary_composition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (M N : coefficientSequenceModules l E Y) :
    letI := sequencePullbackMonoidal l E f
    letI := sequencePullbackMonoidal l E h
    letI := sequencePullbackMonoidal l E (h ≫ f)
    OplaxMonoidal.δ (integralComparisonSequencePullback l E (h ≫ f)) M N ≫
        ((integralComparisonSequenceComposition l E h f).hom.app M ⊗ₘ
          (integralComparisonSequenceComposition l E h f).hom.app N) =
      (integralComparisonSequenceComposition l E h f).hom.app (M ⊗ N) ≫
        (integralComparisonSequencePullback l E h).map
          (OplaxMonoidal.δ (integralComparisonSequencePullback l E f) M N) ≫
        OplaxMonoidal.δ (integralComparisonSequencePullback l E h)
          ((integralComparisonSequencePullback l E f).obj M)
          ((integralComparisonSequencePullback l E f).obj N) :=
  SitePullbackMonoidal.ordinary_composition
    (sequenceAdjunction l E f) (sequenceAdjunction l E h) (sequenceAdjunction l E (h ≫ f))
    (integralComparisonSequenceComposition l E h f)
    (fun V ↦ CategoryTheory.Prod.mkHom (𝟙 V.1)
      ((MorphismProperty.Over.pullbackComp h f).hom.app V.2))
    (fun M V x ↦ sequenceComposition_unit l E h f M V x) M N

/-- The strict comparison of the sequence-site pullback on unbounded complexes. -/
def sequenceComparison {X Y : Scheme.{t}} (f : X ⟶ Y) : PullbackComparison l E f :=
  letI := sequencePullbackMonoidal l E f
  { toCoreMonoidal := (integralComparisonSequencePullback l E f).mapCochainComplexCoreMonoidal
    generators := by
      intro P Q p q k hpq n U x y
      have h₁ := SitePullbackMonoidal.unit_naturality_apply
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (integralComparisonSequenceBaseChange f)
        (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
        (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
        (sequenceAdjunction l E f)
        (HomologicalComplex.ιTensorObj P Q p q k hpq) (n, U)
        (moduleTmul (P.X p) (Q.X q) (op (n, U)) x y)
      have h₂ := congrArg (fun g ↦ g.val.app
          (op ((integralComparisonSequenceBaseChange f).obj (n, U)))
          (((sequenceAdjunction l E f).unit.app (P.X p ⊗ Q.X q)).val.app
              (op (n, U)) (moduleTmul (P.X p) (Q.X q) (op (n, U)) x y)))
        ((integralComparisonSequencePullback l E f).map_ιTensorObj_mapCochainComplexμIso_inv_f
          P Q p q k hpq)
      have h₃ := SitePullbackMonoidal.ordinary_pure
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (integralComparisonSequenceBaseChange f)
        (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
        (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
        (sequenceAdjunction l E f)
        (P.X p) (Q.X q) (n, U) x y
      exact (congrArg (fun z ↦ (((integralComparisonSequencePullback l E f).mapCochainComplexμIso
        P Q).inv.f k).val.app _ z) h₁.symm).trans (h₂.trans (congrArg (fun z ↦
          (HomologicalComplex.ιTensorObj ((pull l E f).obj P) ((pull l E f).obj Q)
            p q k hpq).val.app _ z) h₃)) }

/-- The strict comparisons satisfy the signed symmetry identity. -/
theorem sequenceComparison_coherent {X Y : Scheme.{t}} (f : X ⟶ Y) :
    Coherent l E f (sequenceComparison l E f) := by
  let := sequencePullbackMonoidal l E f
  intro P Q
  exact (integralComparisonSequencePullback l E f).mapCochainComplex_braiding
    (fun M N ↦ SitePullbackMonoidal.ordinary_braiding
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (integralComparisonSequenceBaseChange f)
      (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
      (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
      (sequenceAdjunction l E f) M N) P Q

/-- The strict comparisons satisfy the composition law with the prescribed compositor. -/
theorem sequenceComparison_compositionLaw {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) :
    CompositionLaw l E h f (sequenceComparison l E f) (sequenceComparison l E h)
      (sequenceComparison l E (h ≫ f)) := by
  let := sequencePullbackMonoidal l E f
  let := sequencePullbackMonoidal l E h
  let := sequencePullbackMonoidal l E (h ≫ f)
  intro P Q
  exact Functor.mapCochainComplex_composition (integralComparisonSequencePullback l E f)
    (integralComparisonSequencePullback l E h) (integralComparisonSequencePullback l E (h ≫ f))
    (integralComparisonSequenceComposition l E h f)
    (fun M N ↦ sequenceOrdinary_composition l E h f M N) P Q

end WeilConjectures.IntegralCoherence
