/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import WeilConjectures.TraceFormula.Supporting.AmbientQuotientScalarModelExistence
import WeilConjectures.TraceFormula.Supporting.TransportedReductionPullbackNormalized
import all WeilConjectures.TraceFormula.Supporting.TransportedReductionScalarNormalized
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization

/-! # Ambient normalized primitive comparison data

Source: Stacks 099N(2),(5), 06YY, 0941; the quotient-diagram construction in
blueprint trace transport (blueprint: lem-trf-ambient-comparison-system-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem ambientRoos (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X) :
    Nonempty (IntegralComparisonRoosModel l E X) := by
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E X S
  exact ⟨roosModel l E X S M D⟩

private theorem ambientPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X) :
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) := by
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E Y SY
  obtain ⟨θ, hθ⟩ := ordinaryQuotientPullbackTowerComparison l E f M
  let A := (integralOperationsGoodComplex l E Y).ι
  let R := M.quotient l E Y
  let F := integralComparisonSequencePullback l E f
  let U := coefficientSequenceRestriction l E X
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let L := coefficientSequenceLimit l E X
  let V := integralComparisonDerivedSequencePullback l E f ⋙ L
  let η : DerivedCategory.Q ⋙ V ≅ T ⋙ H :=
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors L ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l E X) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) ρX.comparison)
  let d : integralOperationsGoodLocalization l E Y ⋙ SY.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      haveI := D.reduction_isIso P.obj P.property.1 P.property.2
      exact asIso (D.reductionComparison.app P.obj)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  let δ : integralOperationsGoodLocalization l E Y ⋙ (SY.reduction ⋙ V) ≅
      integralOperationsPullbackOnGood l E f :=
    Functor.isoWhiskerRight d V ≪≫ Functor.isoWhiskerLeft (A ⋙ R) η ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  have descended := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
  have huniq := descended.choose_spec.choose_spec.1
  obtain ⟨r, hr, _⟩ := huniq (SY.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) r ≪≫ δ =
    integralDerivedPullbackComparison l E f at hr
  refine ⟨⟨r, ?_⟩⟩
  intro P C e κ _hp hc
  obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l E Y SY M D P.obj C e κ hc
  let q := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨q, hθ P.obj C a κ hκ, ?_⟩
  have he := congrArg (fun z ↦ z.hom.app P) hr
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (V.map (D.reductionComparison.app P.obj) ≫ η.hom.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj)) =
    (integralDerivedPullbackComparison l E f).hom.app P at he
  have hn := η.hom.naturality a.hom
  change V.map (DerivedCategory.Q.map a.hom) ≫ η.hom.app C =
    η.hom.app (R.obj P.obj) ≫ H.map (T.map a.hom) at hn
  have hη : (L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
      L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E X ρX _).hom) =
      V.map e.hom ≫ η.hom.app C := by
    rfl
  have hq : T.map a.hom ≫ q.hom = θ.hom.app P.obj := by
    dsimp only [q]
    change T.map a.hom ≫ (T.map a.inv ≫ θ.hom.app P.obj) = _
    rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
  have hcancel : H.map (T.map a.hom) ≫ H.map q.hom = H.map (θ.hom.app P.obj) := by
    rw [← H.map_comp, hq]
  have hcomp : V.map e.hom ≫ η.hom.app C ≫ H.map q.hom =
      V.map (D.reductionComparison.app P.obj) ≫ η.hom.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj) := by
    rw [← ha, V.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (V.map (DerivedCategory.Q.map a.hom)), hn]
    simp only [Category.assoc]
    rw [hcancel]
  have hfirst :
      L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
          (integralComparisonRoosBridge l E X ρX _).hom ≫ H.map q.hom =
      V.map e.hom ≫ η.hom.app C ≫ H.map q.hom := by
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ H.map q.hom) hη
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
          (integralComparisonRoosBridge l E X ρX _).hom ≫ H.map q.hom) = _
  rw [hfirst, hcomp]
  exact he

variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

private theorem ambientScalarNormalized
    {Y : Scheme.{u}}
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    ∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K)) := by
  classical
  obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
    (Scheme.ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y)
    (coefficientSequenceCommRingTransition l E Y)
  let A : CoefficientExtensionSystems l E L ι Y :=
    D.coefficientExtension (integralCoefficientCommRingSheaf l L Y)
      (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)
  have hφ : SemilinearSections.systemMap.{u + 1, u, max u (u + 1)}
      (Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y) (coefficientSequenceCommRingTransition l E Y)
      (integralCoefficientCommRingSheaf l L Y) (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y) =
        integralComparisonSequenceScalarMap l E L ι Y := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (SemilinearSections.systemMap_existsUnique.{u + 1, u, max u (u + 1)}
      (Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y) (coefficientSequenceCommRingTransition l E Y)
      (integralCoefficientCommRingSheaf l L Y) (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)).exists.choose_spec
        U.unop.1 (Opposite.op U.unop.2)
  let a : A.scalar.T ≅ integralComparisonDerivedSequenceScalar l E L ι Y :=
    scalarModelIso hφ A.scalar.model (integralComparisonSequenceScalarModel l E L ι Y)
  obtain ⟨association⟩ := coefficientExtensionFiniteAssociation_exists l E L ι Y A
  obtain ⟨_, _, _, _, _, hn⟩ := coefficientExtensionStrictRepresentative_exists
    l E L ι Y A SY association.association association.association_section
  intro K
  exact coefficientSequenceNormalized_of_iso l L Y (a.app (SY.reduction.obj K))
    (hn K)

private theorem ambientComplete (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : sfIntegralConstructibleCategory l E X) :
    IsIso (S.adjunction.unit.app K.obj) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  apply (purNormalizedReconstructionOfScheme l E X S).2 K.obj
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K.obj).mp K.property.1⟩

/-- Primitive normalized realization data exist on every scheme, with effectivity
on the constructible domain recorded by the comparison interface.
Source: Stacks 099N(2),(5), 06YY and 0941; blueprint common-stage transport,
construction of the strict quotient models
(blueprint: lem-trf-ambient-comparison-system-existence).

Proof: for each coefficient field and scheme take the whole-system derived reduction
adjunction with its quotient evaluation comparisons. The right-derived restriction
and limit construction supplies its natural Roos comparison, normalized on every
K-injective tower by the ordinary cone. On a flat-term K-flat representative, whole
system pullback of its reduction is the diagram of the pulled-back finite quotient
complexes. Its Roos realization is the defining completed pullback. Derived change
of rings similarly identifies scalar change of reduction with the diagram of the
scalar quotient tensors; the balanced association multiplies the two coefficient
factors and retains all quotient transitions. These constructions are available
without inverting ell on the base scheme: they concern module sheaves and the
actual quotient coefficient maps. Descent along K-flat resolutions gives the two
normalized primitive models on the ambient categories. For a constructible complete
input, normalized reconstruction makes the actual unit invertible. Its counit on
the scalarized reduction is invertible by the same normalized quotient tensor
calculation. With ell invertible on both schemes, the pullback calculation and
constructibility preservation give invertibility of its pullback counit as well.
Choose these constructions simultaneously over all the field and scheme parameters.
This proves existence of the primitive data only; no mixed, scalar-unit, scalar-tower
or geometric coherence equation is asserted here. -/
theorem ambientComparisonSystem_exists (l : ℕ) [Fact l.Prime] :
    Nonempty (IntegralComparisonSystem.{u} l) := by
  classical
  let S := fun (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (X : Scheme.{u}) ↦
    (coefficientDerivedSystemEvaluationCalculus l F X).choose
  let R := fun (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (X : Scheme.{u}) ↦
    (ambientRoos l F X (S F X)).some
  let P := fun (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] {X Y : Scheme.{u}} (f : X ⟶ Y) ↦
    (ambientPullback l F f (S F Y) (R F X)).some
  let C : ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F], IntegralComparisonCoefficientData l F :=
    fun F _ _ _ ↦ {
      system := S F
      roos := R F
      pullback := P F
      effective := by
        intro X Y _ _ f K
        have hn : IsNormalizedCoefficientSequence l F X
            ((integralComparisonDerivedSequencePullback l F f).obj
              ((S F Y).reduction.obj K.obj)) :=
          transportedReductionSystems_pullback_normalized l F f
          (fun x ↦ isUnit_of_invertible (l : X.residueField x))
          (fun y ↦ isUnit_of_invertible (l : Y.residueField y)) (S F Y) K.obj
        have := ((purNormalizedReconstructionOfScheme l F X (S F X)).1 _ hn).2
        change IsIso ((S F X).reduction.map ((P F f).realization.hom.app K.obj) ≫
          (S F X).adjunction.counit.app
            ((integralComparisonDerivedSequencePullback l F f).obj
              ((S F Y).reduction.obj K.obj)))
        infer_instance
      complete := fun X K ↦ ambientComplete l F X (S F X) K }
  refine ⟨{ coefficient := C, scalar := ?_ }⟩
  intro F _ _ _ G _ _ _ i
  let M := fun X : Scheme.{u} ↦
    (ambientQuotientScalarModel_exists l F G i X (S F X) (R G X)).some
  refine { model := M, effective := ?_ }
  intro X K
  have hn : IsNormalizedCoefficientSequence l G X
      ((integralComparisonDerivedSequenceScalar l F G i X).obj
        ((S F X).reduction.obj K.obj)) :=
    ambientScalarNormalized l F G i (S F X) K.obj
  have := ((purNormalizedReconstructionOfScheme l G X (S G X)).1 _ hn).2
  change IsIso ((S G X).reduction.map ((M X).realization.hom.app K.obj) ≫
    (S G X).adjunction.counit.app
      ((integralComparisonDerivedSequenceScalar l F G i X).obj
        ((S F X).reduction.obj K.obj)))
  infer_instance

end WeilConjectures
