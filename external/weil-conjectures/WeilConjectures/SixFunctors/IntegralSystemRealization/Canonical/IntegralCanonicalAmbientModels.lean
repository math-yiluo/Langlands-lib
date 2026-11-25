/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralCanonicalSystemCoherence
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullbackModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenReductionNormalizedLimit
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedModelExistence
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import all WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence

/-! # Intermediate assembly data for integral realization
Source: blueprint fix-prop-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CategoricalAssembly
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

private theorem openReconstruction
    {R : C ⥤ A} {L : A ⥤ C} (adj : R ⊣ L)
    {R' : D ⥤ B} {L' : B ⥤ D} (adj' : R' ⊣ L')
    (J : A ⥤ B) (j : C ⥤ D) (δ : R ⋙ J ⟶ j ⋙ R') (M : A)
    [IsIso (adj.counit.app M)] [IsIso (δ.app (L.obj M))]
    [IsIso (adj'.unit.app (j.obj (L.obj M)))] :
    ∃ e : L'.obj (J.obj M) ≅ j.obj (L.obj M),
      L'.map (J.map (adj.counit.app M)) ≫ e.hom ≫
        adj'.unit.app (j.obj (L.obj M)) = L'.map (δ.app (L.obj M)) := by
  let e := (L'.mapIso (J.mapIso (asIso (adj.counit.app M)))).symm ≪≫
    L'.mapIso (asIso (δ.app (L.obj M))) ≪≫
    (asIso (adj'.unit.app (j.obj (L.obj M)))).symm
  refine ⟨e, ?_⟩
  dsimp only [e]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    asIso_hom, asIso_inv, Functor.map_inv, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, IsIso.hom_inv_id_assoc]

private def inverseAdjunct {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {H : A ⥤ C} {K : A ⥤ D} (t : H ⟶ K ⋙ G) : H ⋙ F ⟶ K where
  app M := (adj.homEquiv _ _).symm (t.app M)
  naturality M N f := by
    dsimp only [Functor.comp_map]
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact t.naturality f

private theorem inverseAdjunct_app {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {H : A ⥤ C} {K : A ⥤ D} (t : H ⟶ K ⋙ G) (M : A) :
    (adj.homEquiv _ _) ((inverseAdjunct adj t).app M) = t.app M :=
  (adj.homEquiv _ _).apply_symm_apply _

end CategoricalAssembly

private theorem properProjection_app (o : Operations l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : System l E X) (N : System l E Y) :
    ((properProjection l E o f).app M).app N =
      (o.direct f).adj.homEquiv _ _
        ((pullbackTensorSystemComparison l E f).hom.app
            ((Operations.push l E o f).obj M, N) ≫
          (calculus l E X).systemClosed.tensor.map
            (Prod.mkHom ((o.direct f).adj.counit.app M) (𝟙 ((pull l E f).obj N)))) := by
  unfold properProjection
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  apply congrArg ((o.direct f).adj.homEquiv _ _)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.curry_map_app_app, Functor.curryObjProdComp_hom_app_app]
  dsimp only [Functor.curryObj, Functor.id_obj]
  erw [Category.comp_id]

/-- Simultaneous canonical operations, mate-pasting models and open reconstruction.
This assertion contains no comparison of an arbitrary finite expression.
Source: Stacks 0941, 03DI, 07A7 and 0F7B--0F7F; blueprint fix-prop-coherence,
strict-system realization steps 1--2
(blueprint: lem-sf-integral-canonical-ambient-models).

Proof: construct total right-derived system image from its ordinary adjunction,
using K-injective resolutions on the ringed sequence site. Descend exact system
inverse image and open extension by zero. Evaluation of the inverse image is the
specified quotient-tensor map; transposing it gives direct-image evaluation and
its unit, counit and quotient-transition equations. Ordinary direct image on
sections gives its compositor and the bridge to intrinsic semilinear systems.
Transpose to obtain the pull and derived direct compositors. Transport the intrinsic
proper/open lambda and its open adjunct along the bridge; uniqueness of adjuncts
and semilinear mate pasting give all three recorded pasting equations. Apply the
ringed exchange/tensor coherence theorem to the same tensor pullback square.
The ordinary sectionwise limit/push comparison gives the realization model by
adjunction conjugation and K-flat localization. For an arbitrary good M, invert
the normalized reconstruction counit and use the open reduction mate followed
by the inverse reconstruction unit at J(L M). Its normalization follows from
unit naturality and the triangle identity. Finally use the ordinary completed
ringed-site tensor and pullback models, and their exact open mates, for the
ringed models and proper/open adjunct. All choices are fixed by their displayed
section, localization and adjunction normalizations, including the empty open. -/
theorem integralCanonicalAmbientModels :
    ∃ o : Operations l E, Nonempty (AmbientModels l E o) := by
  classical
  obtain ⟨o, c, a, b, ⟨pasting⟩, tensorSquare⟩ := integralCanonicalSystemCoherence l E
  obtain ⟨model⟩ := integralReductionPullbackModel l E o
  obtain ⟨d, ⟨da⟩⟩ := integralRingedModelExistence l E
  let openResult {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
      (M : System l E U) (hM : Good l E U M)
      (hJ : Good l E V ((Operations.shriek l E o j).obj M)) :
      ∃ e : (coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M) ≅
          (ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj M),
        (coefficientSequenceLimit l E V).map
            ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app M)) ≫
          e.hom ≫ (calculus l E V).adjunction.unit.app
            ((ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj M)) =
          (coefficientSequenceLimit l E V).map
            ((model.openReduction l E j).app ((coefficientSequenceLimit l E U).obj M)) := by
    have := (purNormalizedReconstructionOfScheme l E U (calculus l E U)).1 M hM.1 |>.2
    obtain ⟨hu, hr⟩ := integralOpenReductionNormalizedLimit l E o model j M hM hJ
    have := hu
    have := hr
    exact openReconstruction (calculus l E U).adjunction (calculus l E V).adjunction
      (Operations.shriek l E o j) (ringedOpen l E j) (model.openReduction l E j) M
  let ringedGamma {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) :
      ringedPush l E r ⋙ ringedOpen l E i ⟶ ringedOpen l E k ⋙ ringedPush l E p :=
    inverseAdjunct (ringedOpenAdj l E i) (ringedProperOpenLambda l E d da k r p i h).inv
  refine ⟨o, ⟨{
    compositors := c
    openComparisons := a
    canonicalBridge := b
    properOpen := pasting
    ringedTensorCoherence := ?_
    realizationModel := model
    openRealization := fun {U V} j [hj : IsOpenImmersion j] hq M hM hJ ↦
      (@openResult U V j hj hq M hM hJ).choose
    openNormalization := fun {U V} j [hj : IsOpenImmersion j] [hq : QuasiCompact j] M hM hJ ↦
      (@openResult U V j hj hq M hM hJ).choose_spec
    ringedModels := d
    ringedOpenComparisons := da
    ringedProperOpen := {
      gamma := ringedGamma
      adjunct := fun {_ _ _ _} k r p i [IsOpenImmersion k] [IsOpenImmersion i]
          [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p] h M ↦
        inverseAdjunct_app (ringedOpenAdj l E i)
          (ringedProperOpenLambda l E d da k r p i h).inv M }
  }⟩⟩
  · intro U V W Z k r p i h M N
    simp only [properProjection_app, properExchange]
    exact tensor_mate_coherence (o.direct p).adj (o.direct r).adj
      (calculus l E Z).systemClosed.tensor (calculus l E V).systemClosed.tensor
      (calculus l E W).systemClosed.tensor (calculus l E U).systemClosed.tensor
      (pullbackTensorSystemComparison l E p).hom
      (pullbackTensorSystemComparison l E i).hom
      (pullbackTensorSystemComparison l E k).hom
      (pullbackTensorSystemComparison l E r).hom
      (c.square l E k r p i h) (tensorSquare k r p i h) M N

end WeilConjectures.IntegralSystemRealization
