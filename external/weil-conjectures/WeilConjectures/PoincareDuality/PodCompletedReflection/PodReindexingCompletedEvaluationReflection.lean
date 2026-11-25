/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCompletionUnitTensor
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorAugmentationSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingOrdinaryCurrying
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.PoincareDuality.Pod.PodNormalizedTensorSignedShifts
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedIdentityNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCompositionNormalization

/-! # Completed evaluation by reflection and its normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, proof Steps 2 and 4;
Stacks Tags 099B, 0A0E and 099M
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodCompletedReflection

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded ambient completed-ring category, without a constructibility restriction.
Source: Stacks 08J7
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev D (W : Scheme.{u}) := podReindexingDerived l E W none

/-- The existing ordinary closed calculus, with the K-injective internal Hom.
Source: Stacks 08J9
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev closed (W : Scheme.{u}) := (podReindexCalculus l E W).integralClosed

/-- Its existing K-flat total-tensor normalization.
Source: Stacks 07A4
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev models (W : Scheme.{u}) := (podReindexCalculus l E W).integralTensorModel

/-- The recorded ambient internal Hom, at the completed coefficient stage.
Source: Stacks 08J7
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev hom (W : Scheme.{u}) (M N : D l E W) :=
  (podReindexingDerivedHom l E W none).obj (op M, N)

/-- The actual ordinary-to-quotient-tower tensor unit, written using the published
reduction adjunction, its tensor comparison and its normalized Roos realization.
Source: Stacks 099M; blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev unit (W : Scheme.{u}) (M L : D l E W) :
    (closed l E W).tensor.obj (M, L) ⟶ (integralCompletedTensor l E W).obj (M, L) :=
  (podReindexCalculus l E W).adjunction.unit.app _ ≫
    (coefficientSequenceLimit l E W).map
      ((podReindexCalculus l E W).reductionTensor.hom.app (M, L)) ≫
    (pullbackTensorIntegralTensorModel l E W).inv.app (M, L)

/-- Ordinary M-first currying uses the recorded signed braiding, followed by the
ordinary Hom-first adjunction. Thus the Koszul symmetry is fixed, rather than chosen.
Source: Stacks 08J9; blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def ordinaryTranspose (W : Scheme.{u}) (M L N : D l E W) :
    ((closed l E W).tensor.obj (M, L) ⟶ N) ≃ (L ⟶ hom l E W M N) :=
  ((pullbackTensorBraiding (ProEt.topology W)
    (podReindexingRing l E W none) (closed l E W) (models l E W)).app (M, L)).homFromEquiv.trans
    ((closed l E W).transpose L M N)

/-- The two projection-normalized inverse-image presentations agree as functors.
Source: blueprint dual-Tate compatibility, Steps 1--2; Stacks 03CO
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof: the finite coefficient maps in the Hom resolution model are the constant
maps. Every completed projection therefore agrees with isoReductionCompletedMap.
Uniqueness of the inverse-limit map identifies the ring maps. Substitution in
isoSectionwiseModuleInverseImage identifies the exact module functors, and their
identical termwise localizations give the displayed equality. -/
theorem reindex_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g := by
  have hπ (W : Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n) =
          limit.π (integralCoefficientSheafSystem l E W) (op n) := by rfl
  have hc := (podReindexingCoefficient_existsUnique l E g).exists.choose_spec
  have he : (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g none) = isoReductionCompletedMap l E g := by
    apply (isoReductionCompletedMap_existsUnique l E g).unique
    · intro n
      have hn := congrArg
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (hc.2 n)
      change _ ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) = _
      have hm : (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((isoSectionwiseInverseImage g CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n)) =
          (isoSectionwiseInverseImage g RingCat.{u + 1}).map
            ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (completedIntegralCommRingProjectionUnrestricted l E Y n)) := rfl
      simpa only [Functor.map_comp, hm, hπ, hc.1 n, podReindexingCoefficient,
        Functor.mapIso_hom] using hn
    · exact (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec
  exact congrArg (fun c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
        completedIntegralCoefficientSheafUnrestricted l E X ↦
      (isoSectionwiseModuleInverseImage g c.hom).mapDerivedCategory) he

private theorem adjunction_unit_bijective
    {C : Type v} [Category.{w} C] {B : Type*} [Category B]
    {F : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G)
    (hε : ∀ P : C, IsIso (adj.counit.app (F.obj P)))
    (P N : C) [IsIso (adj.unit.app N)] :
    Function.Bijective (fun f : (F ⋙ G).obj P ⟶ N ↦ adj.unit.app P ≫ f) := by
  have : IsIso (adj.counit.app (F.obj P)) := hε P
  have : IsIso (F.map (adj.unit.app P)) := by
    have ht := adj.left_triangle_components P
    have : IsIso (F.map (adj.unit.app P) ≫ adj.counit.app (F.obj P)) := by
      rw [ht]
      exact CategoryTheory.IsIso.id _
    exact IsIso.of_isIso_comp_right (F.map (adj.unit.app P))
      (adj.counit.app (F.obj P))
  constructor
  · intro f g h
    have hh := congrArg (F ⋙ G).map h
    simp only [Functor.map_comp] at hh
    have : IsIso ((F ⋙ G).map (adj.unit.app P)) := G.map_isIso _
    have he := (cancel_epi ((F ⋙ G).map (adj.unit.app P))).mp hh
    apply (cancel_mono (adj.unit.app N)).mp
    have hf := adj.unit.naturality f
    have hg := adj.unit.naturality g
    dsimp only [Functor.id_map, Functor.id_obj] at hf hg
    exact hf.trans ((congrArg (fun k ↦ adj.unit.app ((F ⋙ G).obj P) ≫ k) he).trans hg.symm)
  · intro f
    refine ⟨(F ⋙ G).map f ≫ inv (adj.unit.app N), ?_⟩
    change adj.unit.app P ≫ (F ⋙ G).map f ≫ inv (adj.unit.app N) = f
    have hf := adj.unit.naturality f
    dsimp only [Functor.id_map, Functor.id_obj] at hf
    rw [← Category.assoc, ← hf]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The first bijection is precomposition with precisely the published tensor unit.
No assumption says the ordinary tensor is complete or M is perfect.
Source: Stacks 099B, 0A0E and 099M; blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof (node Step 1): the strict balanced comparison identifies the quotient tower of
ordinary tensor with the two-reduction tensor tower, including the augmentation.
The constant-completion equivalence identifies this unit with the Koszul unit.
Constructible N is locally derived complete by integralConstructible_locallyComplete.
The ambient completed tensor adjunction and the Koszul reflector then give precisely
this Hom bijection. Neither input needs a finite Tor bound. -/
theorem precompose_bijective (W : Scheme.{u})
    (M L N : sfIntegralConstructibleCategory l E W) :
    Function.Bijective (fun f : (integralCompletedTensor l E W).obj (M.obj, L.obj) ⟶ N.obj ↦
      unit l E W M.obj L.obj ≫ f) := by
  -- Use the actual reduction adjunction to identify the reflector map directly.
  obtain ⟨hc, hu⟩ := purNormalizedReconstructionOfScheme l E W (podReindexCalculus l E W)
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ D.p := by change l ≠ p; omega
  have hN : IntegralOnSlice.IsComplete l E W none N.obj :=
    ⟨D, hlp, (sfDerivedComplete_iff_legacy l E W D hlp N.obj).mp N.property.1⟩
  have : IsIso ((podReindexCalculus l E W).adjunction.unit.app N.obj) := hu N.obj hN
  let e : (integralCompletedTensor l E W).obj (M.obj, L.obj) ≅
      (coefficientSequenceLimit l E W).obj
        ((podReindexCalculus l E W).reduction.obj
          ((closed l E W).tensor.obj (M.obj, L.obj))) :=
    (pullbackTensorIntegralTensorModel l E W).app (M.obj, L.obj) ≪≫
      (coefficientSequenceLimit l E W).mapIso
        (((podReindexCalculus l E W).reductionTensor).app (M.obj, L.obj)).symm
  have hb := adjunction_unit_bijective (podReindexCalculus l E W).adjunction
    (fun P ↦ (hc _ ((podReindexCalculus l E W).reduction_normalized P)).2)
    ((closed l E W).tensor.obj (M.obj, L.obj)) N.obj
  have hh := hb.comp e.homFromEquiv.bijective
  convert hh using 1
  funext f
  simp only [Function.comp_def, Iso.homFromEquiv_apply, e, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc, unit]
  rfl

/-- The canonical first Hom equivalence; its inverse is the unique reflector extension.
Source: Stacks 099B (blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def reflectorEquiv (W : Scheme.{u}) (M L N : sfIntegralConstructibleCategory l E W) :
    ((integralCompletedTensor l E W).obj (M.obj, L.obj) ⟶ N.obj) ≃
      ((closed l E W).tensor.obj (M.obj, L.obj) ⟶ N.obj) :=
  Equiv.ofBijective _ (precompose_bijective l E W M L N)

/-- The composite of the two specified bijections, in the node's M-first order.
Source: Stacks 099B, 08J9
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def transpose (W : Scheme.{u}) (M L N : sfIntegralConstructibleCategory l E W) :
    ((integralCompletedTensor l E W).obj (M.obj, L.obj) ⟶ N.obj) ≃
      (L.obj ⟶ hom l E W M.obj N.obj) :=
  (reflectorEquiv l E W M L N).trans (ordinaryTranspose l E W M.obj L.obj N.obj)

/-- Completed evaluation is the unique completion-unit extension of ordinary evaluation.
The Hom-constructibility hypothesis is used only to form its constructible tensor input.
Source: blueprint dual-Tate compatibility, Step 2; Stacks 099B
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def evaluation (W : Scheme.{u}) (M N : sfIntegralConstructibleCategory l E W)
    (hH : sfIntegralConstructible l E W (hom l E W M.obj N.obj)) :
    (integralCompletedTensor l E W).obj (M.obj, hom l E W M.obj N.obj) ⟶ N.obj :=
  (transpose l E W M ⟨hom l E W M.obj N.obj, hH⟩ N).symm (𝟙 _)

/-- The projection-fixed identification of the two ordinary inverse-image interfaces.
Source: Stacks 03CO (blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def reindexIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingDerivedFunctor l E g none ≅ podOrdinaryReindex l E g :=
  eqToIso (reindex_eq l E g)

/-- The normalized ordinary comparison data of the recorded evaluation lemma.
Source: Stacks 0GMX (blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
abbrev Comparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  PodReindexingCoherence.Comparison l E g none
    (closed l E X) (closed l E Y) (models l E X) (models l E Y)

/-- The ambient c⁰, transported only through equality of the projection-fixed functors.
It has no constructibility hypothesis on its two unbounded inputs.
Source: blueprint dual-Tate compatibility, Steps 1 and 4
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def homComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (c : Comparison l E g) (M N : D l E Y) :
    (podOrdinaryReindex l E g).obj (hom l E Y M N) ≅
      hom l E X ((podOrdinaryReindex l E g).obj M) ((podOrdinaryReindex l E g).obj N) :=
  ((reindexIso l E g).app (hom l E Y M N)).symm ≪≫
    c.derived.app (op M, N) ≪≫
    (podReindexingDerivedHom l E X none).mapIso
      (((reindexIso l E g).app M).symm.op.prod ((reindexIso l E g).app N))

/-- The same projection-fixed transport of the ordinary tensor comparison μ⁰.
Source: Stacks 07A4 (blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def tensorComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (c : Comparison l E g) (M L : D l E Y) :
    (podOrdinaryReindex l E g).obj ((closed l E Y).tensor.obj (M, L)) ≅
      (closed l E X).tensor.obj
        ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj L) :=
  ((reindexIso l E g).app ((closed l E Y).tensor.obj (M, L))).symm ≪≫
    c.tensor.app (M, L) ≪≫
    (closed l E X).tensor.mapIso
      (((reindexIso l E g).app M).prod ((reindexIso l E g).app L))

private theorem ambientEvaluation_naturality
    {D : Type v} [Category.{w} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem ambientInverseTranspose_naturality
    {D : Type v} [Category.{w} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (L L' P Q P' Q' : D)
    (f : L' ⟶ L) (g : P' ⟶ P) (h : Q ⟶ Q') (phi : L ⟶ H.obj (op P, Q)) :
    (S.transpose L' P' Q').symm (f ≫ phi ≫ H.map (Prod.mkHom g.op h)) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose L P Q).symm phi ≫ h := by
  let := S.monoidal
  have he (T P Q : D) (psi : T ⟶ H.obj (op P, Q)) :
      (S.transpose T P Q).symm psi =
        S.tensor.map (Prod.mkHom psi (𝟙 P)) ≫ S.evaluation P Q :=
    by
      have ht : S.tensor.map (Prod.mkHom psi (𝟙 P)) =
          (@MonoidalCategory.tensorRight D _ S.monoidal P).map psi :=
        @MonoidalCategory.tensorHom_id D _ S.monoidal T _ psi P
      rw [ht]
      exact (S.adjunction P).homEquiv_counit (g := psi)
  rw [he, he, Category.assoc]
  have hn := S.tensor.map (Prod.mkHom (f ≫ phi) (𝟙 P')) ≫=
    ambientEvaluation_naturality S P Q P' Q' g h
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using hn

private def tensorUnitNat (W : Scheme.{u}) :
    (closed l E W).tensor ⟶ integralCompletedTensor l E W :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (podReindexCalculus l E W).adjunction.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (podReindexCalculus l E W).reductionTensor.hom
      (coefficientSequenceLimit l E W) ≫
    (pullbackTensorIntegralTensorModel l E W).inv

private theorem ordinaryInverse_naturality (W : Scheme.{u})
    (M M' L L' N N' : D l E W) (a : M' ⟶ M) (f : L' ⟶ L) (d : N ⟶ N')
    (phi : L ⟶ hom l E W M N) :
    (ordinaryTranspose l E W M' L' N').symm
        (f ≫ phi ≫ (podReindexingDerivedHom l E W none).map (Prod.mkHom a.op d)) =
      (closed l E W).tensor.map (Prod.mkHom a f) ≫
        (ordinaryTranspose l E W M L N).symm phi ≫ d := by
  let beta := pullbackTensorBraiding (ProEt.topology W)
    (podReindexingRing l E W none) (closed l E W) (models l E W)
  change (beta.app (M', L')).hom ≫ _ =
    (closed l E W).tensor.map (Prod.mkHom a f) ≫
      ((beta.app (M, L)).hom ≫ _) ≫ d
  erw [ambientInverseTranspose_naturality (closed l E W) L L' M N M' N' f a d phi]
  have hn := beta.hom.naturality (Prod.mkHom a f)
  dsimp only [Functor.comp_map, pullbackTensorSwap] at hn
  simp only [Category.assoc]
  have hh := congrArg
    (fun k ↦ k ≫ ((closed l E W).transpose L M N).symm phi ≫ d) hn.symm
  simp only [Category.assoc] at hh
  convert hh using 1 <;> rfl

private theorem ordinary_naturality (W : Scheme.{u})
    (M M' L L' N N' : D l E W) (a : M' ⟶ M) (f : L' ⟶ L) (d : N ⟶ N')
    (b : (closed l E W).tensor.obj (M, L) ⟶ N) :
    ordinaryTranspose l E W M' L' N'
        ((closed l E W).tensor.map (Prod.mkHom a f) ≫ b ≫ d) =
      f ≫ ordinaryTranspose l E W M L N b ≫
        (podReindexingDerivedHom l E W none).map (Prod.mkHom a.op d) := by
  apply (ordinaryTranspose l E W M' L' N').symm.injective
  rw [Equiv.symm_apply_apply, ordinaryInverse_naturality, Equiv.symm_apply_apply]

/-- Naturality of both bijections, in the parameter and both internal-Hom variables,
and unique extension of evaluation along the actual completion unit.
Source: Stacks 099B, 08J9; blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof (node Steps 1--2 and 6): naturality of the reduction unit and tensor comparison
makes precomposition natural. Compose with ordinary signed currying. Its naturality
in all variables gives the displayed transpose equation. The inverse image of the
identity under currying is ordinary M-first evaluation; reflector bijectivity gives
its unique extension, and equality with the explicitly defined completed evaluation.
This argument uses only completeness of the target and full-subcategory Hom sets. -/
theorem reflection_laws (W : Scheme.{u}) :
    (∀ (M L N : sfIntegralConstructibleCategory l E W)
      (b : (integralCompletedTensor l E W).obj (M.obj, L.obj) ⟶ N.obj),
      transpose l E W M L N b = ordinaryTranspose l E W M.obj L.obj N.obj
        (unit l E W M.obj L.obj ≫ b)) ∧
    (∀ (M M' L L' N N' : sfIntegralConstructibleCategory l E W)
      (a : M' ⟶ M) (f : L' ⟶ L) (d : N ⟶ N')
      (b : (integralCompletedTensor l E W).obj (M.obj, L.obj) ⟶ N.obj),
      transpose l E W M' L' N'
        ((integralCompletedTensor l E W).map (Prod.mkHom a.hom f.hom) ≫ b ≫ d.hom) =
      f.hom ≫ transpose l E W M L N b ≫
        (podReindexingDerivedHom l E W none).map (Prod.mkHom a.hom.op d.hom)) ∧
    (∀ (M N : sfIntegralConstructibleCategory l E W)
      (hH : sfIntegralConstructible l E W (hom l E W M.obj N.obj)),
      (unit l E W M.obj (hom l E W M.obj N.obj) ≫ evaluation l E W M N hH =
        (ordinaryTranspose l E W M.obj (hom l E W M.obj N.obj) N.obj).symm (𝟙 _)) ∧
      ∀ e : (integralCompletedTensor l E W).obj (M.obj, hom l E W M.obj N.obj) ⟶ N.obj,
        unit l E W M.obj (hom l E W M.obj N.obj) ≫ e =
          (ordinaryTranspose l E W M.obj (hom l E W M.obj N.obj) N.obj).symm (𝟙 _) ↔
        e = evaluation l E W M N hH) := by
  refine ⟨fun M L N b ↦ rfl, ?_, ?_⟩
  · intro M M' L L' N N' a f d b
    change ordinaryTranspose l E W M'.obj L'.obj N'.obj
      (unit l E W M'.obj L'.obj ≫ _) = _
    have hn : (closed l E W).tensor.map (Prod.mkHom a.hom f.hom) ≫
        unit l E W M.obj L.obj = unit l E W M'.obj L'.obj ≫
          (integralCompletedTensor l E W).map (Prod.mkHom a.hom f.hom) := by
      simpa [tensorUnitNat, unit, CoefficientClosedStructure.tensor, Category.assoc] using
        (tensorUnitNat l E W).naturality (Prod.mkHom a.hom f.hom)
    have ht := congrArg (fun k ↦ ordinaryTranspose l E W M'.obj L'.obj N'.obj
      (k ≫ b ≫ d.hom)) hn.symm
    calc
      _ = ordinaryTranspose l E W M'.obj L'.obj N'.obj
          ((closed l E W).tensor.map (Prod.mkHom a.hom f.hom) ≫
            (unit l E W M.obj L.obj ≫ b) ≫ d.hom) := by
        simpa only [Category.assoc] using ht
      _ = _ := ordinary_naturality l E W M.obj M'.obj L.obj L'.obj N.obj N'.obj
        a.hom f.hom d.hom (unit l E W M.obj L.obj ≫ b)
  · intro M N hH
    have he : unit l E W M.obj (hom l E W M.obj N.obj) ≫ evaluation l E W M N hH =
        (ordinaryTranspose l E W M.obj (hom l E W M.obj N.obj) N.obj).symm (𝟙 _) := by
      apply (ordinaryTranspose l E W M.obj (hom l E W M.obj N.obj) N.obj).injective
      rw [Equiv.apply_symm_apply]
      exact (transpose l E W M ⟨hom l E W M.obj N.obj, hH⟩ N).apply_symm_apply (𝟙 _)
    refine ⟨he, fun e ↦ ⟨fun h ↦ ?_, fun h ↦ h ▸ he⟩⟩
    exact (precompose_bijective l E W M ⟨hom l E W M.obj N.obj, hH⟩ N).injective
      (h.trans he.symm)

/-- The ambient isomorphism restricts to the actual constructible integral category.
Source: blueprint dual-Tate compatibility, Step 4
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof (node Step 3): T.constructible puts FM, FN and FHom(M,N) in the integral
subcategory with their complete uniform finite reductions. The ambient Hom
comparison is an isomorphism. Completeness, constructibility of every positive
reduction and its common cohomological interval are invariant under isomorphism.
Transport these properties through homComparison. Fullness restricts that same
isomorphism; it introduces no new internal-Hom map. -/
theorem constructible_hom {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (c : Comparison l E g) (M N : sfIntegralConstructibleCategory l E Y)
    (hH : sfIntegralConstructible l E Y (hom l E Y M.obj N.obj)) :
    sfIntegralConstructible l E X
      (hom l E X ((podOrdinaryReindex l E g).obj M.obj)
        ((podOrdinaryReindex l E g).obj N.obj)) := by
  exact (sfIntegralConstructible l E X).prop_of_iso
    (homComparison l E g c M.obj N.obj)
    (T.constructible ⟨hom l E Y M.obj N.obj, hH⟩)

/-- The restricted c⁰ has exactly the ambient isomorphism as its underlying arrow.
Source: blueprint dual-Tate compatibility, Step 4
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def restrictedComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (c : Comparison l E g) (M N : sfIntegralConstructibleCategory l E Y)
    (hH : sfIntegralConstructible l E Y (hom l E Y M.obj N.obj)) :
    (⟨(podOrdinaryReindex l E g).obj (hom l E Y M.obj N.obj),
      T.constructible ⟨hom l E Y M.obj N.obj, hH⟩⟩ : sfIntegralConstructibleCategory l E X) ≅
    ⟨hom l E X ((podOrdinaryReindex l E g).obj M.obj)
      ((podOrdinaryReindex l E g).obj N.obj), constructible_hom l E g A T c M N hH⟩ :=
  ObjectProperty.isoMk _ (homComparison l E g c M.obj N.obj)

/-- The completed evaluation and transpose equations for these very normalized maps.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 099B
(blueprint: lem-pod-reindexing-completed-evaluation-reflection). -/
def ReindexingLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (c : Comparison l E g) : Prop :=
    (∀ M L : sfIntegralConstructibleCategory l E Y,
      (podOrdinaryReindex l E g).map (unit l E Y M.obj L.obj) ≫ (T.tensor M L).hom =
        (tensorComparison l E g c M.obj L.obj).hom ≫
          unit l E X ((podOrdinaryReindex l E g).obj M.obj)
            ((podOrdinaryReindex l E g).obj L.obj)) ∧
    (∀ M L N : sfIntegralConstructibleCategory l E Y,
      Function.Bijective (fun f :
        (podOrdinaryReindex l E g).obj ((integralCompletedTensor l E Y).obj (M.obj, L.obj)) ⟶
          (podOrdinaryReindex l E g).obj N.obj ↦
        (podOrdinaryReindex l E g).map (unit l E Y M.obj L.obj) ≫ f)) ∧
    (∀ (M N : sfIntegralConstructibleCategory l E Y)
      (hH : sfIntegralConstructible l E Y (hom l E Y M.obj N.obj)),
      (T.tensor M ⟨hom l E Y M.obj N.obj, hH⟩).hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom (𝟙 _) (homComparison l E g c M.obj N.obj).hom) ≫
        evaluation l E X ⟨_, T.constructible M⟩ ⟨_, T.constructible N⟩
          (constructible_hom l E g A T c M N hH) =
      (podOrdinaryReindex l E g).map (evaluation l E Y M N hH)) ∧
    (∀ (M L N : sfIntegralConstructibleCategory l E Y)
      (b : (integralCompletedTensor l E Y).obj (M.obj, L.obj) ⟶ N.obj),
      transpose l E X ⟨_, T.constructible M⟩ ⟨_, T.constructible L⟩ ⟨_, T.constructible N⟩
          ((T.tensor M L).inv ≫ (podOrdinaryReindex l E g).map b) =
        (podOrdinaryReindex l E g).map (transpose l E Y M L N b) ≫
          (homComparison l E g c M.obj N.obj).hom) ∧
    (∀ (M M' N N' : D l E Y) (a : M' ⟶ M) (b : N ⟶ N'),
      (podOrdinaryReindex l E g).map
          ((podReindexingDerivedHom l E Y none).map (Prod.mkHom a.op b)) ≫
        (homComparison l E g c M' N').hom =
      (homComparison l E g c M N).hom ≫ (podReindexingDerivedHom l E X none).map
        (Prod.mkHom ((podOrdinaryReindex l E g).map a).op
          ((podOrdinaryReindex l E g).map b)))

private theorem transportedHom_naturality
    {C0 : Type v} [Category.{w} C0] {D0 : Type t} [Category.{u} D0]
    (HC : C0ᵒᵖ × C0 ⥤ C0) (HD : D0ᵒᵖ × D0 ⥤ D0)
    (F G : C0 ⥤ D0) (e : F ≅ G)
    (c : HC ⋙ F ≅ (F.op.prod F) ⋙ HD) :
    let k := fun M N ↦ ((e.app (HC.obj (op M, N))).symm ≪≫
      c.app (op M, N) ≪≫ HD.mapIso (((e.app M).symm.op).prod (e.app N))).hom
    ∀ (M M' N N' : C0) (a : M' ⟶ M) (b : N ⟶ N'),
      G.map (HC.map (Prod.mkHom a.op b)) ≫ k M' N' =
        k M N ≫ HD.map (Prod.mkHom (G.map a).op (G.map b)) := by
  intro k M M' N N' a b
  let d : HC ⋙ G ≅ (G.op.prod G) ⋙ HD :=
    Functor.isoWhiskerLeft HC e.symm ≪≫ c ≪≫
      Functor.isoWhiskerRight (NatIso.prod (NatIso.op e.symm) e) HD
  exact d.hom.naturality (Prod.mkHom a.op b)

private theorem transported_precompose_bijective
    {C0 : Type v} [Category.{w} C0] {A0 A1 B0 B1 N0 : C0}
    (e : A0 ≅ A1) (d : B0 ≅ B1) (u : A1 ⟶ B1) (v : A0 ⟶ B0)
    (h : u ≫ d.inv = e.inv ≫ v)
    (hb : Function.Bijective (fun f : B1 ⟶ N0 ↦ u ≫ f)) :
    Function.Bijective (fun f : B0 ⟶ N0 ↦ v ≫ f) := by
  have hh := e.symm.homFromEquiv.bijective.comp (hb.comp d.homFromEquiv.bijective)
  convert hh using 1
  funext f
  simp only [Function.comp_def, Iso.homFromEquiv_apply, Iso.symm_inv]
  rw [← Category.assoc u d.inv f, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

section
attribute [local irreducible] podReindexCalculus

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Completed evaluation, its tensor-Hom transpose, and the exact ordinary equation
obtained by precomposition with the normalized tensor unit.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 099B, 0A0E
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof (node Steps 4--5): the normalized tensor-augmentation square gives the first
law. Its inverse form identifies unit_X followed by the inverse completed tensor
comparison with the inverse ordinary comparison followed by F(unit_Y). Composing
the reflector bijection with the two tensor isomorphisms proves the second law.
For b, the same inverse unit square reduces completed currying to ambient ordinary
M-first currying, proving the transpose law. To prove evaluation compatibility,
precompose by the inverse tensor comparison and apply completed currying injectivity.
Naturality in its second input sends the Hom comparison followed by evaluation to
the Hom comparison itself, since evaluation transposes to the identity. The transpose
law gives the same answer for F(evaluation). The last law is naturality of the
ambient natural isomorphism obtained by whiskering the original c with reindexIso. -/
theorem reindexing_laws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T) (c : Comparison l E g) :
    ReindexingLaws l E g A T c := by
  have hu : ∀ M L : sfIntegralConstructibleCategory l E Y,
      (podOrdinaryReindex l E g).map (unit l E Y M.obj L.obj) ≫ (T.tensor M L).hom =
        (tensorComparison l E g c M.obj L.obj).hom ≫
          unit l E X ((podOrdinaryReindex l E g).obj M.obj)
            ((podOrdinaryReindex l E g).obj L.obj) := by
    as_aux_lemma =>
      exact podReindexing_tensor_augmentation_square l E g A T hA hT (unit l E) rfl c
        (reindex_eq l E g)
  have ho (M L N : D l E Y) (b : (closed l E Y).tensor.obj (M, L) ⟶ N) :
      ordinaryTranspose l E X ((podOrdinaryReindex l E g).obj M)
          ((podOrdinaryReindex l E g).obj L) ((podOrdinaryReindex l E g).obj N)
          ((tensorComparison l E g c M L).inv ≫ (podOrdinaryReindex l E g).map b) =
        (podOrdinaryReindex l E g).map (ordinaryTranspose l E Y M L N b) ≫
          (homComparison l E g c M N).hom := by
    as_aux_lemma =>
      have h := podReindexing_ordinary_currying l E g (closed l E X) (closed l E Y)
        (models l E X) (models l E Y) c (podOrdinaryReindex l E g)
        (reindex_eq l E g) M L N b
      dsimp only [ordinaryTranspose, tensorComparison, homComparison, reindexIso, hom] at h ⊢
      exact h
  have hu' (M L : sfIntegralConstructibleCategory l E Y) :
      unit l E X ((podOrdinaryReindex l E g).obj M.obj)
          ((podOrdinaryReindex l E g).obj L.obj) ≫ (T.tensor M L).inv =
        (tensorComparison l E g c M.obj L.obj).inv ≫
          (podOrdinaryReindex l E g).map (unit l E Y M.obj L.obj) := by
    as_aux_lemma =>
      apply (cancel_epi (tensorComparison l E g c M.obj L.obj).hom).mp
      have h := congrArg (· ≫ (T.tensor M L).inv) (hu M L).symm
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id] at h ⊢
      exact h
  have ht (M L N : sfIntegralConstructibleCategory l E Y)
      (b : (integralCompletedTensor l E Y).obj (M.obj, L.obj) ⟶ N.obj) :
      transpose l E X ⟨_, T.constructible M⟩ ⟨_, T.constructible L⟩ ⟨_, T.constructible N⟩
          ((T.tensor M L).inv ≫ (podOrdinaryReindex l E g).map b) =
        (podOrdinaryReindex l E g).map (transpose l E Y M L N b) ≫
          (homComparison l E g c M.obj N.obj).hom := by
    as_aux_lemma =>
      change ordinaryTranspose l E X _ _ _ (unit l E X _ _ ≫ _) = _
      rw [← Category.assoc, hu', Category.assoc, ← CategoryTheory.Functor.map_comp]
      exact ho M.obj L.obj N.obj (unit l E Y M.obj L.obj ≫ b)
  refine ⟨hu, ?_, ?_, ht, ?_⟩
  · as_aux_lemma =>
      intro M L N
      exact transported_precompose_bijective
        (tensorComparison l E g c M.obj L.obj) (T.tensor M L)
        (unit l E X _ _) ((podOrdinaryReindex l E g).map (unit l E Y M.obj L.obj))
        (hu' M L) (precompose_bijective l E X
          ⟨_, T.constructible M⟩ ⟨_, T.constructible L⟩ ⟨_, T.constructible N⟩)
  · intro M N hH
    let H : sfIntegralConstructibleCategory l E Y := ⟨hom l E Y M.obj N.obj, hH⟩
    let FM : sfIntegralConstructibleCategory l E X := ⟨_, T.constructible M⟩
    let FN : sfIntegralConstructibleCategory l E X := ⟨_, T.constructible N⟩
    let FH : sfIntegralConstructibleCategory l E X := ⟨_, T.constructible H⟩
    let HX : sfIntegralConstructibleCategory l E X :=
      ⟨_, constructible_hom l E g A T c M N hH⟩
    let f : FH ⟶ HX := ObjectProperty.homMk (homComparison l E g c M.obj N.obj).hom
    apply (cancel_epi (T.tensor M H).inv).mp
    apply (transpose l E X FM FH FN).injective
    simp only [H, Iso.inv_hom_id_assoc]
    have hn := (reflection_laws l E X).2.1 FM FM HX FH FN FN
      (𝟙 FM) f (𝟙 FN) (evaluation l E X FM FN HX.property)
    have heX : transpose l E X FM HX FN (evaluation l E X FM FN HX.property) = 𝟙 _ :=
      (transpose l E X FM HX FN).apply_symm_apply (𝟙 _)
    have heY : transpose l E Y M H N (evaluation l E Y M N hH) = 𝟙 _ :=
      (transpose l E Y M H N).apply_symm_apply (𝟙 _)
    have htr := ht M H N (evaluation l E Y M N hH)
    simp only [heY, CategoryTheory.Functor.map_id, Category.id_comp] at htr
    simp only [ObjectProperty.FullSubcategory.id_hom, Category.comp_id,
      CategoryTheory.Functor.map_id, heX, f, ObjectProperty.homMk,
      CategoryTheory.op_id, ← CategoryTheory.prod_id] at hn ⊢
    exact hn.trans htr.symm
  · as_aux_lemma =>
      intro M M' N N' a b
      exact transportedHom_naturality
        (podReindexingDerivedHom l E Y none) (podReindexingDerivedHom l E X none)
        (podReindexingDerivedFunctor l E g none) (podOrdinaryReindex l E g)
        (reindexIso l E g) c.derived M M' N N' a b

end

/-- Both signed Hom shifts are the existing ordinary shifts. Their completion transport
uses the same signed tensor maps and both actual Roos coordinates.
Source: blueprint dual-Tate compatibility, Steps 4--5; Stacks 011G, 0A8X, 099B
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof (node Step 6): on Hom degree r the double shift reindexes its source by a
and multiplies by (-1)^(a*r), exactly as in the ordinary evaluation lemma.
The reindexing tensor lemma shifts the second Roos coordinate by (-1)^r.
Thus the ordinary signed square commutes with the tensor completion unit.
Reflector injectivity, as in coherence_iff, makes its completed extension unique.
The chain and derived Hom squares are the ordinary ones with the same c, and
RoosFst and RoosSnd explicitly fix both product coordinates of that extension. -/
theorem signed_shifts {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T) (c : Comparison l E g) :
    (∃ (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X),
      PodReindexSignedShifts l E g A T SY SX) ∧
    (∃ (sX : PodReindexingCoherence.ChainShift l E X none)
      (sY : PodReindexingCoherence.ChainShift l E Y none),
      PodReindexingCoherence.ShiftLaws l E g none (closed l E X) (closed l E Y)
        (models l E X) (models l E Y) c sX sY) ∧
    PodCompletionReindex.RoosFst l E g A ∧ PodCompletionReindex.RoosSnd l E g A := by
  obtain ⟨_, _, _, hs⟩ := PodReindexingCoherence.comparison_exists l E g none
    (closed l E X) (closed l E Y) (models l E X) (models l E Y)
  exact ⟨podNormalized_tensor_signed_shifts l E g A T hA hT, hs c,
    hA.2.2.2.2.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2.2.2.2.1⟩

private theorem coefficient_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g none) = isoReductionCompletedMap l E g := by
  have hπ (W : Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n) =
          limit.π (integralCoefficientSheafSystem l E W) (op n) := by rfl
  have hc := (podReindexingCoefficient_existsUnique l E g).exists.choose_spec
  have he : (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g none) = isoReductionCompletedMap l E g := by
    apply (isoReductionCompletedMap_existsUnique l E g).unique
    · intro n
      have hn := congrArg
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (hc.2 n)
      change _ ≫ limit.π (integralCoefficientSheafSystem l E X) (op n) = _
      have hm : (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((isoSectionwiseInverseImage g CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E Y n)) =
          (isoSectionwiseInverseImage g RingCat.{u + 1}).map
            ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (completedIntegralCommRingProjectionUnrestricted l E Y n)) := rfl
      simpa only [Functor.map_comp, hm, hπ, hc.1 n, podReindexingCoefficient,
        Functor.mapIso_hom] using hn
    · exact (isoReductionCompletedMap_existsUnique l E g).exists.choose_spec
  exact he

section CoherenceTransport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type*} [Category C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] cachedCompose

attribute [local irreducible] podReindexingCoefficient isoReductionCompletedMap

private abbrev ambientRing (W : Scheme.{u}) :=
  (sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (podReindexingRing l E W none)

private theorem ordinary_reindex_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podReindexingFunctor l E g none = isoReductionIntegralInverse l E g := by
  exact congrArg (fun c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      (ambientRing l E Y) ≅
        ambientRing l E X ↦
      isoSectionwiseModuleInverseImage.{u, u} g c.hom) (coefficient_eq l E g)

private theorem reindex_exact {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (podReindexingFunctor l E g none).Additive ∧
      PreservesFiniteLimits (podReindexingFunctor l E g none) ∧
      PreservesFiniteColimits (podReindexingFunctor l E g none) := by
  let c := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (podReindexingCoefficient l E g none)
  exact @isoSectionwiseModuleInverseImage_exact.{u, u} X Y g inferInstance _ _ c.hom
    c.isIso_hom

private theorem ordinary_exact {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionIntegralInverse l E g).Additive ∧
      PreservesFiniteLimits (isoReductionIntegralInverse l E g) ∧
      PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
  (ordinary_reindex_eq l E g) ▸ reindex_exact l E g

private theorem reindex_additive {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (podReindexingFunctor l E g none).Additive := (reindex_exact l E g).1

private theorem reindex_limits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (podReindexingFunctor l E g none) := (reindex_exact l E g).2.1

private theorem reindex_colimits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (podReindexingFunctor l E g none) := (reindex_exact l E g).2.2

private theorem ordinary_additive {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionIntegralInverse l E g).Additive := (ordinary_exact l E g).1

private theorem ordinary_limits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (isoReductionIntegralInverse l E g) := (ordinary_exact l E g).2.1

private theorem ordinary_colimits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (isoReductionIntegralInverse l E g) := (ordinary_exact l E g).2.2

attribute [local instance 1000001] reindex_additive reindex_limits reindex_colimits
  ordinary_additive ordinary_limits ordinary_colimits

private def transportHom {C B : Type*} [Category C] [Category B]
    (HC : Cᵒᵖ × C ⥤ C) (HB : Bᵒᵖ × B ⥤ B) {F G : C ⥤ B}
    (e : F ≅ G)
    (c : ∀ M N : C, F.obj (HC.obj (op M, N)) ≅ HB.obj (op (F.obj M), F.obj N))
    (M N : C) :=
  (e.app (HC.obj (op M, N))).symm ≪≫ c M N ≪≫
    HB.mapIso (((e.app M).symm.op).prod (e.app N))

attribute [local irreducible] podReindexCalculus HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

attribute [local instance 1000001] HasDerivedCategory.standard

attribute [local irreducible] derivedInternalHomOfUniverses reindexIso podOrdinaryReindex
  PodReindexFamily.identityDerived PodReindexFamily.compositionDerived

-- Abstract the isomorphisms before specializing the categorical calculation. This keeps
-- the kernel from unfolding the derived identity and compositor constructions.
end CoherenceTransport

/-- A single normalized completion family supplies the stated reflection transport
for every scheme isomorphism, with no additional geometric or perfection hypotheses.
Source: blueprint dual-Tate compatibility, Steps 2, 4--5; Stacks 099B, 0A0E, 099M
(blueprint: lem-pod-reindexing-completed-evaluation-reflection).

Proof: apply the unit/tensor reindexing theorem once to obtain its coherent family.
At every isomorphism use the ordinary evaluation lemma with the recorded closed
calculus and K-flat models to obtain c⁰. Node Steps 1--2 give precompose_bijective
and reflection_laws, Step 3 gives constructible_hom and restrictedComparison,
Steps 4--5 give reindexing_laws, and Step 6 gives signed_shifts and
identity_composition. All maps are the original maps fixed by quotient projections,
Hom-product projections and tensor generators; fullness only restricts them.
Consequently the same completion-unit extensions preserve both normalized Roos
coordinates. Empty schemes, zero objects and arbitrary signed shifts are included. -/
theorem podReindexingCompletedEvaluationReflection :
    ∃ A : PodReindexFamily l E,
      A.Relabelling l E ∧ A.Identity l E ∧ A.Composition l E ∧
      ∀ {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)],
        PodCompletionReindex.Laws l E g (A.completion g) ∧
        PodCompletedTensorReindex.Laws l E g (A.completion g) (A.tensor g) ∧
        A.TensorConstraints l E g ∧
        (∀ M : sfIntegralConstructibleCategory l E Y,
          IsIso ((podOrdinaryToCompleted l E g (A.completion g)).app M.obj)) ∧
        ∃ c : Comparison l E g,
          ReindexingLaws l E g (A.completion g) (A.tensor g) c ∧
          (∃ (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X),
            PodReindexSignedShifts l E g (A.completion g) (A.tensor g) SY SX) ∧
          (∃ (sX : PodReindexingCoherence.ChainShift l E X none)
            (sY : PodReindexingCoherence.ChainShift l E Y none),
            PodReindexingCoherence.ShiftLaws l E g none (closed l E X) (closed l E Y)
              (models l E X) (models l E Y) c sX sY) := by
  have : ∀ w : (Scheme.empty : Scheme.{u}),
      Invertible (l : (Scheme.empty : Scheme.{u}).residueField w) := fun w ↦ PEmpty.elim w
  obtain ⟨A, hR, hI, hC, hF, _⟩ :=
    podReindexingCompletionUnitTensor l E (𝟙 (Scheme.empty : Scheme.{u}))
  refine ⟨A, hR, hI, hC, ?_⟩
  intro X Y g _ _ _
  obtain ⟨hA, _, hU, hT, hTC⟩ := hF g
  obtain ⟨c, _, hs, _⟩ := PodReindexingCoherence.comparison_exists l E g none
    (closed l E X) (closed l E Y) (models l E X) (models l E Y)
  exact ⟨hA, hT, hTC, hU, c,
    reindexing_laws l E g (A.completion g) (A.tensor g) hA hT c,
    (signed_shifts l E g (A.completion g) (A.tensor g) hA hT c).1, hs⟩

end WeilConjectures.PodCompletedReflection
