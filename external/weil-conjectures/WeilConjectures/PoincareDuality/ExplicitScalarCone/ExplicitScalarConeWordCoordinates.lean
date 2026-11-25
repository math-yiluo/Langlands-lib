/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SixFunctors.Supporting.SpecifiedPullbackComparisonAlpha
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SixFunctors.Scalar.ScalarPullbackStrictConeNaturality
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
import WeilConjectures.PoincareDuality.PrimitiveReductionTransport.PrimitiveQuotientRealizationsTransport
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackCompletionNormalization
import WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # The explicit scalar cone in normalized word coordinates

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, first sentence through prose-10-20,
first paragraph; agent-extracted normalization calculation
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates).

Positive exponent n+1 is indexed by n. The two word coordinates use the actual
whole-system counits and arbitrary supplied normalized primitive models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.ExplicitScalarCone

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
  (SEY : CoefficientDerivedSystemCalculus l E Y)

/-- The first whole-system word U_g,E R_E,Y K.
Source: the node's displayed definitions of C and A
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def pullbackSystem (K : DerivedCategory (integralTowerModules l E Y)) :=
  (integralComparisonDerivedSequencePullback l E g).obj (SEY.reduction.obj K)

/-- The first scalar word S_Y R_E,Y K, before its pullback.
Source: the node's displayed definitions of C and B
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def scalarSystem (K : DerivedCategory (integralTowerModules l E Y)) :=
  (integralComparisonDerivedSequenceScalar l E L ι Y).obj (SEY.reduction.obj K)

/-- The source quotient-system word A = S_X U_g,E C.
Source: the node's displayed definition of A
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def sourceSystem (K : DerivedCategory (integralTowerModules l E Y)) :=
  (integralComparisonDerivedSequenceScalar l E L ι X).obj
    (pullbackSystem l E g SEY K)

/-- The target quotient-system word B = U_g,L S_Y C.
Source: the node's displayed definition of B
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def targetSystem (K : DerivedCategory (integralTowerModules l E Y)) :=
  (integralComparisonDerivedSequencePullback l L g).obj (scalarSystem l E L ι SEY K)

variable (SEX : CoefficientDerivedSystemCalculus l E X)
  (SLY : CoefficientDerivedSystemCalculus l L Y)
  (ρEX : IntegralComparisonRoosModel l E X)
  (ρLX : IntegralComparisonRoosModel l L X)
  (ρLY : IntegralComparisonRoosModel l L Y)
  (UE : IntegralComparisonPullbackModel l E g SEY ρEX)
  (UL : IntegralComparisonPullbackModel l L g SLY ρLX)
  (SX : IntegralComparisonScalarModel l E L ι X SEX ρLX)
  (SY : IntegralComparisonScalarModel l E L ι Y SEY ρLY)

/-- beta_A is S-hat_X(b_U,K), then b_S,LUC, then L(S_X(e_UC)).
This is exactly r_S,UC composed with S-hat_X(b_U,K).
Source: the node's displayed beta_A and r formulas
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def betaA (K : DerivedCategory (integralTowerModules l E Y)) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((integralDerivedPullback l E g).obj K) ⟶
      (coefficientSequenceLimit l L X).obj (sourceSystem l E L ι g SEY K) :=
  (integralScalarExtensionOfUniverses l E L ι X).map (UE.realization.hom.app K) ≫
    SX.realization.hom.app
      ((coefficientSequenceLimit l E X).obj (pullbackSystem l E g SEY K)) ≫
    (coefficientSequenceLimit l L X).map
      ((integralComparisonDerivedSequenceScalar l E L ι X).map
        (SEX.adjunction.counit.app (pullbackSystem l E g SEY K)))

/-- beta_B is U-hat_g,L(b_S,K), then b_U,LSC, then L(U_g,L(e_SC)).
It retains the entire-system counit of the scalar intermediate system.
Source: the node's displayed beta_B and r formulas
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates). -/
def betaB (K : DerivedCategory (integralTowerModules l E Y)) :
    (integralDerivedPullback l L g).obj
        ((integralScalarExtensionOfUniverses l E L ι Y).obj K) ⟶
      (coefficientSequenceLimit l L X).obj (targetSystem l E L ι g SEY K) :=
  (integralDerivedPullback l L g).map (SY.realization.hom.app K) ≫
    UL.realization.hom.app
      ((coefficientSequenceLimit l L Y).obj (scalarSystem l E L ι SEY K)) ≫
    (coefficientSequenceLimit l L X).map
      ((integralComparisonDerivedSequencePullback l L g).map
        (SLY.adjunction.counit.app (scalarSystem l E L ι SEY K)))

section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel
  coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback

private theorem roos_eq (W : AlgebraicGeometry.Scheme.{u})
    (ρ ρ' : IntegralComparisonRoosModel l E W) : ρ = ρ' := by
  suffices h : ρ.comparison = ρ'.comparison by
    cases ρ
    cases ρ'
    cases h
    rfl
  apply Iso.ext_inv
  apply NatTrans.ext
  funext C
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso q := hq
  have : IsIso ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q) := by
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q))
    infer_instance
  have hi : ρ.comparison.app I = ρ'.comparison.app I := by
    apply Iso.ext
    exact (ρ.computes I).trans (ρ'.computes I).symm
  apply (cancel_mono ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q)).1
  rw [← ρ.comparison.inv.naturality q, ← ρ'.comparison.inv.naturality q]
  exact congrArg (fun z ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q ≫ z) (congrArg Iso.inv hi)

private theorem coordinate_eq
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (O : B ⥤ C) (L : C ⥤ D) (H : A ⥤ D)
    (b : H ⟶ R ⋙ O ⋙ L) {P Q : A} {N : B} (f : P ⟶ Q) (e : R.obj Q ⟶ N) :
    H.map f ≫ (b.app Q ≫ L.map (O.map e)) =
      b.app P ≫ L.map (O.map (R.map f ≫ e)) := by
  rw [← Category.assoc, b.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

private theorem coordinate_change
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R R' : A ⥤ B) (J : B ⥤ A) (O : B ⥤ C) (L : C ⥤ D) (H : A ⥤ D)
    (α : R ≅ R') (ε : J ⋙ R ⟶ 𝟭 B) (ε' : J ⋙ R' ⟶ 𝟭 B)
    (b : H ⟶ R ⋙ O ⋙ L) (b' : H ⟶ R' ⋙ O ⋙ L)
    {P : A} {N N' : B} (f : P ⟶ J.obj N) (f' : P ⟶ J.obj N') (a : N ⟶ N')
    (hf : f ≫ J.map a = f')
    (hb : b.app P ≫ L.map (O.map (α.hom.app P)) = b'.app P)
    (hε : α.hom.app (J.obj N') ≫ ε'.app N' = ε.app N') :
    (H.map f ≫ b.app (J.obj N) ≫ L.map (O.map (ε.app N))) ≫ L.map (O.map a) =
      H.map f' ≫ b'.app (J.obj N') ≫ L.map (O.map (ε'.app N')) := by
  have h : R.map f ≫ ε.app N ≫ a = R.map f' ≫ ε.app N' := by
    have hn := ε.naturality a
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← hn, ← Category.assoc, ← R.map_comp, hf]
  have k : R.map f' ≫ ε.app N' =
      α.hom.app P ≫ R'.map f' ≫ ε'.app N' := by
    rw [← hε, ← Category.assoc, α.hom.naturality f', Category.assoc]
  rw [coordinate_eq R O L H b f (ε.app N),
    coordinate_eq R' O L H b' f' (ε'.app N')]
  rw [Category.assoc, ← L.map_comp, ← O.map_comp, Category.assoc, h, k]
  simp only [O.map_comp, L.map_comp, ← Category.assoc]
  rw [hb]

private theorem map_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B B' Z : C} (f : A ⟶ B) (g : B ⟶ Z) (h : A ⟶ B') (i : B' ⟶ Z)
    (e : f ≫ g = h ≫ i) : F.map f ≫ F.map g = F.map h ≫ F.map i := by
  rw [← F.map_comp, ← F.map_comp, e]

private theorem normalized_transport
    {C : Type*} [Category* C] {X Y A B A' B' : C}
    (α : X ⟶ Y) (p : X ⟶ A) (q : Y ⟶ B) (k : A ⟶ B)
    (a : A ⟶ A') (b : B ≅ B')
    (lam : X ⟶ A') (mu : Y ⟶ A') (k' : A' ⟶ B')
    (hp : p ≫ a = lam) (hq : q ≫ b.hom = mu ≫ k')
    (hα : α ≫ mu = lam) (hk : a ≫ k' = k ≫ b.hom) : α ≫ q = p ≫ k := by
  apply (cancel_mono b.hom).1
  calc
    (α ≫ q) ≫ b.hom = α ≫ (q ≫ b.hom) := Category.assoc _ _ _
    _ = α ≫ (mu ≫ k') := congrArg (fun z ↦ α ≫ z) hq
    _ = (α ≫ mu) ≫ k' := (Category.assoc _ _ _).symm
    _ = lam ≫ k' := congrArg (fun z ↦ z ≫ k') hα
    _ = (p ≫ a) ≫ k' := congrArg (fun z ↦ z ≫ k') hp.symm
    _ = p ≫ (a ≫ k') := Category.assoc _ _ _
    _ = p ≫ (k ≫ b.hom) := congrArg (fun z ↦ p ≫ z) hk
    _ = (p ≫ k) ≫ b.hom := (Category.assoc _ _ _).symm

/-- The explicit tensor/completion arrow in the prescribed two word coordinates.
The five effectivity hypotheses are at C, U_E C, S_Y C, A, and B respectively.
Each lists normalization, constructible-complete realization, and invertible counit.
The primitive realization structures impose the simultaneous quotient and Roos
normalizations; no finite-level flatness or Tor interval is assumed.

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, first sentence through prose-10-20,
first paragraph; agent-extracted comparison normalization
(blueprint: lem-pod-explicit-scalar-cone-word-coordinates).

Proof:
1. Choose one simultaneous normalized comparison system D. Its Roos models equal
   the supplied ones: compare on K-injective resolutions using the normalized
   computes equations, then extend by naturality and cancellation.
2. Compare any two reduction calculi S,T by leftAdjointUniq. The unit-projection
   equations identify its finite evaluation maps. Hence whole-system quotient
   presentations and their coherence transport across this isomorphism. Transport
   the primitive realization models with them and apply primitive uniqueness.
   This identifies the supplied realizations with those of D, after applying the
   system operation and total derived limit to the reduction comparison.
3. Naturality of the primitive realizations rewrites each word coordinate as its
   initial realization followed by the image of a reduction/counit composite.
   Naturality of the actual counit and the leftAdjointUniq counit equation then
   transport both word coordinates to D, retaining the intermediate counits.
4. In D the source coordinate is lambda and the target coordinate is mu followed
   by L(kappa). The existing completed scalar pullback normalization gives
   alpha ; mu = lambda for the specified tensor-and-completion comparison.
5. Postcompose the required equality with the invertible image of the initial
   reduction comparison. Substitute the transported coordinates and use the
   naturality of kappa. Cancelling this isomorphism proves the equality.

These are whole-system calculations. No faithfulness of the separate finite
levels, flatness of a ramified quotient map, or additional Tor bound is used.
-/
theorem explicitScalarConeWordCoordinates
    [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SLX : CoefficientDerivedSystemCalculus l L X)
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K)
    (_hC : IsNormalizedCoefficientSequence l E Y (SEY.reduction.obj K) ∧
      sfIntegralConstructible l E Y
        ((coefficientSequenceLimit l E Y).obj (SEY.reduction.obj K)) ∧
      IsIso (SEY.adjunction.counit.app (SEY.reduction.obj K)))
    (_hU : IsNormalizedCoefficientSequence l E X (pullbackSystem l E g SEY K) ∧
      sfIntegralConstructible l E X
        ((coefficientSequenceLimit l E X).obj (pullbackSystem l E g SEY K)) ∧
      IsIso (SEX.adjunction.counit.app (pullbackSystem l E g SEY K)))
    (_hS : IsNormalizedCoefficientSequence l L Y (scalarSystem l E L ι SEY K) ∧
      sfIntegralConstructible l L Y
        ((coefficientSequenceLimit l L Y).obj (scalarSystem l E L ι SEY K)) ∧
      IsIso (SLY.adjunction.counit.app (scalarSystem l E L ι SEY K)))
    (_hA : IsNormalizedCoefficientSequence l L X (sourceSystem l E L ι g SEY K) ∧
      sfIntegralConstructible l L X
        ((coefficientSequenceLimit l L X).obj (sourceSystem l E L ι g SEY K)) ∧
      IsIso (SLX.adjunction.counit.app (sourceSystem l E L ι g SEY K)))
    (_hB : IsNormalizedCoefficientSequence l L X (targetSystem l E L ι g SEY K) ∧
      sfIntegralConstructible l L X
        ((coefficientSequenceLimit l L X).obj (targetSystem l E L ι g SEY K)) ∧
      IsIso (SLX.adjunction.counit.app (targetSystem l E L ι g SEY K))) :
    (scalarPullbackCompleted l E L ι g K hK.1
        (specifiedPullbackComparisonAlpha l E L ι g K hK).choose).hom ≫
        betaB l E L ι g SEY SLY ρLX ρLY UL SY K =
      betaA l E L ι g SEY SEX ρEX ρLX UE SX K ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSystemScalarPullback l E L ι g).hom.app
            (SEY.reduction.obj K)) := by
  classical
  obtain ⟨D⟩ := ambientComparisonSystem_exists.{u} l
  have hρEX := roos_eq l E X ρEX ((D.coefficient E).roos X)
  have hρLX := roos_eq l L X ρLX ((D.coefficient L).roos X)
  have hρLY := roos_eq l L Y ρLY ((D.coefficient L).roos Y)
  subst ρEX
  subst ρLX
  subst ρLY
  let TEY := (D.coefficient E).system Y
  let TEX := (D.coefficient E).system X
  let TLY := (D.coefficient L).system Y
  let a₀ := SEY.adjunction.leftAdjointUniq TEY.adjunction
  let a₁ := SEX.adjunction.leftAdjointUniq TEX.adjunction
  let a₂ := SLY.adjunction.leftAdjointUniq TLY.adjunction
  let UE' := (D.coefficient E).pullback g
  let UL' := (D.coefficient L).pullback g
  let SX' := (D.scalar E L ι).model X
  let SY' := (D.scalar E L ι).model Y
  let U := integralComparisonDerivedSequencePullback l E g
  let V := integralComparisonDerivedSequencePullback l L g
  let S := integralComparisonDerivedSequenceScalar l E L ι X
  let T := integralComparisonDerivedSequenceScalar l E L ι Y
  let LL := coefficientSequenceLimit l L X
  have hUE := (PrimitiveReductionTransport.realizations_transport l E L ι g SEY TEY
    ((D.coefficient E).roos X) ((D.coefficient L).roos Y) UE' SY').1 UE K
  have hUL := (PrimitiveReductionTransport.realizations_transport l L L
    (AlgHom.id ℚ_[l] L) g SLY TLY
    ((D.coefficient L).roos X) ((D.coefficient L).roos Y) UL'
    ((D.scalar L L (AlgHom.id ℚ_[l] L)).model Y)).1 UL
  have hSX := (PrimitiveReductionTransport.realizations_transport l E L ι
    (𝟙 X) SEX TEX ((D.coefficient E).roos X) ((D.coefficient L).roos X)
    ((D.coefficient E).pullback (𝟙 X)) SX').2 SX
  have hSY := (PrimitiveReductionTransport.realizations_transport l E L ι
    (𝟙 Y) SEY TEY ((D.coefficient E).roos Y) ((D.coefficient L).roos Y)
    ((D.coefficient E).pullback (𝟙 Y)) SY').2 SY K
  have hA := coordinate_change SEX.reduction TEX.reduction
    (coefficientSequenceLimit l E X) S LL
    (integralScalarExtensionOfUniverses l E L ι X) a₁
    SEX.adjunction.counit TEX.adjunction.counit SX.realization.hom SX'.realization.hom
    (UE.realization.hom.app K) (UE'.realization.hom.app K) (U.map (a₀.hom.app K))
    hUE (hSX _) (SEX.adjunction.leftAdjointUniq_hom_app_counit TEX.adjunction _)
  have hB := coordinate_change SLY.reduction TLY.reduction
    (coefficientSequenceLimit l L Y) V LL (integralDerivedPullback l L g) a₂
    SLY.adjunction.counit TLY.adjunction.counit UL.realization.hom UL'.realization.hom
    (SY.realization.hom.app K) (SY'.realization.hom.app K) (T.map (a₀.hom.app K))
    hSY (hUL _) (SLY.adjunction.leftAdjointUniq_hom_app_counit TLY.adjunction _)
  change betaA l E L ι g SEY SEX ((D.coefficient E).roos X)
      ((D.coefficient L).roos X) UE SX K ≫ LL.map (S.map (U.map (a₀.hom.app K))) =
    betaA l E L ι g TEY TEX ((D.coefficient E).roos X)
      ((D.coefficient L).roos X) UE' SX' K at hA
  change betaB l E L ι g SEY SLY ((D.coefficient L).roos X)
      ((D.coefficient L).roos Y) UL SY K ≫ LL.map (V.map (T.map (a₀.hom.app K))) =
    betaB l E L ι g TEY TLY ((D.coefficient L).roos X)
      ((D.coefficient L).roos Y) UL' SY' K at hB
  have ha : betaA l E L ι g TEY TEX ((D.coefficient E).roos X)
      ((D.coefficient L).roos X) UE' SX' K =
      (integralComparisonLambda l E L ι D g ⟨K, hK⟩).hom := by
    dsimp only [betaA, pullbackSystem, TEY, TEX, UE', SX', integralComparisonLambda,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
      integralComparisonPullbackCounit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    exact coordinate_eq _ _ _ _ _ _ _
  have hb : betaB l E L ι g TEY TLY ((D.coefficient L).roos X)
      ((D.coefficient L).roos Y) UL' SY' K =
      (integralComparisonMu l E L ι D g ⟨K, hK⟩).hom ≫
        LL.map ((integralComparisonSystemScalarPullback l E L ι g).hom.app
          (TEY.reduction.obj K)) := by
    dsimp only [betaB, scalarSystem, TEY, TLY, UL', SY', integralComparisonMu,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
      integralComparisonScalarCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact coordinate_eq _ _ _ _ _ _ _
  have hn := integralScalarPullbackCompletion_normalization l E L ι D g ⟨K, hK⟩
    (specifiedPullbackComparisonAlpha l E L ι g K hK).choose
  have hk := (integralComparisonSystemScalarPullback l E L ι g).hom.naturality
    (a₀.hom.app K)
  change S.map (U.map (a₀.hom.app K)) ≫
      (integralComparisonSystemScalarPullback l E L ι g).hom.app (TEY.reduction.obj K) =
    (integralComparisonSystemScalarPullback l E L ι g).hom.app (SEY.reduction.obj K) ≫
      V.map (T.map (a₀.hom.app K)) at hk
  have hk' := map_square LL _ _ _ _ hk
  exact normalized_transport
    (scalarPullbackCompleted l E L ι g K hK.1
      (specifiedPullbackComparisonAlpha l E L ι g K hK).choose).hom
    (betaA l E L ι g SEY SEX ((D.coefficient E).roos X)
      ((D.coefficient L).roos X) UE SX K)
    (betaB l E L ι g SEY SLY ((D.coefficient L).roos X)
      ((D.coefficient L).roos Y) UL SY K)
    (LL.map ((integralComparisonSystemScalarPullback l E L ι g).hom.app
      (SEY.reduction.obj K)))
    (LL.map (S.map (U.map (a₀.hom.app K))))
    (LL.mapIso (V.mapIso (T.mapIso (a₀.app K))))
    (integralComparisonLambda l E L ι D g ⟨K, hK⟩).hom
    (integralComparisonMu l E L ι D g ⟨K, hK⟩).hom
    (LL.map ((integralComparisonSystemScalarPullback l E L ι g).hom.app
      (TEY.reduction.obj K)))
    (hA.trans ha) (hB.trans hb) hn hk'

end

private theorem reduction_section_map (Y : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    {M N : integralTowerModules l E Y} (f : M ⟶ N) (V : Y.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj V) (x : M.val.obj V) :
    ((unrestrictedIntegralReductionFunctor l E Y n).map f).val.app V
        (unrestrictedIntegralTensorSection l E Y n M V a x) =
      unrestrictedIntegralTensorSection l E Y n N V a (f.val.app V x) := by
  have h : eqToHom (unrestrictedReduction_obj l E Y n M).symm ≫
      (unrestrictedIntegralReductionFunctor l E Y n).map f =
      SheafOfModules.changeOfRingsHom (completedIntegralCommRingProjectionUnrestricted l E Y n)
        M f ≫ eqToHom (unrestrictedReduction_obj l E Y n N).symm := by
    rw [unrestrictedReduction_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  calc
    _ = (eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V
        ((SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M f).val.app V
          (SheafOfModules.UnrestrictedTowerProof.tensorSection
            (completedIntegralCommRingProjectionUnrestricted l E Y n) M V a x)) :=
      congrArg (fun k ↦ k.val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M V a x)) h
    _ = _ := congrArg ((eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V)
      (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M f V a x)

private theorem generator_map {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) {P Q : CochainComplex (integralTowerModules l E Y) ℤ} (f : P ⟶ Q)
    (i : ℤ) (V : Y.ProEt) (p : (P.X i).val.obj (op V))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))) :
    (((integralOperationsPullbackLevel l E g n).map f).f i).val.app
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))
        (scalarPullbackGenerator l E g n P i V p a b) =
      scalarPullbackGenerator l E g n Q i V ((f.f i).val.app (op V) p) a b := by
  let A := AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let f' := (unrestrictedIntegralReductionFunctor l E Y n).map (f.f i)
  have h := congrArg (fun k ↦ k.val.app (op V)
    (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p))
      (A.unit.naturality f')
  change integralOperationsPullbackGenerator l E g n _ V
      (f'.val.app (op V)
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p)) =
    (((integralOperationsLevelPullback l E g n).map f').val.app
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g n _ V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p)) at h
  dsimp only [scalarPullbackGenerator, id_eq]
  change (((integralOperationsLevelPullback l E g n).map f').val.app _)
    (b • _) = b • _
  rw [map_smul]
  apply congrArg (fun z ↦ b • z)
  exact h.symm.trans (congrArg (integralOperationsPullbackGenerator l E g n
    ((unrestrictedIntegralReductionFunctor l E Y n).obj (Q.X i)) V)
      (reduction_section_map l E Y n (f.f i) (op V) a p))

end WeilConjectures.ExplicitScalarCone
