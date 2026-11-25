/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement

/-! # Evaluation of the normalized reduction tensor square

Source: Stacks 06YS, 07A4 and 0941.
(blueprint: lem-coef-reduction-tensor-evaluation-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.uniformProd
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.integralReductionTargetHasDerivedCategory
  WeilConjectures.coefficientFiniteHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor CoefficientClosedStructure.tensor
  coefficientIntegralTensorModelIso coefficientSystemTensorModelIso
  coefficientFiniteTensorModelIso coefficientFiniteReductionModel
  coefficientScalarTensorIso coefficientEvaluationTensorIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section Pasting
universe a b
private theorem pasteTensorSquares
    {D : Type a} [Category.{b} D]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ C₀ C₁ C₂ C₃ C₄ C₅ D₀ D₁ D₂ D₃ : D}
    (pre : A₀ ⟶ A₁) [Epi pre] (r : A₁ ⟶ A₂) (e : A₂ ⟶ A₃)
    (p : A₃ ⟶ A₄) (m : A₄ ⟶ A₅) [Mono m]
    (c : A₃ ⟶ B₀) (f : B₀ ⟶ B₁) (k : B₁ ⟶ A₅)
    (j : A₂ ⟶ C₀) (e' : C₀ ⟶ B₀)
    (z : A₀ ⟶ C₁) (psi : C₁ ⟶ C₂) (bb : C₂ ⟶ C₀)
    (efT : C₂ ⟶ C₃) (ev : C₃ ⟶ C₄) (cEval : C₄ ⟶ B₁)
    (tk : C₄ ⟶ C₅) (cFin : C₅ ⟶ A₅)
    (efZ : C₁ ⟶ D₀) (qpsi : D₀ ⟶ C₃) (qkZ : D₀ ⟶ D₁)
    (qscalar : D₁ ⟶ C₅) (rhoQ : A₀ ⟶ D₂) (mt : D₂ ⟶ D₁)
    (gm : D₂ ⟶ D₃) (rho : A₁ ⟶ D₃) (mu : D₃ ⟶ A₄)
    (hprod : p ≫ m = c ≫ f ≫ k)
    (hnat : e ≫ c = j ≫ e')
    (hR : pre ≫ r ≫ j = z ≫ psi ≫ bb)
    (hE : bb ≫ e' ≫ f = efT ≫ ev ≫ cEval)
    (hmodel : cEval ≫ k = tk ≫ cFin)
    (hpsi : psi ≫ efT = efZ ≫ qpsi)
    (hchain : qpsi ≫ ev ≫ tk = qkZ ≫ qscalar)
    (hZ : z ≫ efZ ≫ qkZ = rhoQ ≫ mt)
    (hF : gm ≫ mu ≫ m = mt ≫ qscalar ≫ cFin)
    (hrho : pre ≫ rho = rhoQ ≫ gm) :
    r ≫ e ≫ p = rho ≫ mu := by
  apply (cancel_epi pre).1
  apply (cancel_mono m).1
  simp only [Category.assoc]
  calc
    pre ≫ r ≫ e ≫ p ≫ m = pre ≫ r ≫ e ≫ c ≫ f ≫ k := by rw [hprod]
    _ = pre ≫ r ≫ j ≫ e' ≫ f ≫ k := by rw [reassoc_of% hnat]
    _ = z ≫ psi ≫ bb ≫ e' ≫ f ≫ k := by rw [reassoc_of% hR]
    _ = z ≫ psi ≫ efT ≫ ev ≫ cEval ≫ k := by rw [reassoc_of% hE]
    _ = z ≫ psi ≫ efT ≫ ev ≫ tk ≫ cFin := by rw [hmodel]
    _ = z ≫ efZ ≫ qpsi ≫ ev ≫ tk ≫ cFin := by rw [reassoc_of% hpsi]
    _ = z ≫ efZ ≫ qkZ ≫ qscalar ≫ cFin := by rw [reassoc_of% hchain]
    _ = rhoQ ≫ mt ≫ qscalar ≫ cFin := by rw [reassoc_of% hZ]
    _ = rhoQ ≫ gm ≫ mu ≫ m := by rw [hF]
    _ = pre ≫ rho ≫ mu ≫ m := by rw [reassoc_of% hrho]

private theorem mapPairComp
    {C : Type a} [Category.{b} C] {D : Type*} [Category D]
    (T : C × C ⥤ D) {X Y Z X' Y' Z' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) (i : Y' ⟶ Z') :
    T.map (Prod.mkHom f g) ≫ T.map (Prod.mkHom h i) =
      T.map (Prod.mkHom (f ≫ h) (g ≫ i)) := by
  rw [← T.map_comp]
  rfl
private theorem mapComparison
    {C : Type a} [Category.{b} C] {D : Type*} [Category D]
    (F : C ⥤ D) {X Y Z T U : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T} {i : X ⟶ U} {j : U ⟶ T}
    (hh : f ≫ g ≫ h = i ≫ j) :
    F.map f ≫ F.map g ≫ F.map h = F.map i ≫ F.map j := by
  simpa only [Functor.map_comp] using congrArg F.map hh
end Pasting

section ModelNaturality
universe c v r w
private theorem tensorModel_naturality
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J A)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J A))
    (M : CoefficientTensorModels.{r, c, v, w} J A S)
    (P Q P' Q' : CochainComplex (SheafOfModules.scalarModules J A) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (CoefficientTensorModels.iso J A S M P Q hP hQ).hom ≫
        S.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) =
      DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)) ≫
        (CoefficientTensorModels.iso J A S M P' Q' hP' hQ').hom := by
  have hn := M.comparison.hom.naturality
    (Prod.mkHom (show (⟨P, hP⟩ : ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A))) ⟶ ⟨P', hP'⟩
      from ObjectProperty.homMk f)
      (show (⟨Q, hQ⟩ : ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A))) ⟶ ⟨Q', hQ'⟩
        from ObjectProperty.homMk g))
  simpa only [CoefficientTensorModels.iso, Iso.app, Functor.comp_map, Functor.prod_map,
    coefficientKFlatInclusion, ObjectProperty.ι_map, ObjectProperty.homMk,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] using hn.symm
end ModelNaturality

private theorem evaluation_on_representatives
    (R : CoefficientDerivedSystemReduction l E W)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (fP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
      (P.X i))
    (fQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
      (Q.X i)) (n : ℕ) :
    CoefficientComparisonEquation
      ((coefficientSequenceDerivedEvaluation l E W n).map
        (R.reductionTensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
      ((R.evaluationTensor n).hom.app
        (R.reduction.obj (DerivedCategory.Q.obj P), R.reduction.obj (DerivedCategory.Q.obj Q)))
      ((R.finiteClosed n).tensor.map
        (Prod.mkHom ((R.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P))
          ((R.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q))))
      ((R.reductionEvaluation n).hom.app
        (R.integralClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
      ((R.finiteTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  obtain ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ,
    hPC, hPD, hPZ, hψ, hs⟩ := hR P Q hP hQ fP fQ
  let Ev := coefficientSequenceDerivedEvaluation l E W n
  let F := R.reduction
  let G := coefficientFiniteDerivedExtension l E W n
  let T := (R.finiteClosed n).tensor
  let tc := coefficientTotalTensor.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let tf := coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let eqc := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors
  let a := coefficientIntegralTensorModelIso l E W R.toCoefficientDerivedSystemTensors P Q hP hQ
  let b := coefficientSystemTensorModelIso l E W R.toCoefficientDerivedSystemTensors C D hC hD
  let mp := coefficientFiniteReductionModel l E W P hP n
  let mq := coefficientFiniteReductionModel l E W Q hQ n
  let hPQ := coefficientTotalTensor_isKFlat.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q hP hQ
  let ti := coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let mt := coefficientFiniteReductionModel l E W (ti.obj (P,Q)) hPQ n
  let ep := (coefficientTensorModelPreservation l E W).2 C hC n
  let eq := (coefficientTensorModelPreservation l E W).2 D hD n
  let fp := (coefficientTensorModelPreservation l E W).1 P hP n
  let fq := (coefficientTensorModelPreservation l E W).1 Q hQ n
  let cm := coefficientFiniteTensorModelIso l E W R.toCoefficientDerivedSystemTensors n _ _ ep eq
  let fm := coefficientFiniteTensorModelIso l E W R.toCoefficientDerivedSystemTensors n _ _ fp fq
  let ρ := (R.reductionEvaluation n).hom
  let μ := (R.evaluationTensor n).hom
  let κ := Prod.mkHom (κC n).hom (κD n).hom
  have hp := (hPC.1 n)
  have hq := (hPD.1 n)
  have hz := (hPZ.1 n)
  unfold CoefficientComparisonEquation at hp hq hz
  have hprod : T.map (Prod.mkHom (ρ.app (DerivedCategory.Q.obj P))
      (ρ.app (DerivedCategory.Q.obj Q))) ≫ T.map (Prod.mkHom mp.hom mq.hom) =
      T.map (Prod.mkHom (Ev.map eC.hom) (Ev.map eD.hom)) ≫
        T.map (Prod.mkHom (eqc.hom.app C) (eqc.hom.app D)) ≫
          T.map (Prod.mkHom (DerivedCategory.Q.map (κC n).hom)
            (DerivedCategory.Q.map (κD n).hom)) := by
    rw [mapPairComp, ← hp, ← hq, ← mapPairComp, ← mapPairComp]
  have hn := μ.naturality (Prod.mkHom eC.hom eD.hom)
  have hr := congrArg Ev.map hs
  have he := hE n C D hC hD
  have hf := hF n P Q hP hQ
  have hqψ := eqc.hom.naturality ψ
  have hρ := ρ.naturality a.hom
  unfold CoefficientTensorComparisonSquare at hs he hf
  simp only [Functor.map_comp] at hr
  unfold CoefficientComparisonEquation
  have : IsIso (Prod.mkHom mp.hom mq.hom) := by
    change IsIso (Iso.prod mp mq).hom
    infer_instance
  apply pasteTensorSquares
    (Ev.map (F.map a.hom)) _ _ _ (T.map (Prod.mkHom mp.hom mq.hom))
    (T.map (Prod.mkHom (Ev.map eC.hom) (Ev.map eD.hom)))
    (T.map (Prod.mkHom (eqc.hom.app C) (eqc.hom.app D)))
    (T.map (Prod.mkHom (DerivedCategory.Q.map (κC n).hom)
      (DerivedCategory.Q.map (κD n).hom)))
    (Ev.map (R.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
    (μ.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj D))
    (Ev.map eZ.hom) (Ev.map (DerivedCategory.Q.map ψ)) (Ev.map b.hom)
    (eqc.hom.app (tc.obj (C,D)))
    (DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n C D).hom) cm.hom
    (DerivedCategory.Q.map (tf.map κ)) fm.hom
    (eqc.hom.app Z)
    (DerivedCategory.Q.map
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ))
    (DerivedCategory.Q.map (κZ n).hom)
    (DerivedCategory.Q.map (coefficientScalarTensorIso l E W n P Q).hom)
    (ρ.app (DerivedCategory.Q.obj (ti.obj (P,Q)))) mt.hom
    (G.map a.hom) (ρ.app (R.integralClosed.tensor.obj
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    ((R.finiteTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
  · exact hprod
  · exact hn.symm
  · exact hr
  · exact he
  · dsimp only [cm, fm, T, tf, κ]
    unfold coefficientFiniteTensorModelIso
    exact tensorModel_naturality (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
      _ _ _ _ ep eq fp fq (κC n).hom (κD n).hom
  · exact hqψ
  · exact mapComparison DerivedCategory.Q (hψ n)
  · exact hz
  · exact hf
  · exact hρ

/-- The three representative tensor normalizations imply the reduction/evaluation law.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product; 0941,
compatibility of the strict reduction model with finite evaluation.

Proof: restrict both natural transformations in the claimed equation to pairs of
flat-term K-flat integral complexes; this restriction is faithful by cochain tensor
model rigidity. Choose the three simultaneous presentations and strict tensor map
from hR. Evaluate its final system-derived square at n. Use naturality of the
exact evaluation/localization comparison on the strict tensor map, followed by hE,
to express the evaluated tensor square on the evaluated representatives. Compose
with the finite identifications of the three presentations. Naturality of the
finite tensor-model comparison moves these identifications across its square.
The finite-component identity for the strict tensor map then replaces the middle
composite by the ordinary scalar tensor map. The three presentation equations
identify its outer maps with reductionEvaluation and the prescribed finite
reduction models. Apply hF to the resulting scalar tensor square. Cancel the
integral tensor-model isomorphism and the two finite reduction-model isomorphisms.
This proves the desired equality on representatives, and faithfulness gives it
for arbitrary derived inputs. No faithfulness of level evaluation is asserted.
(blueprint: lem-coef-reduction-tensor-evaluation-pasting). -/
theorem coefficientReductionTensorEvaluation_of_normalizations
    (R : CoefficientDerivedSystemReduction l E W)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (hE : CoefficientEvaluationTensorNormalization l E W R) :
    CoefficientReductionTensorEvaluation l E W R := by
  intro P Q n
  let F := R.reduction
  let Ev := coefficientSequenceDerivedEvaluation l E W n
  let G := coefficientFiniteDerivedExtension l E W n
  let T := (R.finiteClosed n).tensor
  let ρ := R.reductionEvaluation n
  let lhs : R.integralClosed.tensor ⋙ F ⋙ Ev ⟶ G.prod G ⋙ T :=
    (Functor.isoWhiskerRight R.reductionTensor Ev).hom ≫
      (Functor.isoWhiskerLeft (F.prod F) (R.evaluationTensor n)).hom ≫
        (Functor.isoWhiskerRight (NatIso.prod ρ ρ) T).hom
  let rhs : R.integralClosed.tensor ⋙ F ⋙ Ev ⟶ G.prod G ⋙ T :=
    (Functor.isoWhiskerLeft R.integralClosed.tensor ρ).hom ≫ (R.finiteTensor n).hom
  have hh : lhs = rhs := by
    have hff := (SheafOfModules.cochain_tensor_model_rigidity.{t+1, t,
      max u (t+1), max (t+2) (u+1), _, _} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.2.2
      (normalizedDVRDerived l E W n) inferInstance
    apply (hff _ _).1
    ext X
    obtain ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩ := X
    exact evaluation_on_representatives l E W R hR hF hE P Q
      hp.1 hq.1 hp.2 hq.2 n
  exact congrArg (fun η ↦ η.app (P, Q)) hh

end WeilConjectures
