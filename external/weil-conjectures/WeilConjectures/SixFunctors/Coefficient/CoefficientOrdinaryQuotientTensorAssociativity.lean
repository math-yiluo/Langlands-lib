/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssociativity
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # The quotient-system tensor comparison respects the total associators

Source: Stacks 03EK, 07A4 and 0941.

Chain maps of strict systems are tested on all finite evaluations. There the tensor
comparison of the ordinary quotient system becomes the normalized scalar tensor
comparison, whose reassociation is computed in `OrdinaryModel.scalarTensorAssociativity`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

namespace OrdinaryQuotient

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso coefficientScalarTensorIso coefficientUniqueComparisonChoice
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory

/-- The evaluated associator formula holds on arbitrary finite-level sections, by surjectivity
of the section transport. Source: Stacks 03EK, 07A4, 0941. -/
private theorem evaluatedAssociator_generator_section (n : ℕ)
    (X Y Z : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (b' : (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (X, Y), Z) ≅
      (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        (X, (coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (Y, Z)))
    (hb' : CoefficientComplexAssociatorFormula
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) X Y Z b')
    (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr) (hk : pq + r = k)
    (hk' : p + qr = k) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj (X.X p)).val.obj U)
    (y : ((coefficientSequenceEvaluation l E W n).obj (Y.X q)).val.obj U)
    (z : ((coefficientSequenceEvaluation l E W n).obj (Z.X r)).val.obj U) :
    (((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
          (coefficientEvaluationTensorIso l E W n X Y).inv (𝟙 _)) ≫
      (coefficientEvaluationTensorIso l E W n ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (X, Y)) Z).inv ≫
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b'.hom ≫
      (coefficientEvaluationTensorIso l E W n X ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (Y, Z))).hom ≫
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom (𝟙 _)
          (coefficientEvaluationTensorIso l E W n Y Z).hom)).f k).val.app U
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ pq r k hk U
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n) _ _ p q pq hpq U x y) z) =
    coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ p qr k hk' U x
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) _ _ q r qr hqr U y z) := by
  revert x y z
  refine (coefficientEvaluationSection_surjective l E W (X.X p) n U).forall.2 ?_
  intro x
  refine (coefficientEvaluationSection_surjective l E W (Y.X q) n U).forall.2 ?_
  intro y
  refine (coefficientEvaluationSection_surjective l E W (Z.X r) n U).forall.2 ?_
  intro z
  exact evaluatedAssociator_generator l E W n X Y Z b' hb'
    p q r pq qr k hpq hqr hk hk' U x y z

attribute [local semireducible] coefficientSequenceEvaluation in
/-- The scalar-coordinate form of tensor associativity for the quotient system: on unit
insertions of triple generators both composites are the reassociated generator.
Source: Stacks 03EK, 07A4, 0941. -/
theorem OrdinaryModel.scalarTensorAssociativity (M : OrdinaryModel l E W) (n : ℕ)
    (P Q N : CochainComplex (scalarReductionSource l E W) ℤ)
    (a : (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q), N) ≅
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj
        (P, (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N)))
    (ha : CoefficientComplexAssociatorFormula (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P Q N a)
    (b' : (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((M.quotient l E W).obj P, (M.quotient l E W).obj Q), (M.quotient l E W).obj N) ≅
      (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((M.quotient l E W).obj P, (coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((M.quotient l E W).obj Q, (M.quotient l E W).obj N)))
    (hb' : CoefficientComplexAssociatorFormula
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      ((M.quotient l E W).obj P) ((M.quotient l E W).obj Q) ((M.quotient l E W).obj N) b') :
    let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
    let T' := coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
    let tA := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
    let Ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
    let F := (scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)
    let K := M.quotient l E W
    let θ := NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)
    let e := coefficientEvaluationTensorIso l E W n
    let s := coefficientScalarTensorIso l E W n
    F.map a.hom ≫ (s P (tA.obj (Q, N))).hom ≫ T.map (Prod.mkHom (𝟙 (F.obj P)) (s Q N).hom) =
    (s (tA.obj (P, Q)) N).hom ≫ T.map (Prod.mkHom (s P Q).hom (𝟙 (F.obj N))) ≫
      T.map (Prod.mkHom (T.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N)) ≫
      T.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
      (e (T'.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ Ev.map b'.hom ≫
      (e (K.obj P) (T'.obj (K.obj Q, K.obj N))).hom ≫
      T.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom) ≫
      T.map (Prod.mkHom (θ.hom.app P) (T.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N)))) := by
  dsimp only
  apply scalarExtension_tripleTensor_hom_ext l E W n P Q N
  intro p q r i k hpq hik V x y z
  let g := coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let u := fun (X : scalarReductionSource l E W) (w : X.val.obj V) ↦
    coefficientIntegralScalarUnitSection l E W n X V w
  have hk' : p + (q + r) = k := by omega
  have L1 := coefficientIntegralScalarUnitSection_naturality l E W n (a.hom.f k) V
    (g _ N i r k hik V (g P Q p q i hpq V x y) z)
  have L2 := ha p q r i (q + r) k hpq rfl hik hk' V x y z
  have L3 := coefficientScalarTensorIso_hom_unitSection l E W n P
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N))
    p (q + r) k hk' V
    x (g Q N q r (q + r) rfl V y z)
  have L4 := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P))
    (coefficientScalarTensorIso l E W n Q N).hom
    p (q + r) k hk' V (u _ x) (u _ (g Q N q r (q + r) rfl V y z))
  -- Normalize the generator equations without reducing the whole associativity goal.
  simp only [u, g, coefficientScalarTensorIso_hom_unitSection] at L4
  have R1 := coefficientScalarTensorIso_hom_unitSection l E W n
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))
    N i r k hik V
    (g P Q p q i hpq V x y) z
  have R2 := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    (coefficientScalarTensorIso l E W n P Q).hom
    (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj N))
    i r k hik V (u _ (g P Q p q i hpq V x y)) (u _ z)
  simp only [u, g, coefficientScalarTensorIso_hom_unitSection] at R2
  have hθ (X : CochainComplex (scalarReductionSource l E W) ℤ) (j : ℤ)
      (v : (X.X j).val.obj V) :
      (((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app X).f j).val.app V
        ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app X).f j).val.app V
          (u _ v)) = u _ v :=
    congrArg (fun φ ↦ (φ.f j).val.app V (u _ v))
      ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv_hom_id_app X)
  have R3a := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q) p q i hpq V
    (u _ x) (u _ y)
  have R3b := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P)
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q)))
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N) i r k hik V
    (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ p q i hpq V (u _ x) (u _ y)) (u _ z)
  have R4 := evaluatedAssociator_generator_section l E W n ((M.quotient l E W).obj P)
    ((M.quotient l E W).obj Q) ((M.quotient l E W).obj N)
    b' hb' p q r i (q + r) k hpq rfl hik hk' V
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P).f p).val.app V (u _ x))
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q).f q).val.app V (u _ y))
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N).f r).val.app V (u _ z))
  have R5a := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app N) q r (q + r) rfl V
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q).f q).val.app V (u _ y))
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N).f r).val.app V (u _ z))
  simp only [hθ] at R5a
  have R5b := OrdinaryQuotient.normalizedDVR_tensorGenerator_map l E W n
    ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app N))) p (q + r) k hk' V
    ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P).f p).val.app V (u _ x))
    (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) _ _ q r (q + r) rfl V
      ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app Q).f q).val.app V (u _ y))
      ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N).f r).val.app V (u _ z)))
  simp only [hθ] at R5b
  have c2 := R3b.trans (congrArg (fun v ↦ coefficientTensorGenerator.{u, t + 1, t}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n) _
      (((M.tensor ⋙ coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj N)
      i r k hik V v
      ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app N).f r).val.app V
        (u _ z))) R3a)
  have c4 := R5b.trans (congrArg (fun v ↦ coefficientTensorGenerator.{u, t + 1, t}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
      (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) _
      p (q + r) k hk' V (u _ x) v) R5a)
  have c1 := (congrArg (fun v ↦ ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
      (coefficientScalarTensorIso l E W n P Q).hom
      (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj N)))).f k).val.app
        V v)) R1).trans R2
  have cL1 := L1.trans (congrArg (coefficientIntegralScalarUnitSection l E W n _ V) L2)
  have cL2 := (congrArg (fun v ↦ (((coefficientScalarTensorIso l E W n P
    ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (Q, N))).hom.f k).val.app V v))
    cL1).trans L3
  have cL := (congrArg (fun v ↦ ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom
      (𝟙 (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P))
      (coefficientScalarTensorIso l E W n Q N).hom)).f k).val.app V v)) cL2).trans L4
  let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let T' := coefficientTotalTensor.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let Ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  let K := M.quotient l E W
  let θ := NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)
  let e := coefficientEvaluationTensorIso l E W n
  let m3 := T.map (Prod.mkHom (T.map (Prod.mkHom (θ.inv.app P) (θ.inv.app Q))) (θ.inv.app N))
  let mΞ := T.map (Prod.mkHom (e (K.obj P) (K.obj Q)).inv (𝟙 (Ev.obj (K.obj N)))) ≫
    (e (T'.obj (K.obj P, K.obj Q)) (K.obj N)).inv ≫ Ev.map b'.hom ≫
    (e (K.obj P) (T'.obj (K.obj Q, K.obj N))).hom ≫
    T.map (Prod.mkHom (𝟙 (Ev.obj (K.obj P))) (e (K.obj Q) (K.obj N)).hom)
  let m9 := T.map (Prod.mkHom (θ.hom.app P) (T.map (Prod.mkHom (θ.hom.app Q) (θ.hom.app N))))
  have cR := (congrArg (fun v ↦ (m9.f k).val.app V ((mΞ.f k).val.app V ((m3.f k).val.app V v)))
    c1).trans ((congrArg (fun v ↦ (m9.f k).val.app V ((mΞ.f k).val.app V v)) c2).trans
      ((congrArg (fun v ↦ (m9.f k).val.app V v) R4).trans c4))
  exact cL.trans cR.symm

/-- The ordinary tensor comparison of the quotient system is compatible with the native
total associators: both composites agree after every finite evaluation, where they become
the reassociation of the scalar tensor comparisons.
Source: Stacks 03EK, 07A4, 0941. -/
theorem OrdinaryModel.quotientTensor_associativity (M : OrdinaryModel l E W)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hb : M.TensorEvaluation l E W b) :
    CoefficientComplexTensorAssociativity (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (M.quotient l E W) b := by
  intro P Q N a b' ha hb'
  apply coefficientSequenceComplex_hom_ext
  intro n
  refine evaluated_tensor_associativity
    (A := CochainComplex (scalarReductionSource l E W) ℤ)
    (S := CochainComplex (coefficientSequenceModules l E W) ℤ)
    (L := CochainComplex (normalizedDVRModules l E W n) ℤ)
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W))
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n))
    (M.quotient l E W) ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ))
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)) b
    (coefficientEvaluationTensorIso l E W n) (coefficientScalarTensorIso l E W n)
    ?_ ?_ P Q N a.hom b'.hom ?_
  · intro X X' Y Y' f g
    exact coefficientEvaluationTensorIso_naturality l E W n f g
  · exact fun P Q ↦ hb n P Q
  · exact M.scalarTensorAssociativity l E W n P Q N a ha b' hb'

end OrdinaryQuotient

end WeilConjectures
