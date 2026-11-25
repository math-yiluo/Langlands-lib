/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor
import WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates

/-! # Successor maps of ordinary composite scalar tensors

Source: Stacks 03D7, 03EK and the sequence-site construction preceding 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open CoefficientExtensionAssociation
section ConjugateSections
universe c v r
private theorem conjugate_maps_on_section
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (φ : R ⟶ S) (ψ₀ : T ⟶ R) (ψ₁ : T ⟶ S)
    {A B : SheafOfModules.{r} R} {C₀ D₀ : SheafOfModules.{r} S}
    (e : A ≅ B) (f : C₀ ≅ D₀)
    (τ : A ⟶ (SheafOfModules.restrictScalars φ).obj C₀)
    (σ : (SheafOfModules.restrictScalars ψ₀).obj B ⟶
      (SheafOfModules.restrictScalars ψ₁).obj D₀)
    (U : Cᵒᵖ) (x : B.val.obj U) (y : D₀.val.obj U)
    (ht : HEq (τ.val.app U (e.inv.val.app U x)) (f.inv.val.app U y))
    (hσ : HEq (σ.val.app U x) y) :
    (moduleAbConjugate φ e f τ).hom.app U x =
      (eqToHom (restrict_toSheaf_obj ψ₀ B).symm ≫
        (SheafOfModules.toSheaf T).map σ ≫ eqToHom (restrict_toSheaf_obj ψ₁ D₀)).hom.app U x := by
  have ha := moduleAbConjugate_apply_heq φ e f τ U x
  have hc := restrict_apply_heq φ f.hom U (τ.val.app U (e.inv.val.app U x))
    (f.inv.val.app U y) ht
  have he := congrArg (fun k ↦ k.val.app U y) f.inv_hom_id
  have hb := sheafAb_cast_apply_heq (restrict_toSheaf_obj ψ₀ B)
    (restrict_toSheaf_obj ψ₁ D₀) ((SheafOfModules.toSheaf T).map σ) U x x (HEq.refl _)
  exact eq_of_heq (ha.trans (hc.trans ((heq_of_eq he).trans (hσ.symm.trans hb.symm))))
end ConjugateSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

private theorem tensorTransition_of_generators
    (N : coefficientSequenceModules l L W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ)
    (e : ∀ k : ℕ, (coefficientSequenceEvaluation l L W k).obj N ≅
      (integralScalarReduction l E L ι W k).obj (P.X i))
    (h : ∀ (V : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf l L W (n + 1)).obj.obj V)
      (y : (P.X i).val.obj V),
      HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app N).val.app V
        ((e (n + 1)).inv.val.app V
          (integralScalarTensorSection l E L ι W (n + 1) (P.X i) V s y)))
        ((e n).inv.val.app V (integralScalarTensorSection l E L ι W n (P.X i) V
          ((integralCoefficientSheafTransition l L W n).hom.app V s) y))) :
    ∀ (U : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj N).val.obj U),
      HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app N).val.app U x)
        ((e n).inv.val.app U
          ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
            ((e (n + 1)).hom.val.app U x))) := by
  intro U x
  let K := P.X i
  let τ := (coefficientSequenceTransition l L W (Nat.le_succ n)).app N
  let σ := ((integralScalarTransition l E L ι W n).app P).f i
  let a := moduleAbConjugate (normalizedDVRQuotient l L W (Nat.le_succ n))
    (e (n + 1)) (e n) τ
  let ψ (k : ℕ) := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l L W k)
  have hk (k : ℕ) : (SheafOfModules.toSheaf _).obj
      (((integralScalarLevel l E L ι W k).obj P).X i) =
      (SheafOfModules.toSheaf _).obj ((integralScalarReduction l E L ι W k).obj K) :=
    restrict_toSheaf_obj (ψ k) ((integralScalarReduction l E L ι W k).obj K)
  let b := eqToHom (hk (n + 1)).symm ≫
    (SheafOfModules.toSheaf _).map σ ≫ eqToHom (hk n)
  have hab : a = b := by
    apply scalarTensor_ab_hom_ext l E L ι W (n + 1) K
    intro V s₀ y
    let s : (integralCoefficientSheaf l L W (n + 1)).obj.obj V := s₀
    exact conjugate_maps_on_section
      (normalizedDVRQuotient l L W (Nat.le_succ n)) (ψ (n + 1)) (ψ n)
      (e (n + 1)) (e n) τ σ V
      (integralScalarTensorSection l E L ι W (n + 1) K V s y)
      (integralScalarTensorSection l E L ι W n K V
        ((integralCoefficientSheafTransition l L W n).hom.app V s) y)
      (h V s₀ y)
      (heq_of_eq ((integralScalarTransition_existsUnique l E L ι W n).exists.choose_spec
        P i V s y))
  exact completed_conjugation_section
    (normalizedDVRQuotient l L W (Nat.le_succ n)) (ψ (n + 1)) (ψ n)
    (e (n + 1)) (e n) τ σ hab U x

/-- Scalar extension of an ordinary quotient tensor model has the published
successor transition in the balanced finite tensor coordinates.

Source: Stacks sites-modules.tex, tensor/restriction adjunction (03D7) and
section-tensor-product (03EK); sites-cohomology.tex, section-derived-limits,
the sequence-site construction preceding lemma-derived-limit-is-ok (0941).
This is the tensor calculation in step 1 of
stage3-pur-extension-ordinary-association-chain.
(blueprint: stage3-pur-extension-association-successor).

Proof: write a_n for the displayed composite of rho, scalar extension of the
ordinary quotient evaluation, and balanced association. Transport the source
successor map by a_(n+1) and a_n. Compare the resulting completed-L-linear map
with the published integralScalarTransition. Maps from the sheafified direct
tensor B_(n+1) tensor_R P^i agree if they agree on every local tensor b tensor x:
apply the ordinary tensor/restriction Hom equivalence and sheafification.
The unit equation for rho identifies its inverse on a finite unit tensor with
the finite evaluation of the system scalar-adjunction unit. Naturality of that
system unit with respect to the horizontal sequence-site arrow identifies its
successor with the scalar unit at the lower level applied to the original
quotient successor. The transition clause of M, transported by M.evaluation,
identifies this original successor with coefficientOrdinaryQuotient. Its
normalized quotient-tensor formula reduces the coefficient and keeps x.
The balanced formula hassociation then sends both nested tensors to
red(b) tensor x. The defining tensor formula for integralScalarTransition gives
the same section. Thus the transported maps agree on generators and hence on
all sections. Conjugating by the two a_n gives the displayed HEq. This proof is
termwise and uses no differential, flatness or good-complex condition; zero
terms, n=0, empty sites and ramified extensions are included. -/
theorem coefficientExtensionAssociation_successor
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association) :
    let a (n : ℕ) := Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
      Functor.isoWhiskerRight (M.evaluation n) (A.levels n).model.E ≪≫ association n
    ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
      (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj
        (A.scalar.model.E.obj (M.tensor.obj (P.X i)))).val.obj U),
      HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
          (A.scalar.model.E.obj (M.tensor.obj (P.X i)))).val.app U x)
        (((a n).inv.app (P.X i)).val.app U
          ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
            (((a (n + 1)).hom.app (P.X i)).val.app U x))) := by
  dsimp only
  intro P n i
  exact tensorTransition_of_generators l E L ι W
    (A.scalar.model.E.obj (M.tensor.obj (P.X i))) P n i
    (fun k ↦ (Functor.isoWhiskerLeft M.tensor (ρ k) ≪≫
      Functor.isoWhiskerRight (M.evaluation k) (A.levels k).model.E ≪≫ association k).app (P.X i))
    (fun V s y ↦ associatedTensor_transition l E L ι W A M ρ hρ association hassociation
      (P.X i) n V s y)

end WeilConjectures
