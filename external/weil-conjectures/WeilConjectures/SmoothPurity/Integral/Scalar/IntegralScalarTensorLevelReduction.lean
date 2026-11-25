/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Consecutive reduction for integral scalar tensor comparisons

Source: Stacks 03EL and 07A4; Bhatt--Scholze, Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  coefficientTotalTensor unrestrictedIntegralReductionExistence
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem projection_surjective (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (U : W.ProEtᵒᵖ) : Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U) := by
  intro s
  obtain ⟨a, ha⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n U s
  refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app U a, ?_⟩
  have h : integralConstantToCompletionOfUniverses l E W ≫
      limit.π (integralCoefficientSheafSystem l E W) (op n) =
        integralConstantQuotientOfUniverses l E W n := by
    exact limit.lift_π (integralConstantConeOfUniverses l E W) (op n)
  exact (congrArg (fun f ↦ f.hom.app U a) h).trans ha

private theorem reduction_tensor_lift (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (r : (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
    (x : M.val.obj U) :
    unrestrictedIntegralTensorSection l E W n M U
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U r) x =
      unrestrictedIntegralTensorSection l E W n M U 1 (r • x) := by
  let : Module ((completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
      ((integralCoefficientCommRingSheaf l E W n).obj.obj U) :=
    Module.compHom _ ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
  unfold unrestrictedIntegralTensorSection
  congr 2
  change _ ⊗ₜ[_, _] x =
    (1 : (integralCoefficientCommRingSheaf l E W n).obj.obj U) ⊗ₜ[_, _] (r • x)
  rw [TensorProduct.tmul_smul]
  congr 1
  change _ = ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U r) * 1
  exact (mul_one _).symm

private theorem finite_tensor_ext (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ)
    (H : integralTowerModules l E W)
    (f g : (((integralOperationsTensorLevel l E W n).obj (P, Q)).X k) ⟶ H)
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (eqToHom (congrArg
          (fun j ↦ (((integralOperationsTensorLevel l E W n).obj (P, Q)).X j)) hpq)
        |>.val.app U (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n _ U 1 x)
          (unrestrictedIntegralTensorSection l E W n _ U 1 y))) =
      g.val.app U (eqToHom (congrArg
          (fun j ↦ (((integralOperationsTensorLevel l E W n).obj (P, Q)).X j)) hpq)
        |>.val.app U (integralOperationsTotalTensorSection l E W n P Q p q U
          (unrestrictedIntegralTensorSection l E W n _ U 1 x)
          (unrestrictedIntegralTensorSection l E W n _ U 1 y)))) : f = g := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨b, hb⟩ := finiteTensorComparison.{u, u} l E W n
  let U := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
  let e := U.mapIso ((HomologicalComplex.eval _ (.up ℤ) k).mapIso (b.app (P, Q)))
  apply (cancel_epi e.hom).mp
  let F := unrestrictedIntegralReductionFunctor l E W n
  let := extension_preserves_small_colimits.{u + 1, u, u}
    (completedIntegralCommRingProjectionUnrestricted l E W n) F
    (unrestrictedReduction_obj l E W n) (fun a ↦ unrestrictedReduction_map l E W n a)
  apply total_extension_hom_ext.{u + 1, u, u}
    (completedIntegralCommRingProjectionUnrestricted l E W n) F
    (unrestrictedReduction_obj l E W n) (fun a ↦ unrestrictedReduction_map l E W n a) P Q k
  intro p q hpq V s x y
  subst k
  obtain ⟨r, rfl⟩ := projection_surjective l E W n V s
  change f.val.app V (((b.hom.app (P, Q)).f (p + q)).val.app V
      (unrestrictedIntegralTensorSection l E W n _ V
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V r)
        (coefficientTensorGenerator _ _ P Q p q (p + q) rfl V x y))) =
    g.val.app V (((b.hom.app (P, Q)).f (p + q)).val.app V
      (unrestrictedIntegralTensorSection l E W n _ V
        ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app V r)
        (coefficientTensorGenerator _ _ P Q p q (p + q) rfl V x y)))
  rw [reduction_tensor_lift]
  erw [← tensorGenerator_smul_left.{u + 1, u, u}
    (R := completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V r x y]
  rw [hb]
  exact h p q rfl V (r • x) y

/-- Normalized scalar tensor level maps commute with a single quotient reduction.
Source: Stacks, Modules on Sites, Tag 03EL, tensor products; Cohomology on Sites,
Tag 07A4; Bhatt--Scholze, Definition 3.4.10.
(blueprint: lem-pur-integral-scalar-tensor-level-reduction).
Proof: precompose in each total degree with the scalar extensions of all tensor
summand injections. Use the scalar-extension adjunction, the sheafification unit,
and the balanced tensor universal property to reduce equality to
1 tensor ((1 tensor x) tensor (1 tensor y)). The assumed normalization describes
both level maps on these generators. The recorded quotient transition carries
1 tensor x to 1 tensor x at the next quotient, and the tensor transition reduces
both entries. Naturality of ordinary scalar extension on tensor sections therefore
makes both composites equal to
(1 tensor (1 tensor x)) tensor (1 tensor (1 tensor y)) at level n.
Completed-ring linearity extends this equality to scalar multiples: the projection
onto the finite quotient is locally surjective, so finite coefficients can be lifted
locally. Additivity, tensor generation, and separatedness of the target sheaf prove
equality of the summand maps. Coproduct, chain-map, and natural-transformation
extensionality give the asserted consecutive square. This argument needs no
flatness, and includes zero inputs and the empty site.
Lean proof: test the two composites on scalar-extended total tensor generators.
Naturality of the scalar unit and the prescribed transition and normalization formulas
identify their values. The adjunction, local tensor generation and coproduct
extensionality give the equality of natural transformations. -/
theorem integralScalarTensorLevelReduction (W : AlgebraicGeometry.Scheme.{u})
    (α : ∀ n : ℕ, integralOperationsTensorLevel l E W n ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          integralOperationsTensorLevel l L W n)
    (hα : ∀ (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((α n).app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U 1
            (integralOperationsTotalTensorSection l E W n P Q p q U
              (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
              (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
        integralOperationsTotalTensorSection l L W n
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q U
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (P.X p)) U 1
            (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x))
          (unrestrictedIntegralTensorSection l L W n
            ((integralOrdinaryScalar l E L ι W).obj (Q.X q)) U 1
            (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y))) (n : ℕ) :
    Functor.whiskerRight (integralOperationsTensorTransition l E W n)
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ≫
      α n =
    α (n + 1) ≫ Functor.whiskerLeft
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)))
      (integralOperationsTensorTransition l L W n) := by
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E L ι W).homEquiv _ _).injective
  apply finite_tensor_ext l E W (n + 1) P Q k
  intro p q hpq U x y
  subst k
  change (((α n).app (P, Q)).f (p + q)).val.app U
      (((integralOrdinaryScalar l E L ι W).map
        (((integralOperationsTensorTransition l E W n).app (P, Q)).f (p + q))).val.app U
          (((scalarAdjunction l E L ι W).unit.app _).val.app U
            (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U
              (unrestrictedIntegralTensorSection l E W (n + 1) _ U 1 x)
              (unrestrictedIntegralTensorSection l E W (n + 1) _ U 1 y)))) =
    (((integralOperationsTensorTransition l L W n).app
      ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))).f
          (p + q)).val.app U
      ((((α (n + 1)).app (P, Q)).f (p + q)).val.app U
        (((scalarAdjunction l E L ι W).unit.app _).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U
            (unrestrictedIntegralTensorSection l E W (n + 1) _ U 1 x)
            (unrestrictedIntegralTensorSection l E W (n + 1) _ U 1 y))))
  simp only [scalarAdjunction_unit]
  rw [scalar_map_tensor,
    tensor_transition_apply, reduction_transition_apply, reduction_transition_apply]
  simp only [map_one]
  rw [hα, hα, tensor_transition_apply]
  erw [reduction_transition_apply, reduction_transition_apply]
  simp only [map_one]
  rfl

end WeilConjectures
