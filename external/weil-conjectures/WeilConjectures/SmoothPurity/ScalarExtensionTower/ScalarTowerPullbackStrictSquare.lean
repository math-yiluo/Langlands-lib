/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionTensorUnit

/-! # Strict scalar/pullback square below the total-limit comparison

Source: Stacks 03EL and 07A4; strict part of
lem-pur-scalar-extension-tower-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

attribute [local irreducible] comparisons scalar_adj
  coefficientTotalTensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf integralComparisonSequenceScalarModel
  integralComparisonSequenceTensorSection integralComparisonSequenceScalarPullback
  CategoryTheory.Functor.leftAdjoint

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Equality of normalized scalar/pullback maps before localization and total limit.
The proof is the homogeneous generator calculation: both routes send a generator
`b ⊗ (x ⊗ y)` to `(b ⊗ x) ⊗ (1 ⊗ y)`, and the equality is retained by every
quotient transition.  This is strictly below the target's realization and limit
statement.
Source: Stacks 03EL and 07A4
(blueprint: stage3-pur-scalar-pullback-strict-square).
Proof: compare homogeneous generators after applying the scalar adjunction
transpose; the scalar and pullback formulas agree and preserve every quotient
transition.
-/
theorem scalarTowerPullbackStrictSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    leftRoute l E L ι f = rightRoute l E L ι f := by
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ((scalar_adj l E L ι X).homEquiv _ _).injective
  apply ((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage.{u, u} l E f)).homEquiv _ _).injective
  apply WeilConjectures.total_tensor_sections_ext l E Y P Q n
  intro p q hpq V x y
  subst n
  rcases V with ⟨m, U⟩
  change (((scalar_adj l E L ι X).homEquiv _ _)
      (((leftRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y)) =
    (((scalar_adj l E L ι X).homEquiv _ _)
      (((rightRoute l E L ι f).hom.app (P, Q)).f (p + q))).val.app
        (op (m, (Scheme.proEtaleBaseChange f).obj U))
        (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))
  rw [scalar_transpose_section, scalar_transpose_section]
  simp only [leftRoute, rightRoute, leftRouteCore, rightRouteCore,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change
    ((((comparisons l).c L f).hom.app
      ((scalar l E L ι Y).obj P, (scalar l E L ι Y).obj Q)).f (p + q)).val.app _
      (((integralComparisonSequencePullback.{u, u} l L f).map
        ((((comparisons l).sigma E L ι Y).hom.app (P, Q)).f (p + q))).val.app _
          (((integralComparisonSequenceScalarPullback.{u, u} l E L ι f).hom.app
            (((tensor l E Y).obj (P, Q)).X (p + q))).val.app _
              (integralComparisonSequenceTensorSection l E L ι X _ _ 1
                (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y))))) =
    (((tensor l L X).map (Prod.mkHom
      ((kappa l E L ι f).hom.app P) ((kappa l E L ι f).hom.app Q))).f (p + q)).val.app _
      (((((comparisons l).sigma E L ι X).hom.app
        ((pull l E f).obj P, (pull l E f).obj Q)).f (p + q)).val.app _
          (((integralComparisonSequenceScalarModel.{u, u} l E L ι X).E.map
            ((((comparisons l).c E f).hom.app (P, Q)).f (p + q))).val.app _
              (integralComparisonSequenceTensorSection l E L ι X _ _ 1
                (pullSection l E f _ m U (generator l E Y P Q p q (op (m, U)) x y)))))
  erw [scalar_pull_section, pull_section_naturality]
  rw [(comparisons l).sigma_formula E L ι Y P Q p q (op (m, U)) 1 x y]
  erw [pull_tensor_section, scalar_section_naturality, pull_tensor_section]
  erw [(comparisons l).sigma_formula]
  erw [WeilConjectures.generator_map]
  erw [scalar_pull_section, scalar_pull_section]
  rfl

end WeilConjectures.ScalarExtensionTower
