/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.SmoothPurity.Integral.IntegralRootPowerLocalGeneration

/-! # Local generation of integral root powers

Source: Stacks, Modules on Sites, Tag 03EK, and coefficient-twist clause 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  MorphismProperty.Over.pullback constantSheaf Padic

/-- Maps out of a root tensor power are determined by the prescribed scalar/root
sections. The generator family G is arbitrary subject to its three recursion equations;
thus this lemma introduces no replacement for the existing generator construction.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/
def-weil-frobenius-coefficient-twists.md, Tate-twist construction;
expanded DAG clause 3; Stacks, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-integral-root-power-generators).
Proof: in degree zero, the generators are all coefficient sections.
In degree one, use the sheafification adjunction for the integral scalar extension.
Tensor generation reduces equality to a scalar tensor a tensor x. Scalar linearity
moves a to the target, leaving the root generator with scalar 1. The completed
integral action restricts to the original discrete O_E action by its defining
normalization, so this reduction also applies to completed-linear arrows.
For degree d+2, the sheaf tensor is the sheafification of the sectionwise tensor
product of degree d+1 and degree one. Locally every section of either factor is a
finite sum of scalar multiples of its root generators. Pass to a common refinement
of the two covers. Bilinearity expresses a pure tensor as a sum of the displayed
nested root tensors, putting the product of the two scalars in its first factor.
The induction hypothesis and the degree-one calculation prove equality there.
Separatedness of the target sheaf descends equality from this cover. This proves
local generation and the asserted extensionality simultaneously, without assuming
that arbitrary sheaf sections globally lift to their tensor presheaf. The induction
includes zero coefficients, zero root groups, and the empty scheme. -/
theorem integralRootPower_hom_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (G : ∀ (d : ℕ) (V : T.ProEtᵒᵖ) (_a : (completedIntegralCoefficientSheafUnrestricted l E
      T).obj.obj V),
      (Fin d → (purTwistZlOne T l).obj.obj V) →
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) d).val.obj V)
    (hzero : ∀ V a x, G 0 V a x = a)
    (hone : ∀ V a x, G 1 V a (fun _ ↦ x) =
      @SMul.smul _ _ (purTwistIntegralAction T l E V).toSMul a
          (purTwistIntegralTensor T l E V 1 x))
    (hsucc : ∀ d V a x, G (d + 2) V a x =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
          (purTwistIntegralModule T l E) (d + 1))
        (purTwistIntegralModule T l E) V (G (d + 1) V a (fun i ↦ x i.castSucc))
        (purTwistIntegralTensor T l E V 1 (x (Fin.last (d + 1)))))
    (d : ℕ) (N : proEtaleRingModules T (completedIntegralCommRingSheafUnrestricted l E T))
    (f g : coefficientTwistPower T (R := (completedIntegralCommRingSheafUnrestricted l E T))
      (purTwistIntegralModule T l E) d ⟶ N)
    (h : ∀ V a x, f.val.app V (G d V a x) = g.val.app V (G d V a x)) :
    f = g := by
  apply integralRootPower_hom_ext_of_locallySpans l E T G
    (integralRootPower_local_spanning l E T G hzero hone hsucc) d N f g h

end WeilConjectures
