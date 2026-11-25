/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

/-! # Independence of the normalized integral coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/--
Any two normalized coefficient presentations induce the same integral map into the
native coefficient sheaf.  This is the finite-quotient uniqueness step in
Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-completed-coefficient-change)

Proof source: compose both maps with every finite quotient projection.  The finite
constant and residue equations force equality on each projection, and the completed
coefficient sheaf is the inverse limit of these quotients, so joint monicity gives
the equality of the original maps.
-/
theorem coefficientPresentation_integralMap_eq
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (T : Scheme.{u})
    (C D : CoefficientPresentation l T E i) :
    C.integralMap l T = D.integralMap l T := by
  have hfinite (n : ℕ) : (C.finite n).hom = (D.finite n).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology T) _ _
      (finiteContinuousCoefficientSheaf l T E n).property
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply @ContinuousMap.ext U.unop.left (finiteCoefficientRing l E n) _ ⊥
    intro x
    exact (C.finite_constants n U a x).trans (D.finite_constants n U a x).symm
  have hintegral : C.integral.hom = D.integral.hom := by
    let H := sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    apply H.map_injective
    apply limit.hom_ext
    intro n
    have h : C.integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n.unop =
        D.integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n.unop := by
      apply (cancel_mono (C.finite n.unop).hom).mp
      rw [Category.assoc, Category.assoc, hfinite]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      apply @ContinuousMap.ext U.unop.left (finiteCoefficientRing l E n.unop) _ ⊥
      intro x
      apply ULift.ext
      have hc := C.integral_residues n.unop U s x
      rw [hfinite] at hc
      exact hc.trans (D.integral_residues n.unop U s x).symm
    exact congrArg H.map h
  have hinv : C.integral.inv = D.integral.inv := by
    apply (cancel_epi C.integral.hom).mp
    rw [Iso.hom_inv_id, hintegral, Iso.hom_inv_id]
  have hinclusion : C.integralInclusion ≫ C.rationalInclusion =
      D.integralInclusion ≫ D.rationalInclusion := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change (C.rationalInclusion.hom.app U (C.integralInclusion.hom.app U s)).down.1 x =
      (D.rationalInclusion.hom.app U (D.integralInclusion.hom.app U s)).down.1 x
    exact (C.rationalInclusion_normalized U _ x).trans
      ((congrArg i ((C.integralInclusion_normalized U.unop s x).trans
        (D.integralInclusion_normalized U.unop s x).symm)).trans
          (D.rationalInclusion_normalized U _ x).symm)
  unfold CoefficientPresentation.integralMap
  rw [hinv, hinclusion]

end WeilConjectures.LocallyFiniteAdicCompactSupport
