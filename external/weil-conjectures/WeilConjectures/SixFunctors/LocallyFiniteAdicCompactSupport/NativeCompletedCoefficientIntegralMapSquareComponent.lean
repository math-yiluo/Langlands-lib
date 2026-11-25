/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement

/-! # Components of the normalized integral presentation pullback square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

section
variable (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (i : E →ₐ[Padic l] PadicAlgCl l)
  [G : NativeGeometry.{u} l]

-- Constant sections determine the comparison at every finite residue level.
private theorem finite_direct_square
    {U V : Scheme.{u}} (g : U ⟶ V)
    (A : CoefficientPresentation l U E i) (B : CoefficientPresentation l V E i)
    (n : ℕ) :
    letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    (B.finite n).hom ≫ continuousCoefficientDirectMap (finiteCoefficientRing l E n) g =
      proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)) ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map (A.finite n).hom := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  have hc (W : V.ProEtᵒᵖ) (a : finiteCoefficientRing l E n) :
      (proEtaleCoefficientDirectImageMap g
        (Padic.coefficientExtensionRing l E (n + 1))).hom.app W
          ((toSheafify (ProEt.topology V)
            ((Functor.const V.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app W a) =
      (toSheafify (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app
          ((proEtaleBaseChange g).op.obj W) a := by
    have h := Equiv.apply_symm_apply
      ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{u + 1}).homEquiv
        ((Functor.const V.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
        ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
          (integralCoefficientCommRingSheaf l E U n)))
      (Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))))
    change _ ≫ (proEtaleCoefficientDirectImageMap g
      (Padic.coefficientExtensionRing l E (n + 1))).hom = _ at h
    exact ConcreteCategory.congr_hom (congr_app h W) a
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology V) _ _
    ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (finiteContinuousCoefficientSheaf l U E n)).property
  apply NatTrans.ext
  funext W
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply ContinuousMap.ext
  intro x
  change finiteContinuousCoefficientValue l E V n W
      ((B.finite n).hom.hom.app W
        ((toSheafify (ProEt.topology V)
          ((Functor.const V.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app W a))
          ((pullback.fst W.unop.hom g).base x) =
    finiteContinuousCoefficientValue l E U n ((proEtaleBaseChange g).op.obj W)
      ((A.finite n).hom.hom.app _
        ((proEtaleCoefficientDirectImageMap g
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app W
            ((toSheafify (ProEt.topology V)
              ((Functor.const V.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app W a))) x
  erw [hc W a]
  exact (B.finite_constants n W a _).trans
    (A.finite_constants n ((proEtaleBaseChange g).op.obj W) a x).symm

@[reassoc] private theorem presentation_reduction (T : Scheme.{u})
    (A : CoefficientPresentation l T E i) (n : ℕ) :
    A.integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n ≫
      (A.finite n).hom = continuousCoefficientReduction l E T n := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  exact A.integral_residues n W s x

-- A typed wrapper keeps the integral presentation visible during categorical rewriting.
private noncomputable def integralDirectMap
    {U V : Scheme.{u}} (g : U ⟶ V) :
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l V E ⟶
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l U E) := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientDirectMap
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g

-- Uniqueness of the completed map transports continuous precomposition through
-- every normalized integral presentation.
private theorem completed_direct_square
    {U V : Scheme.{u}} (g : U ⟶ V)
    (A : CoefficientPresentation l U E i) (B : CoefficientPresentation l V E i) :
    B.integral.inv ≫ integralDirectMap l E g ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map A.integral.hom =
      sfCompletedCoefficientMap l E g := by
  let R := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  apply (sfCompletedCoefficientMap_existsUnique l E g).unique
  · intro n
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    apply (cancel_epi B.integral.hom).mp
    apply (cancel_mono (R.map (A.finite n).hom)).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change (integralDirectMap l E g ≫ R.map A.integral.hom) ≫
        R.map (completedIntegralCommRingProjectionUnrestricted l E U n) ≫
        R.map (A.finite n).hom =
      (B.integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E V n ≫
        proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1))) ≫
        R.map (A.finite n).hom
    rw [Category.assoc, ← R.map_comp_assoc, ← R.map_comp,
      Category.assoc A.integral.hom,
      presentation_reduction l E i U A n]
    erw [Category.assoc, Category.assoc, ← finite_direct_square l E i g A B n]
    erw [presentation_reduction_assoc l E i V B n]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply ContinuousMap.ext
    intro x
    rfl
  · exact (sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec

end

/--
The component at each pro-etale test object of the normalized integral-map square.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. The finite constant and
residue formulas identify the completed direct-image map with continuous integral
precomposition, conjugated by the supplied presentations. Apply the sheaf adjunction
and cancel the integral presentation isomorphism. The integral and rational inclusion
normalizations and the native pullback normalization then identify both maps pointwise.
Taking their components gives the displayed equality of ring homomorphisms.
(blueprint: lem-sf-native-completed-coefficient-integral-map-square-component)
-/
theorem coefficient_presentation_integralMap_pull_square_component
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l)
    (C : ∀ T : Scheme.{u}, CoefficientPresentation l T E i)
    {U V : Scheme.{u}} (g : U ⟶ V) (W : U.ProEtᵒᵖ) :
      (((PurCompactSupport.completed l E).pull g).hom ≫
          (C U).integralMap l U).hom.app W =
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            ((C V).integralMap l V) ≫
          ((nativeCoefficients l).pull g).hom).hom.app W := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  have hs : ((PurCompactSupport.completed l E).pull g).hom ≫
        (C U).integralMap l U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          ((C V).integralMap l V) ≫ ((nativeCoefficients l).pull g).hom := by
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _
      ((adj.homEquiv _ _).symm (sfCompletedCoefficientMap l E g) ≫
        (C U).integralMap l U) = _
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    erw [adj.homEquiv_naturality_left ((C V).integralMap l V)
      (G.pull g).hom]
    rw [← completed_direct_square l E i g (C U) (C V)]
    apply (cancel_epi (C V).integral.hom).mp
    simp only [CoefficientPresentation.integralMap, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_assoc]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext Z
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change ((C U).rationalInclusion.hom.app _
      ((C U).integralInclusion.hom.app _
        ((integralDirectMap l E g).hom.app Z s))).down.1 x =
      ((adj.homEquiv _ _ (G.pull g).hom).hom.app Z
        ((C V).rationalInclusion.hom.app Z
          ((C V).integralInclusion.hom.app Z s))).down.1 x
    erw [G.pull_normalized, (C U).rationalInclusion_normalized,
      (C V).rationalInclusion_normalized]
    erw [(C U).integralInclusion_normalized ((proEtaleBaseChange g).obj Z.unop),
      (C V).integralInclusion_normalized Z.unop]
    rfl
  exact congrArg (fun f ↦ f.hom.app W) hs

end WeilConjectures.LocallyFiniteAdicCompactSupport
