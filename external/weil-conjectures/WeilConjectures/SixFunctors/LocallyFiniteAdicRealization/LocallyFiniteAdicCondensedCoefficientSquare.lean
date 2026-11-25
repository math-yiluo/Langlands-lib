/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedStageData
public import WeilConjectures.SixFunctors.AdicFiniteRealization.LocallyFiniteAdicFiniteCondensedRealization
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedNativeLeg
import WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison

/-! # The completed integral coefficient square

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-condensed-integral-coefficient-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [IsCommMonObj (abRing l X)]

private theorem finiteValues_injective (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Injective (fun s : (finiteContinuousCoefficientSheaf l X F n).obj.obj U ↦
      fun x ↦ finiteContinuousCoefficientValue l F X n U s x) := by
  intro s t h
  letI : TopologicalSpace (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⊥
  letI : DiscreteTopology (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⟨rfl⟩
  apply ContinuousMap.ext
  intro x
  exact congrFun h x

private theorem finiteCoefficientSquare (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (i : F →ₐ[ℚ_[l]] PadicAlgCl l)
    (A : RationalModuleRealization l F X) (C : CoefficientPresentation l X F i)
    (n : ℕ) :
    (WeilConjectures.IntegralCoefficientPresentation.level l F X
      (integralCoefficientULift l F) n).hom ≫
      (C.finite n).hom = (A.finiteIso n).hom := by
  let d := pbcIntegralDatum l F
  let c : (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n + 1)))) ⟶
      finiteContinuousCoefficientSheaf l X F n := (C.finite n).hom
  apply (cancel_epi (pbcLevelConstantComparison X d n).hom).mp
  change (pbcLevelConstantComparison X d n).hom ≫
      ((pbcLevelConstantComparison X d n).inv ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (integralCoefficientULift l F n).toCommRingCatIso.hom) ≫ c = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l X F n).property
  let c' : sheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n + 1))))) ⟶
      (finiteContinuousCoefficientSheaf l X F n).obj := c.hom
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ c') = _
  rw [← Category.assoc, ← toSheafify_naturality]
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  letI : TopologicalSpace (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⊥
  letI : DiscreteTopology (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n) := ⟨rfl⟩
  apply finiteValues_injective l X F n U
  funext x
  have hu := ConcreteCategory.congr_hom
    (congr_app (rationalFiniteScalars_constantUnit d X n) U) a
  change (pbcFunctionScalars X d n).app U a =
    (pbcLevelConstantComparison X d n).hom.hom.app U
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (PbcIntegralRing l F ⧸ d.ideal ^ (n + 1))))).app U a) at hu
  change finiteContinuousCoefficientValue l F X n U
      ((C.finite n).hom.hom.app U ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (AlgebraicGeometry.Scheme.finiteCoefficientRing l F n))).app U
            (integralCoefficientULift l F n a))) x = _
  erw [C.finite_constants]
  exact (A.finite_normalization n U a x).symm.trans
    (congrArg (fun y ↦ finiteContinuousCoefficientValue l F X n U
      ((A.finiteIso n).hom.hom.app U y) x) hu)

private theorem integralCoefficientSquare (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (i : F →ₐ[ℚ_[l]] PadicAlgCl l)
    (A : RationalModuleRealization l F X) (C : CoefficientPresentation l X F i) :
    (purCoefficientIso l F X).hom =
      A.integralIso.hom ≫ C.integral.hom := by
  have hπ (n : ℕ) : (purCoefficientIso l F X).hom ≫
      completedIntegralCommRingProjectionUnrestricted l F X n =
    pbcAdicProjection X (pbcIntegralDatum l F) n ≫
      (WeilConjectures.IntegralCoefficientPresentation.level l F X
        (integralCoefficientULift l F) n).hom := by
    apply (adicLisseForget X).map_injective
    simp only [Functor.map_comp]
    have h := congrArg Iso.hom (purCoefficientIso_existsUnique l F X).exists.choose_spec
    change (adicLisseForget X).map (purCoefficientIso l F X).hom = _ at h
    rw [h]
    exact (integralDetailedCoefficientComparison_exists X l F).exists.choose_spec n
  apply (cancel_epi A.integralIso.inv).mp
  apply (adicLisseForget X).map_injective
  apply limit.hom_ext
  intro n
  change (adicLisseForget X).map
      (A.integralIso.inv ≫ (purCoefficientIso l F X).hom) ≫
      (adicLisseForget X).map (completedIntegralCommRingProjectionUnrestricted l F X n.unop) =
    (adicLisseForget X).map
      (A.integralIso.inv ≫
        (A.integralIso.hom ≫ C.integral.hom)) ≫
      (adicLisseForget X).map (completedIntegralCommRingProjectionUnrestricted l F X n.unop)
  simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  apply (adicLisseForget X).congr_map
  rw [hπ]
  apply (cancel_mono (C.finite n.unop).hom).mp
  rw [Category.assoc, Category.assoc, finiteCoefficientSquare l X F i A C n.unop]
  letI : TopologicalSpace
      (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n.unop + 1))) := ⊥
  letI : DiscreteTopology
      (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n.unop + 1))) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  letI : TopologicalSpace
      (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n.unop + 1))) := ⊥
  letI : DiscreteTopology
      (ULift.{u + 1} (Padic.coefficientExtensionRing l F (n.unop + 1))) := ⟨rfl⟩
  apply finiteValues_injective l X F n.unop U
  funext x
  apply ULift.ext
  exact (A.integral_normalization n.unop U s x).trans
    (C.integral_residues n.unop U s x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The two maps out of the raw completed coefficient ring agree before passing to
module categories. This is a statement only about coefficient ring sheaves.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-condensed-integral-coefficient-square).

Proof in words: first compare the finite quotient identifications. Both the raw
integral identity and the continuous realization fix every constant section, so their
maps from the constant finite coefficient sheaf agree by sheafification. Compose with
every inverse-limit projection. The integral residue equations for the continuous
realization and C identify both projections with the same residue of a continuous
integral function. Joint monicity of the limit projections identifies the completed
maps. The two integral-to-rational inclusions agree pointwise by their normalizations.
Finally the finiteIso normalization identifies each finite-field function under the
fixed Shrink equivalence. The closure leg normalization, globalCoefficientIso_fac and
the native comparison send that function to its actual embedding in PadicAlgCl;
C.rationalInclusion_normalized specifies precisely this embedding. These identities
compose to the asserted equality. Empty site objects have the same unique maps.
-/
theorem finiteCondensedIntegralCoefficientSquare (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l))
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)) :
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X).hom ≫ C.integralMap l X =
      ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion) ≫
        (A.closure.leg E) ≫
          ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)  := by
  have hi : C.integralInclusion = (A.realization E).inclusion := by
    letI := coefficientExtensionNormedField l (Coefficient.{u} l (PadicAlgCl l) E)
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact (C.integralInclusion_normalized U.unop s x).trans
      ((A.realization E).inclusion_normalization U.unop s x).symm
  unfold CoefficientPresentation.integralMap
  erw [integralCoefficientSquare l X _ _ (A.realization E) C]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [hi, finiteCondensedNativeLeg l X A E C]

end WeilConjectures.LocallyFiniteAdicRealization
