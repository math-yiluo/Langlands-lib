/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import WeilConjectures.SmoothPurity.IntegralSystemRealization.OrdinarySystemPullbackCompositorEvaluation
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Finite evaluation of the specified system pullback compositor

Source: Stacks 03D8, 0D6D, 0941; the last pullback identification in the
finite-evaluation step of lem-pur-system-level-projection-formula-coherence.
(blueprint: lem-pur-system-pullback-compositor-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  HasDerivedCategory.standard

attribute [local implicit_reducible] coefficientSequenceHasDerived coefficientFiniteHasDerived
  integralTowerHasDerivedCategory scalarReductionSourceDerived scalarReductionTargetDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf pullbackTensorSequenceDerived

private local instance additiveOfLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [Limits.PreservesFiniteLimits F] : F.Additive :=
  Functor.additive_of_preserves_binary_products F

private local instance finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Limits.PreservesFiniteLimits
      (show normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n from
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f) :=
  sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f

private local instance finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Limits.PreservesFiniteColimits
      (show normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n from
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f) :=
  sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f

attribute [local irreducible] pullbackTensorSequenceInverse
  pullbackTensorSequenceInverseEvaluation pullbackTensorLevelIntrinsic

private def ordinaryEvaluation {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    pullbackTensorSequenceInverse l E j ⋙ coefficientSequenceEvaluation l E U n ≅
      coefficientSequenceEvaluation l E X n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) j :=
  (pullbackTensorSequenceInverseEvaluation l E j n).symm ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n)
      (pullbackTensorLevelIntrinsic l E j n)

private theorem ordinaryEvaluation_complex {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (P : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    (NatTrans.mapHomologicalComplex (ordinaryEvaluation l E j n).hom (.up ℤ)).app P =
      (pullbackTensorInverseEvaluationComplex l E j n).inv.app P ≫
        (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E j n) (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp [ordinaryEvaluation, pullbackTensorInverseEvaluationComplex]

private theorem derivedEvaluation_eq {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    Functor.mapDerivedCategorySquareIso
      (B' := normalizedDVRModules l E X n) (E := normalizedDVRModules l E U n)
      (ordinaryEvaluation l E j n) =
      pullbackTensorDerivedEvaluation l E j n := by
  apply (pullbackTensorDerivedEvaluation_existsUnique l E j n).unique
  · intro P
    have h := Functor.exactSquare_fac
      (E := normalizedDVRModules l E X n) (F := normalizedDVRModules l E U n)
      (ordinaryEvaluation l E j n) P
    rw [ordinaryEvaluation_complex l E j n P, DerivedCategory.Q.map_comp] at h
    exact h
  · exact (pullbackTensorDerivedEvaluation_existsUnique l E j n).exists.choose_spec

private theorem localized_compositor (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    c.pullComp f g =
      Functor.mapDerivedCategoryNatIso (c.ordinaryPull f g) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (pullbackTensorSequenceInverse l E g) (pullbackTensorSequenceInverse l E f)).symm := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E Z) (.up ℤ))
  intro P
  apply (cancel_mono ((pull l E f).map
    ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app P) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
      (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj P))).1
  have hf := Functor.mapDerivedCategoryCompIso_hom_app_factors
    (pullbackTensorSequenceInverse l E g) (pullbackTensorSequenceInverse l E f) P
  have hn := Functor.mapDerivedCategoryNatIso_fac (c.ordinaryPull f g) P
  have hc := congrArg (fun t ↦
    (Functor.mapDerivedCategoryNatIso (c.ordinaryPull f g)).hom.app
      (DerivedCategory.Q.obj P) ≫ t) hf.symm
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, pull,
    pullbackTensorSequenceDerived] using
    (c.pullComp_model f g P).trans (hn.symm.trans hc)

private theorem reverse_square {C : Type*} [Category C] {A B D T : C}
    (e : A ≅ B) (d : D ≅ T) (a : A ⟶ D) (b : B ⟶ T)
    (h : e.hom ≫ b = a ≫ d.hom) : e.inv ≫ a = b ≫ d.inv := by
  have h' := congrArg (fun t ↦ e.inv ≫ t ≫ d.inv) h
  simpa only [Category.assoc, e.inv_hom_id_assoc, d.hom_inv_id,
    Category.comp_id] using h'.symm

/-- Evaluation respects the inverse of the specified section-normalized pullback
compositor, on every strict system. This concerns only inverse image: no compact
support, tensor product, projection map, or boundedness hypothesis occurs.
Source: Stacks 03D8, 0D6D, 0941; ordinaryCompositionEvaluation and the cochain
normalizations of Compositors.pullComp and pullbackTensorDerivedEvaluation.
(blueprint: lem-pur-system-pullback-compositor-evaluation).
Proof: first identify c.ordinaryDirect with the canonical section compositor:
c.sections gives equality on every generalized section at (n,U), hence equality
of module-sheaf maps and of natural transformations. The conjugate equation
c.conjugate then identifies c.ordinaryPull with the canonical inverse-image
compositor, since the adjunction conjugacy equivalence is injective. Apply
ordinaryCompositionEvaluation at level n. Transport the finite level functors
through pullbackTensorLevelIntrinsic, whose inverse-image comparison is fixed by
the same ordinary adjunction units. This gives the ordinary square with the
intrinsic finite compositor. Apply the exact cochain functors and localize.
Compositors.pullComp_model and the unique cochain normalization of
pullbackTensorDerivedEvaluation identify the two derived sides on Q(P).
Every derived object is isomorphic to Q(P); naturality transports the equality
along that isomorphism. Finally invert the three comparison isomorphisms to
obtain the displayed inverse-compositor orientation. Identity morphisms and
zero systems give the usual unit identifications; n=0 is exponent one. -/
theorem systemPullbackCompositorEvaluation
    (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (N : System l E Z) :
    (coefficientSequenceDerivedEvaluation l E X n).map ((c.pullComp f g).inv.app N) ≫
      (pullbackTensorDerivedEvaluation l E (f ≫ g) n).hom.app N =
    (pullbackTensorDerivedEvaluation l E f n).hom.app ((pull l E g).obj N) ≫
      (finiteDerivedPullback l E n f).map
        ((pullbackTensorDerivedEvaluation l E g n).hom.app N) ≫
      (sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
        f g).inv.app ((coefficientSequenceDerivedEvaluation l E Z n).obj N) := by
  let := coefficientSequenceEvaluation_additiveInstance l E Z n
  let := coefficientSequenceEvaluation_additiveInstance l E Y n
  let := coefficientSequenceEvaluation_additiveInstance l E X n
  have h := Functor.exactSquare_comp_forward
    (C₀ := coefficientSequenceModules l E Z) (C₁ := coefficientSequenceModules l E Y)
    (C₂ := coefficientSequenceModules l E X) (D₀ := normalizedDVRModules l E Z n)
    (D₁ := normalizedDVRModules l E Y n) (D₂ := normalizedDVRModules l E X n)
    (pullbackTensorSequenceInverse l E g) (pullbackTensorSequenceInverse l E f)
    (pullbackTensorSequenceInverse l E (f ≫ g))
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g)
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) (f ≫ g))
    (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
    (coefficientSequenceEvaluation l E X n)
    (ordinaryEvaluation l E g n) (ordinaryEvaluation l E f n)
    (ordinaryEvaluation l E (f ≫ g) n) (c.ordinaryPull f g)
    (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) f g)
    (ordinarySystemPullbackCompositorEvaluation l E o c f g n) N
  rw [← localized_compositor l E o c f g,
    derivedEvaluation_eq l E g n, derivedEvaluation_eq l E f n,
    derivedEvaluation_eq l E (f ≫ g) n] at h
  simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using reverse_square
    ((coefficientSequenceDerivedEvaluation l E X n).mapIso ((c.pullComp f g).app N))
    ((sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
      f g).app ((coefficientSequenceDerivedEvaluation l E Z n).obj N))
    ((pullbackTensorDerivedEvaluation l E (f ≫ g) n).hom.app N)
    ((pullbackTensorDerivedEvaluation l E f n).hom.app ((pull l E g).obj N) ≫
      (finiteDerivedPullback l E n f).map
        ((pullbackTensorDerivedEvaluation l E g n).hom.app N)) h

end WeilConjectures.IntegralSystemRealization
