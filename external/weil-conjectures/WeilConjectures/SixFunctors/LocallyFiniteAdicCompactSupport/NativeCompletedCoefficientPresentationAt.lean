/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! # Pointwise normalized completed-to-native coefficient presentations -/

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

private def isoOfOpSequence {C : Type*} [Category C] {F H : ℕᵒᵖ ⥤ C}
    (e : ∀ n : ℕ, F.obj (op n) ≅ H.obj (op n))
    (he : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ H.map (homOfLE (Nat.le_succ n)).op) : F ≅ H :=
  NatIso.ofComponents (fun n ↦ e n.unop)
    (fun f ↦ (NatTrans.ofOpSequence (fun n ↦ (e n).hom) he).naturality f)

-- Compare consecutive residue maps before passing to the inverse limit.
private def completionDiagramIso
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    finiteCoefficientTower l T E ⋙
        sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≅
      integralCoefficientSheafSystem l E T :=
  isoOfOpSequence (fun n ↦ Iso.refl _) (by
    intro n
    change
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (finiteCoefficientRingMap l E (Nat.le_succ n))) ≫ 𝟙 _ =
      𝟙 _ ≫ (integralCoefficientSheafSystem l E T).map
        (homOfLE (Nat.le_succ n)).op
    rw [Category.comp_id, Category.id_comp]
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    unfold integralCoefficientSheafTransition
    congr 2)

private theorem preservesCommRingLimits (T : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
  let H := sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : PreservesLimitsOfShape ℕᵒᵖ (H ⋙ sheafToPresheaf (ProEt.topology T) RingCat) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology T) CommRingCat ⋙
        (Functor.whiskeringRight _ _ _).obj (forget₂ CommRingCat RingCat)))
  exact preservesLimitsOfShape_of_reflects_of_preserves H
    (sheafToPresheaf (ProEt.topology T) RingCat)

private def completionIso
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    finiteCoefficientLimit l T E ≅ completedIntegralCommRingSheafUnrestricted l E T := by
  let H := sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have := preservesCommRingLimits T
  exact H.preimageIso (preservesLimitIso H (finiteCoefficientTower l T E) ≪≫
    HasLimit.isoOfNatIso (completionDiagramIso l E T))

-- This identity transports the existing pointwise residue normalization.
private theorem completionIso_projection
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (completionIso l E T).hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      limit.π (finiteCoefficientTower l T E) (op n) := by
  let H := sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have := preservesCommRingLimits T
  apply H.map_injective
  let e : H.obj (finiteCoefficientLimit l T E) ≅
      H.obj (completedIntegralCommRingSheafUnrestricted l E T) :=
    preservesLimitIso H (finiteCoefficientTower l T E) ≪≫
      HasLimit.isoOfNatIso (completionDiagramIso l E T)
  rw [Functor.map_comp]
  change H.map (H.preimage e.hom) ≫
      limit.π (integralCoefficientSheafSystem l E T) (op n) =
    H.map (limit.π (finiteCoefficientTower l T E) (op n))
  rw [Functor.map_preimage]
  change (preservesLimitIso H (finiteCoefficientTower l T E) ≪≫
      HasLimit.isoOfNatIso (completionDiagramIso l E T)).hom ≫
      limit.π (integralCoefficientSheafSystem l E T) (op n) = _
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  change (preservesLimitIso H (finiteCoefficientTower l T E)).hom ≫
      limit.π (finiteCoefficientTower l T E ⋙ H) (op n) ≫ 𝟙 _ = _
  rw [Category.comp_id, preservesLimitIso_hom_π]

private theorem embedding_continuous
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) :
    letI := coefficientExtensionNormedField l E
    Continuous i := by
  let := coefficientExtensionNormedField l E
  let : NormedAlgebra (Padic l) E :=
    { norm_smul_le := fun a x ↦ by
        change spectralNorm (Padic l) E (a • x) ≤ ‖a‖ * spectralNorm (Padic l) E x
        exact le_of_eq (spectralNorm_smul a (Algebra.IsAlgebraic.isAlgebraic x)) }
  exact i.toLinearMap.continuous_of_finiteDimensional

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.Functor.LaxMonoidal
open scoped TensorProduct

-- The monoidal comparisons recover pointwise operations after forgetting modules.
private theorem native_mul [G : NativeGeometry.{u} l] (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a b : (ringSheaf l T).obj.obj U) : (a * b).down = a.down * b.down := by
  change (((«μ» (sheafToPresheaf (ProEt.topology T) AddCommGrpCat) _ _ ≫
    (sheafToPresheaf (ProEt.topology T) AddCommGrpCat).map
      («μ» (ProEtale.weilCoefficientsForgetAb l T) _ _ ≫
        (ProEtale.weilCoefficientsForgetAb l T).map μ[ProEtale.adicConstantSheaf l T])).app
          U).hom (a ⊗ₜ[ℤ] b)).down = _
  rw [Functor.map_comp, ← Category.assoc,
    Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose]
  change (((«μ» ((Functor.whiskeringRight T.ProEtᵒᵖ (WeilCoefficients l)
      AddCommGrpCat).obj (forget₂ (WeilCoefficients l) Ab)) _ _ ≫
    ((Functor.whiskeringRight T.ProEtᵒᵖ (WeilCoefficients l) AddCommGrpCat).obj
      (forget₂ (WeilCoefficients l) Ab)).map
      («μ» (sheafToPresheaf (ProEt.topology T) (WeilCoefficients l)) _ _ ≫
        (sheafToPresheaf (ProEt.topology T) (WeilCoefficients l)).map
          μ[ProEtale.adicConstantSheaf l T])).app U).hom (a ⊗ₜ[ℤ] b)).down = _
  rw [Sheaf.μ_comp_map_mul]
  rfl

private theorem native_one [G : NativeGeometry.{u} l] (T : Scheme.{u}) (U : T.ProEtᵒᵖ) :
    (1 : (ringSheaf l T).obj.obj U).down = 1 := by
  change (((ε (sheafToPresheaf (ProEt.topology T) AddCommGrpCat) ≫
    (sheafToPresheaf (ProEt.topology T) AddCommGrpCat).map
      (ε (ProEtale.weilCoefficientsForgetAb l T) ≫
        (ProEtale.weilCoefficientsForgetAb l T).map η[ProEtale.adicConstantSheaf l T])).app
          U).hom (ULift.up 1)).down = _
  rw [Functor.map_comp, ← Category.assoc,
    Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose]
  change (((ε ((Functor.whiskeringRight T.ProEtᵒᵖ (WeilCoefficients l)
      AddCommGrpCat).obj (forget₂ (WeilCoefficients l) Ab)) ≫
    ((Functor.whiskeringRight T.ProEtᵒᵖ (WeilCoefficients l) AddCommGrpCat).obj
      (forget₂ (WeilCoefficients l) Ab)).map
      (ε (sheafToPresheaf (ProEt.topology T) (WeilCoefficients l)) ≫
        (sheafToPresheaf (ProEt.topology T) (WeilCoefficients l)).map
          η[ProEtale.adicConstantSheaf l T])).app U).hom (ULift.up 1)).down = _
  rw [Sheaf.ε_comp_map_one]
  change algebraMap (PadicAlgCl l) (PadicAlgCl.locallyFiniteFunctions l U.unop.left)
    ((1 : ℤ) • 1) = 1
  simp

private def nativeInclusion [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (T : Scheme.{u}) :
    rationalCoefficientSheaf l T E ⟶ ringSheaf l T := by
  letI := coefficientExtensionNormedField l E
  let f (U : T.ProEtᵒᵖ) (s : C(U.unop.left, ULift.{u + 1} E)) :
      PadicAlgCl.locallyFiniteFunctions l U.unop.left :=
    ⟨⟨fun x ↦ i (s x).down,
      (embedding_continuous l E i).comp (continuous_uliftDown.comp s.continuous)⟩,
      PadicAlgCl.mem_locallyFiniteFunctions_of_finiteDimensional
        (Submodule.finiteDimensional_of_le (S₂ := LinearMap.range i.toLinearMap)
          (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact ⟨(s x).down, rfl⟩)))⟩
  exact ⟨{
    app := fun U ↦ CommRingCat.ofHom
      (R := (rationalCoefficientSheaf l T E).obj.obj U)
      (S := (ringSheaf l T).obj.obj U)
      { toFun := fun s ↦ ULift.up (f U s)
        map_one' := by
          apply ULift.ext
          rw [native_one l T U]
          apply Subtype.ext
          apply ContinuousMap.ext
          intro x
          exact i.map_one
        map_mul' := by
          intro s t
          apply ULift.ext
          refine Eq.trans ?_
            (native_mul l T U (ULift.up (f U s)) (ULift.up (f U t))).symm
          apply Subtype.ext
          apply ContinuousMap.ext
          intro x
          exact i.map_mul _ _
        map_zero' := by
          apply ULift.ext
          apply Subtype.ext
          apply ContinuousMap.ext
          intro x
          exact i.map_zero
        map_add' := by
          intro s t
          apply ULift.ext
          apply Subtype.ext
          apply ContinuousMap.ext
          intro x
          exact i.map_add _ _ }
    naturality := by
      intro U V g
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      rfl }⟩

/--
For one scheme, the finite quotient realization of completed coefficients admits a
normalized coefficient presentation in the native locally finite coefficient ring.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. Construct the inverse-limit
identification from the finite quotient realizations, then use the finite constant and
residue equations to normalize the localization and rational inclusion.
(blueprint: lem-sf-native-completed-coefficient-presentation-at)
-/
theorem exists_native_completed_coefficient_presentation_at
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (T : Scheme.{u}) :
    Nonempty (CoefficientPresentation l T E i) := by
  classical
  obtain ⟨a, ha⟩ := continuousCoefficientCompletion l E T
  choose q hq using ha
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E T
  refine ⟨{
    integral := a ≪≫ completionIso l E T
    finite := q
    finite_constants := fun n U c x ↦ (hq n).1 U c x
    integral_residues := ?_
    localization := b
    localization_normalized := hb
    integralInclusion := integralRationalCoefficientMap l E T
    integralInclusion_normalized := integralRationalCoefficientMap_normalized l E T
    rationalInclusion := nativeInclusion l E i T
    rationalInclusion_normalized := fun U s x ↦ rfl }⟩
  intro n U s x
  have he : (a ≪≫ completionIso l E T).hom ≫
      completedIntegralCommRingProjectionUnrestricted l E T n ≫ (q n).hom =
      a.hom ≫ limit.π (finiteCoefficientTower l T E) (op n) ≫ (q n).hom := by
    simp only [Iso.trans_hom, Category.assoc]
    exact congrArg (fun z ↦ a.hom ≫ z ≫ (q n).hom)
      (completionIso_projection l E T n)
  rw [he]
  exact (hq n).2 U s x

end WeilConjectures.LocallyFiniteAdicCompactSupport
