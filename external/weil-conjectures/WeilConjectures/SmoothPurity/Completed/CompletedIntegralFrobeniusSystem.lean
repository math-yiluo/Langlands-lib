/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FrobeniusChangeOfRings
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.RingTheory.FrobeniusForm

/-! # A Frobenius system for the completed coefficient extension

The completed coefficient map `𝒪_E^∧ ⟶ 𝒪_F^∧` admits a Frobenius system: base change of an
integral basis of `𝒪_F` over `𝒪_E` and of a Frobenius form `𝒪_F → 𝒪_E`
(`Module.exists_bijective_comp_mulLeft`) along the constant sections of the completed
coefficient sheaves. Hence restriction of scalars along it is left adjoint to ordinary
extension of scalars.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
universe uC vC r u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  {A B : Type (max uC vC r)} [CommRing A] [CommRing B] [Algebra A B]

/-- The constant sections of adic completions are compatible with the completed scalar map. -/
private theorem adicBasisCompletedUnit_scalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) :
    letI := adicBasisRingSheafify.{uC, vC, r} J
    adicBasisFromConstant.{uC, vC, r} J t ≫ f =
      (constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom (algebraMap A B)) ≫
        adicBasisFromConstant.{uC, vC, r} J v := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  apply limit.hom_ext
  intro n
  rw [Category.assoc, Category.assoc]
  change _ ≫ (f ≫ adicBasisProjection.{uC, vC, r} J B v n.unop) =
    _ ≫ adicBasisFromConstant.{uC, vC, r} J v ≫ adicBasisProjection.{uC, vC, r} J B v n.unop
  rw [hf, adicBasisFromConstant_projection, ← Category.assoc,
    adicBasisFromConstant_projection]
  dsimp only [adicBasisScalar]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The completed scalar map sends the constant section of `x` to the constant section of its
image. -/
private theorem adicBasisCompletedUnit_apply_scalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) (U : Cᵒᵖ) (x : A) :
    f.hom.app U ((adicBasisCompletedUnit.{uC, vC, r} J t).app U x) =
      (adicBasisCompletedUnit.{uC, vC, r} J v).app U (algebraMap A B x) := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  let P := (Functor.const Cᵒᵖ).obj (RingCat.of.{max uC vC r} A)
  let Q := (Functor.const Cᵒᵖ).obj (RingCat.of.{max uC vC r} B)
  let η : P ⟶ Q := (Functor.const Cᵒᵖ).map (RingCat.ofHom (algebraMap A B))
  have h1 := congrArg (fun k ↦ k.hom.app U ((toSheafify J P).app U x))
    (adicBasisCompletedUnit_scalar.{uC, vC, r} J t v a e he ht f hf)
  have h2 : (sheafifyMap J η).app U ((toSheafify J P).app U x) =
      (toSheafify J Q).app U (algebraMap A B x) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J η) U) x).symm
  exact h1.trans (congrArg ((adicBasisFromConstant.{uC, vC, r} J v).hom.app U) h2)

end CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The completed coefficient map `𝒪_E^∧ ⟶ 𝒪_L^∧` admits a Frobenius system.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (finite freeness of the completed coefficient extension);
the Frobenius form of the finite extension `𝒪_E ⟶ 𝒪_L` of discrete valuation rings. -/
theorem integralCompletedScalarMap_frobeniusSystem :
    ∃ d, Nonempty (SheafOfModules.FrobeniusSystem (integralCompletedScalarMap l E L ι Y) d) := by
  classical
  let := ι.toAlgebra
  let := (integralScalarIntegerInclusion l E L ι).toAlgebra
  let : Algebra (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l L) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l L)
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let FC := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let φ := integralCompletedScalarMap l E L ι Y
  have hφ (n : ℕ) : φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n :=
    (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec n
  obtain ⟨b⟩ := integral_basis l E L ι
  obtain ⟨a, e, he, ht⟩ := integral_ramification l E L ι
  let a' : (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L))ˣ :=
    Units.map ULift.ringEquiv.symm.toMonoidHom a
  have ht' : algebraMap (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L))
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) =
      (a' : ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) *
        (ULift.up (Padic.coefficientExtensionUniformizer l L)) ^ e := by
    apply ULift.ext
    exact ht
  obtain ⟨f, hf, -⟩ := adicBasisScalar_exists_unique.{u + 1, u, u} J
    (ULift.up (Padic.coefficientExtensionUniformizer l E))
    (ULift.up (Padic.coefficientExtensionUniformizer l L)) a' e he ht'
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      FC.map (completedIntegralCommRingProjectionUnrestricted l F Y n) =
        limit.π (integralCoefficientSheafSystem l F Y) (op n) := by
    ext U x
    rfl
  have h : f ≫ (completionPresentation l L Y).hom =
      (completionPresentation l E Y).hom ≫ FC.map φ := by
    apply limit.hom_ext
    intro n
    have hφr := congrArg FC.map (hφ n.unop)
    simp only [Functor.map_comp, hproj] at hφr
    rw [Category.assoc, completionPresentation_projection, ← Category.assoc, hf n.unop,
      Category.assoc, finitePresentation_scalar l E Y L ι n.unop a' e he ht',
      ← Category.assoc, ← completionPresentation_projection, Category.assoc, ← hφr,
      ← Category.assoc]
  let A' := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B' := ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)
  let bL : Module.Basis (Fin (Module.finrank E L)) A' B' := liftedBasis.{u, u} b
  have : Module.Free A' B' := Module.Free.of_basis bL
  have : Module.Finite A' B' := Module.Finite.of_basis bL
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l L) :=
    hL.2.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing B' := IsPrincipalIdealRing.of_surjective
    ULift.ringEquiv.symm.toRingHom ULift.ringEquiv.symm.surjective
  have : IsDomain A' := MulEquiv.isDomain
    (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.toMulEquiv
  have : IsDomain B' := MulEquiv.isDomain
    (Padic.coefficientExtensionIntegers l L) ULift.ringEquiv.toMulEquiv
  obtain ⟨t₀, ht₀⟩ := Module.exists_bijective_comp_mulLeft A' B'
  let uA := adicBasisCompletedUnit.{u + 1, u, u} J
    (ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l E))
  let uB := adicBasisCompletedUnit.{u + 1, u, u} J
    (ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l L))
  let κA (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
      A' →+* (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V :=
    ((completionPresentation l E Y).hom.hom.app V).hom.comp (uA.app V).hom
  let κB (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
      B' →+* (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj V :=
    ((completionPresentation l L Y).hom.hom.app V).hom.comp (uB.app V).hom
  have hu (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : A') :
      f.hom.app V (uA.app V x) = uB.app V (algebraMap A' B' x) :=
    adicBasisCompletedUnit_apply_scalar.{u + 1, u, u} J _ _ a' e he ht' f hf V x
  refine ⟨_, ⟨SheafOfModules.FrobeniusSystem.ofBasis bL t₀ ht₀ κA κB ?_ ?_ ?_ ?_⟩⟩
  · intro V W g x
    exact (ConcreteCategory.congr_hom ((completionPresentation l E Y).hom.hom.naturality g)
      _).symm.trans (congrArg ((completionPresentation l E Y).hom.hom.app W)
        (ConcreteCategory.congr_hom (uA.naturality g) x).symm)
  · intro V W g x
    exact (ConcreteCategory.congr_hom ((completionPresentation l L Y).hom.hom.naturality g)
      _).symm.trans (congrArg ((completionPresentation l L Y).hom.hom.app W)
        (ConcreteCategory.congr_hom (uB.naturality g) x).symm)
  · intro V x
    have h1 := congrArg (fun k ↦ k.hom.app V (uA.app V x)) h
    exact h1.symm.trans (congrArg ((completionPresentation l L Y).hom.hom.app V) (hu V x))
  · intro V
    let d := Module.finrank E L
    let Fw := adicBasisForward.{u + 1, u, u} J d bL _ _ f
    have : IsIso Fw := adicBasisForward_isIso.{u + 1, u, u} J d bL _ _ a' e he ht' f hf
    have hFw : Function.Bijective (Fw.val.app V) :=
      ((SheafOfModules.evaluation _ V).mapIso (asIso Fw)).toLinearEquiv.bijective
    let eqv := adicBasisFreeEquiv.{u + 1, u, u} J (adicBasisCompletion.{u + 1, u, u} J A'
      (ULift.up (Padic.coefficientExtensionUniformizer l E))) d V
    have hG' : Function.Bijective fun r' : Fin d → _ ↦
        ∑ i, f.hom.app V (r' i) * uB.app V (bL i) := by
      have hc : (fun r' : Fin d → _ ↦ ∑ i, f.hom.app V (r' i) * uB.app V (bL i)) =
          Fw.val.app V ∘ eqv.symm := by
        funext r'
        rw [Function.comp_apply, adicBasisForward_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← adicBasisFreeEquiv_apply, Equiv.apply_symm_apply]
      rw [hc]
      exact hFw.comp eqv.symm.bijective
    let cE : _ ≃ _ :=
      { toFun := (completionPresentation l E Y).hom.hom.app V
        invFun := (completionPresentation l E Y).inv.hom.app V
        left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g ↦ g.hom) (completionPresentation l E Y).hom_inv_id) V) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g ↦ g.hom) (completionPresentation l E Y).inv_hom_id) V) x }
    let cL : _ ≃ _ :=
      { toFun := (completionPresentation l L Y).hom.hom.app V
        invFun := (completionPresentation l L Y).inv.hom.app V
        left_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g ↦ g.hom) (completionPresentation l L Y).hom_inv_id) V) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom (congr_app
          (congrArg (fun g ↦ g.hom) (completionPresentation l L Y).inv_hom_id) V) x }
    have hc : (fun r : Fin d → (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V ↦
        ∑ i, φ.hom.app V (r i) * κB V (bL i)) =
        cL ∘ (fun r' : Fin d → _ ↦ ∑ i, f.hom.app V (r' i) * uB.app V (bL i)) ∘
          fun r i ↦ cE.symm (r i) := by
      funext r
      simp only [Function.comp_apply, Equiv.coe_fn_mk, cL, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      have h1 := congrArg (fun k ↦ k.hom.app V (cE.symm (r i))) h
      exact (congrArg (φ.hom.app V) (cE.apply_symm_apply (r i)).symm).trans h1.symm
    rw [hc]
    exact cL.bijective.comp (hG'.comp (Equiv.piCongrRight fun _ ↦ cE.symm).bijective)

/-- Frobenius reciprocity for the completed coefficient extension: restriction of scalars along
`𝒪_E^∧ ⟶ 𝒪_L^∧` is left adjoint to the ordinary extension of scalars `𝒪_L^∧ ⊗_{𝒪_E^∧} -`.
Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15; Stacks Tags 03CZ, 03EK. -/
theorem integralOrdinaryScalar_restrictScalars_adjunction :
    Nonempty (SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι Y)) ⊣ integralOrdinaryScalar l E L ι Y) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  let := ι.toAlgebra
  obtain ⟨d, ⟨Φ⟩⟩ := integralCompletedScalarMap_frobeniusSystem l E L ι Y
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E Y L ι
    (integralCompletedScalarMap l E L ι Y)
    (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec
  obtain ⟨hobj, hmap, -⟩ := (integralOrdinaryScalarWitness l E L ι Y).choose_spec
  exact Φ.nonempty_adjunction e.symm _ hobj hmap

end WeilConjectures
