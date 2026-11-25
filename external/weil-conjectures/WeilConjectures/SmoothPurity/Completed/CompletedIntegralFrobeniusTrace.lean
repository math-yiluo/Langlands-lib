/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFrobeniusSystem
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FrobeniusUnitComp
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFrobeniusSystem
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.RingTheory.FrobeniusForm

/-! # The trace element of the completed coefficient Frobenius system

The Frobenius system of the completed coefficient map `𝒪_E^∧ ⟶ 𝒪_L^∧` obtained by base change
of an integral basis `(bᵢ)` of `𝒪_L` over `𝒪_E` and a Frobenius form, with dual basis `(cᵢ)`,
has the property that the section `∑ᵢ bᵢ cᵢ` is the constant section of a nonzero element of
`𝒪_L`. Composing the Frobenius unit with multiplication is therefore multiplication by a nonzero
constant, which is the input of the integral trace splitting.
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
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The finite presentation sends the constant section of a residue class to the constant
section of the corresponding class. -/
private theorem finitePresentation_toSheafify (n : ℕ) (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : Padic.coefficientExtensionIntegers l L) :
    (finitePresentation l L Y n).hom.hom.app V
      (adicBasisConstant.{u + 1, u, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L))
        (ULift.up (Padic.coefficientExtensionUniformizer l L)) n V (ULift.up x)) =
      integralScalarFiniteConstant l L Y n V x := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let U := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let := adicBasisRingSheafify.{u + 1, u, u} J
  have : J.PreservesSheafification U := scalarPreservesSheafification.{u, u} Y
  let X := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
  let e := (constantCommuteCompose J U).app X
  have hA : Functor.whiskerRight (toSheafify J ((Functor.const _).obj X)) U ≫
      ((constantCommuteCompose J U).hom.app X).hom =
      (Functor.constComp _ X U).hom ≫ toSheafify J ((Functor.const _).obj (U.obj X)) := by
    rw [constantCommuteCompose_hom_app_hom, sheafComposeIso_inv_fac_assoc,
      ← toSheafify_naturality]
  have h3 (w : X) : ((constantCommuteCompose J U).inv.app X).hom.app V
      ((toSheafify J ((Functor.const _).obj (U.obj X))).app V w) =
        (toSheafify J ((Functor.const _).obj X)).app V w := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hA V) w
    refine (congrArg _ h.symm).trans ?_
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g ↦ g.hom)
      ((constantCommuteCompose J U).hom_inv_id_app X)) V) _
  have h4 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J
    ((Functor.const (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ).map
      (RingEquiv.toRingCatIso.{u + 1} (liftedQuotient.{u, u}
        (Padic.coefficientExtensionIntegers l L) (Padic.coefficientExtensionUniformizer l L)
          (n + 1))).hom)) V)
    (Ideal.Quotient.mk _ (ULift.up x))
  exact (congrArg (((constantCommuteCompose J U).inv.app X).hom.app V) h4.symm).trans
    (h3 _)

set_option linter.unusedVariables false in
/-- The completed unit of the constant section `x` of `𝒪_L` is the constant section
`integralScalarConstant x` of the completed coefficient sheaf. -/
private theorem completionPresentation_unit_eq (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : Padic.coefficientExtensionIntegers l L) :
    ((completionPresentation l L Y).hom.hom.app V)
      ((adicBasisCompletedUnit.{u + 1, u, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l L))).app V (ULift.up x)) =
      integralScalarConstant l L Y V x := by
  refine (integralScalarConstant_existsUnique l L Y V x).unique (fun n ↦ ?_)
    (integralScalarConstant_existsUnique l L Y V x).exists.choose_spec
  have h1 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun g ↦ g.hom) (completionPresentation_projection l L Y n)) V)
    ((adicBasisCompletedUnit.{u + 1, u, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l L))).app V (ULift.up x))
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (adicBasisCompletedUnit_projection.{u + 1, u, u} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l L)) n) V) (ULift.up x)
  exact h1.trans ((congrArg ((finitePresentation l L Y n).hom.hom.app V) h2).trans
    (finitePresentation_toSheafify l L Y n V x))

/-- The completed coefficient map `𝒪_E^∧ ⟶ 𝒪_L^∧` admits a Frobenius system `(t, (bᵢ), (cᵢ))`
such that `∑ᵢ bᵢ cᵢ` is the image of a nonzero element `w ∈ 𝒪_L` under ring maps
`κ_V : 𝒪_L → 𝒪_L^∧(V)` compatible with restrictions.
Source: Bhatt--Scholze, Lemma 6.8.2(1); the Frobenius form `t₀` of `𝒪_E ⟶ 𝒪_L` satisfies
`t₀(∑ᵢ bᵢ cᵢ) = [L : E] ≠ 0`. -/
theorem integralCompletedScalarMap_frobeniusSystem_trace :
    ∃ (d : ℕ) (Φ : SheafOfModules.FrobeniusSystem (integralCompletedScalarMap l E L ι Y) d)
      (κ : ∀ V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ, Padic.coefficientExtensionIntegers l L →+*
        (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj V),
      (∀ {V W : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ} (g : V ⟶ W) x,
        (completedIntegralCommRingSheafUnrestricted l L Y).obj.map g (κ V x) = κ W x) ∧
      (∀ V x, κ V x = integralScalarConstant l L Y V x) ∧
      (∃ w : Padic.coefficientExtensionIntegers l L, w ≠ 0 ∧
        ∀ V, ∑ i, (Φ.data V).basis i * (Φ.data V).dual i = κ V w) ∧
      ∃ b : Fin d → Padic.coefficientExtensionIntegers l L,
        (letI := (integralScalarIntegerInclusion l E L ι).toAlgebra
          ∃ b' : Module.Basis (Fin d) (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionIntegers l L), ⇑b' = b) ∧
        (∀ V i, (Φ.data V).basis i = κ V (b i)) ∧
        (∀ V i j, (Φ.data V).trace ((Φ.data V).basis i * (Φ.data V).dual j) =
          if i = j then 1 else 0) ∧
        ∀ V, Function.Bijective fun r : Fin d →
            (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V ↦
          ∑ i, (integralCompletedScalarMap l E L ι Y).hom.app V (r i) * κ V (b i) := by
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
  have : CharZero A' := by
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
    let g : A' →+* E := (Padic.coefficientExtensionIntegers l E).subtype.comp
      ULift.ringEquiv.toRingHom
    exact g.charZero
  have : Nonempty (Fin (Module.finrank E L)) := bL.index_nonempty
  have hbij (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) : Function.Bijective fun r :
      Fin (Module.finrank E L) → (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj V ↦
        ∑ i, φ.hom.app V (r i) * κB V (bL i) := by
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
  have hκA {V W : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ} (g : V ⟶ W) (x : A') :
      (completedIntegralCommRingSheafUnrestricted l E Y).obj.map g (κA V x) = κA W x := by
    exact (ConcreteCategory.congr_hom ((completionPresentation l E Y).hom.hom.naturality g)
      _).symm.trans (congrArg ((completionPresentation l E Y).hom.hom.app W)
        (ConcreteCategory.congr_hom (uA.naturality g) x).symm)
  have hκB {V W : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ} (g : V ⟶ W) (x : B') :
      (completedIntegralCommRingSheafUnrestricted l L Y).obj.map g (κB V x) = κB W x := by
    exact (ConcreteCategory.congr_hom ((completionPresentation l L Y).hom.hom.naturality g)
      _).symm.trans (congrArg ((completionPresentation l L Y).hom.hom.app W)
        (ConcreteCategory.congr_hom (uB.naturality g) x).symm)
  have hκ (V : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : A') :
      φ.hom.app V (κA V x) = κB V (algebraMap A' B' x) := by
    have h1 := congrArg (fun k ↦ k.hom.app V (uA.app V x)) h
    exact h1.symm.trans (congrArg ((completionPresentation l L Y).hom.hom.app V) (hu V x))
  refine ⟨_, SheafOfModules.FrobeniusSystem.ofBasis bL t₀ ht₀ κA κB hκA hκB hκ hbij,
    fun V ↦ (κB V).comp ULift.ringEquiv.symm.toRingHom, ?_,
    ?_,
    ⟨(∑ i, bL i * ModuleCat.CoextendScalars.frobeniusDual bL t₀ ht₀ i).down, ?_, fun V ↦ ?_⟩,
    fun i ↦ (bL i).down, ⟨b, ?_⟩, fun V i ↦ rfl, fun V i j ↦ ?_, hbij⟩
  · intro V W g x
    exact (ConcreteCategory.congr_hom ((completionPresentation l L Y).hom.hom.naturality g)
      _).symm.trans (congrArg ((completionPresentation l L Y).hom.hom.app W)
        (ConcreteCategory.congr_hom (uB.naturality g) _).symm)
  · exact fun V x ↦ completionPresentation_unit_eq l L Y V x
  · intro h
    exact ModuleCat.CoextendScalars.sum_mul_frobeniusDual_ne_zero bL t₀ ht₀ (ULift.ext h)
  · exact ((map_sum (κB V) (fun i ↦ bL i * ModuleCat.CoextendScalars.frobeniusDual bL t₀ ht₀ i)
      Finset.univ).trans (Finset.sum_congr rfl fun i _ ↦ map_mul _ _ _)).symm
  · funext i
    simp only [bL, liftedBasis]
    rw [Module.Basis.coe_ofEquivFun]
    simp [Pi.single_apply, apply_ite ULift.down]
  · have h1 := ModuleCat.FrobeniusData.ofBasisTrace_map bL (κA V) (κB V) (hκ V) (hbij V) t₀
      (bL i * ModuleCat.CoextendScalars.frobeniusDual bL t₀ ht₀ j)
    rw [map_mul] at h1
    refine h1.trans ?_
    rw [mul_comm, ModuleCat.CoextendScalars.apply_frobeniusDual_mul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

end WeilConjectures
