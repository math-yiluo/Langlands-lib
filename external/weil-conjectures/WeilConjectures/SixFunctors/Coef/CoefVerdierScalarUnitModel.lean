/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SixFunctors.PurCompactSupport.IntegralScalarTensorIdentity
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
/-! # Tensor and K-flat models for the scalar identity unit

Source: the identity normalization in theorem-verdier-biduality--3.
(blueprint: lem-coef-verdier-scalar-unit-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace WeilConjectures
attribute [local irreducible] completedScalarChangeData completedAdicChangeData
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pbcComplexCounit completedScalarCounit

attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective

attribute [local irreducible] PurCompactSupport.ordinaryUnit

/-- The scalar identity unit constructed by the identity restriction adjunction.
Source: Stacks 03DA (blueprint: lem-coef-verdier-scalar-unit-model). -/
def identityScalarUnit {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R) :
    pbcExtend φ ≅ 𝟭 _ :=
  eqToIso (congrArg pbcExtend h) ≪≫
    ((conjugateIsoEquiv (pbcScalarAdjunction (𝟙 R)) Adjunction.id).symm
      ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose)).symm

attribute [local irreducible] identityScalarUnit PurCompactSupport.tensorIdentity

private theorem linear_inverse_mul {R A B : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (t : R → A → B)
    (hc : ∀ x, g (f x) = x) (h1 : ∀ x, f x = t 1 x)
    (ht : ∀ s z x, t (s * z) x = s • t z x) (s : R) (x : A) :
    g (t s x) = s • x := by
  rw [show t s x = s • f x by simpa only [mul_one, ← h1] using ht s 1 x]
  rw [map_smul, hc]

private theorem identityUnit_tensor {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : pbcModules X R) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    ((PurCompactSupport.ordinaryUnit R).inv.app M).val.app U
        (pbcTensorSection (𝟙 R) M U s x) =
      @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x := by
  apply linear_inverse_mul
    (((PurCompactSupport.ordinaryUnit R).hom.app M).val.app U).hom
    (((PurCompactSupport.ordinaryUnit R).inv.app M).val.app U).hom
    (pbcTensorSection (𝟙 R) M U)
  · intro y
    exact congrArg (fun f : M ⟶ M ↦ f.val.app U y)
      ((PurCompactSupport.ordinaryUnit R).hom_inv_id_app M)
  · exact PurCompactSupport.ordinaryUnit_hom R M U
  · exact completedTensor_smul X (𝟙 R) M U

private theorem scalarUnit_tensor {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R)
    (M : pbcModules X R) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    ((identityScalarUnit R φ h).hom.app M).val.app U (pbcTensorSection φ M U s x) =
      @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x := by
  cases h
  rw [show identityScalarUnit R (𝟙 R) rfl = (PurCompactSupport.ordinaryUnit R).symm by
    unfold identityScalarUnit
    simp only [eqToIso_refl, Iso.refl_trans]
    unfold PurCompactSupport.ordinaryUnit PurCompactSupport.restrictionUnit
    rfl]
  exact identityUnit_tensor R M U s x

attribute [local instance 100000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

private theorem derivedUnit_model {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R)
    (P : CochainComplex (pbcModules X R) ℤ) (hp : proEtaleFlatRepresentatives.{u} X R P) :
    (eqToIso (congrArg pbcDerivedExtend h) ≪≫
      PurCompactSupport.tensorIdentity R).hom.app (DerivedCategory.Q.obj P) =
      pbcComplexCounit φ P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (identityScalarUnit R φ h) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_trans]
  rw [show identityScalarUnit R (𝟙 R) rfl = (PurCompactSupport.ordinaryUnit R).symm by
    unfold identityScalarUnit
    simp only [eqToIso_refl, Iso.refl_trans]
    unfold PurCompactSupport.ordinaryUnit PurCompactSupport.restrictionUnit
    rfl]
  let t : P ≅ ((pbcExtend (𝟙 R)).mapHomologicalComplex (.up ℤ)).obj P :=
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).symm.app P ≪≫
      (NatIso.mapHomologicalComplex (PurCompactSupport.ordinaryUnit R) (.up ℤ)).app P
  have ht : (PurCompactSupport.tensorIdentity R).inv.app (DerivedCategory.Q.obj P) ≫
      pbcComplexCounit (𝟙 R) P = DerivedCategory.Q.map t.hom := by
    have ht' : t.hom =
        (NatTrans.mapHomologicalComplex (PurCompactSupport.ordinaryUnit R).hom (.up ℤ)).app
          P := by
      apply HomologicalComplex.Hom.ext
      funext n
      simp only [t, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
        NatIso.mapHomologicalComplex_hom_app_f, NatTrans.mapHomologicalComplex_app_f]
      exact Category.id_comp _
    rw [ht']
    exact PurCompactSupport.derivedUnit_complex R P hp
  have hi : (PurCompactSupport.tensorIdentity R).hom.app (DerivedCategory.Q.obj P) =
      pbcComplexCounit (𝟙 R) P ≫ DerivedCategory.Q.map t.inv := by
    apply (cancel_epi ((PurCompactSupport.tensorIdentity R).inv.app
      (DerivedCategory.Q.obj P))).mp
    rw [← Category.assoc, ht, ← Functor.map_comp, t.hom_inv_id, CategoryTheory.Functor.map_id,
      Iso.inv_hom_id_app]
    rfl
  exact hi

/-- The ordinary identity scalar unit has the sectionwise multiplication formula.
Source: Stacks 03DA; identity extension of scalars.
(blueprint: lem-coef-verdier-scalar-unit-model).
-/
private theorem scalar_identity_unit_tensor {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R)
    (M : pbcModules X R) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    ((identityScalarUnit R φ h).hom.app M).val.app U (pbcTensorSection φ M U s x) =
      @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x := by
  exact scalarUnit_tensor R φ h M U s x

/-- The derived identity scalar unit is the counit followed by the chain unit.
Source: Stacks 06YY; the K-flat derived identity extension formula.
(blueprint: lem-coef-verdier-scalar-unit-model).
-/
private theorem scalar_identity_unit_derived {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R) :
    ∀ (P : CochainComplex (pbcModules X R) ℤ)
      (_ : proEtaleFlatRepresentatives.{u} X R P),
      (eqToIso (congrArg pbcDerivedExtend h) ≪≫
        PurCompactSupport.tensorIdentity R).hom.app (DerivedCategory.Q.obj P) =
        pbcComplexCounit φ P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (identityScalarUnit R φ h) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) := by
  intro P hp
  exact derivedUnit_model R φ h P hp

/-- Tensor and K-flat formulas for the constructed scalar identity units.
Source: Stacks 03DA and 06YY; the identity clause of theorem-verdier-biduality--3.
(blueprint: lem-coef-verdier-scalar-unit-model).

Proof: the inverse ordinary adjoint mate multiplies pure tensors, since the
forward mate inserts 1 and is linear. On flat-term K-flat complexes, cancel
the inverse derived mate in the derived adjunction unit formula. The chain
isomorphism inverse equations give the displayed counit formula. -/
theorem scalar_identity_unit_model {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (φ : R ⟶ R) (h : φ = 𝟙 R) :
    (∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U),
      ((identityScalarUnit R φ h).hom.app M).val.app U (pbcTensorSection φ M U s x) =
        @SMul.smul _ _ (M.val.obj U).isModule.toSMul s x) ∧
    ∀ (P : CochainComplex (pbcModules X R) ℤ)
      (_ : proEtaleFlatRepresentatives.{u} X R P),
      (eqToIso (congrArg pbcDerivedExtend h) ≪≫
        PurCompactSupport.tensorIdentity R).hom.app (DerivedCategory.Q.obj P) =
        pbcComplexCounit φ P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (identityScalarUnit R φ h) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) := by
  exact ⟨scalar_identity_unit_tensor R φ h, scalar_identity_unit_derived R φ h⟩

end WeilConjectures
