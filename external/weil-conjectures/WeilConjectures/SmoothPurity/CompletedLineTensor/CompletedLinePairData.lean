/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLinePowerComparison
public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import all WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Normalized ordinary comparisons between scalar extension and line tensor

Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

For a comparison `b` between the scalar extension of a line `L` and a line `N`, there is
a unique `PairData` satisfying `IsPairNormalized`. Its derived comparison satisfies the
counit normalization on every complex, and the comparisons for a three-field tower
are compatible with the ordinary associator.

## Main statements

* `pairData_exists`, `pairData_unique`: existence and uniqueness of normalized data.
* `pairData_ordinary_tower`: compatibility with the ordinary associator.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

open scoped ChangeOfRings

section Identification

attribute [local semireducible] completedOrdinaryScalarExtension completedScalarTensorSection

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded ordinary extension is the sheafified scalar extension.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem extension_obj_eq (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l E F ι X).obj M =
      SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) M :=
  completedOrdinaryScalarExtension_obj l E F ι X M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identification sends the recorded pure section to the scalar-extension section.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem extension_obj_eq_section (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U) :
    (eqToHom (extension_obj_eq l E X F ι M)).val.app U
        (completedScalarTensorSection l E F ι X M U s x) =
      SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) M U s x := by
  have b := ((completedScalarChangeData l E F ι X).choose_spec.choose M).symm
  have key : eqToHom b ≫ eqToHom (extension_obj_eq l E X F ι M) =
      𝟙 (SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) M) :=
    (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  exact congrArg (fun f ↦ f.val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf
        (completedCoefficientMap l E F ι X) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
            ((completedCoefficientMap l E F ι X).hom.app U).hom] x))) key

end Identification

/-- The inverse identification sends the scalar-extension section to the recorded one.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem extension_obj_eq_symm_section (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (x : M.val.obj U) :
    (eqToHom (extension_obj_eq l E X F ι M).symm).val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) M U s x) =
      completedScalarTensorSection l E F ι X M U s x := by
  rw [← extension_obj_eq_section l E X F ι M U s x]
  exact congrArg (fun f ↦ f.val.app U (completedScalarTensorSection l E F ι X M U s x))
    (eqToIso (extension_obj_eq l E X F ι M)).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring with an isomorphism in the second variable.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def tensorSecondIso (M : integralTowerModules l F X) {N N' : integralTowerModules l F X}
    (e : N ≅ N') :
    (SheafOfModules.siteSheafTensorRight N).obj M ≅
      (SheafOfModules.siteSheafTensorRight N').obj M where
  hom := SheafOfModules.siteSheafTensorSecondMap M e.hom
  inv := SheafOfModules.siteSheafTensorSecondMap M e.inv
  hom_inv_id := by
    apply SheafOfModules.scalarTensor_hom_ext
    intro U x y
    have h1 := SheafOfModules.scalarTensor_second_tmul M e.hom U x y
    have h2 := SheafOfModules.scalarTensor_second_tmul M e.inv U x (e.hom.val.app U y)
    have h3 : e.inv.val.app U (e.hom.val.app U y) = y :=
      congrArg (fun f ↦ f.val.app U y) e.hom_inv_id
    exact (congrArg (fun z ↦ (SheafOfModules.siteSheafTensorSecondMap M e.inv).val.app U z)
      h1).trans (h2.trans (congrArg _ h3))
  inv_hom_id := by
    apply SheafOfModules.scalarTensor_hom_ext
    intro U x y
    have h1 := SheafOfModules.scalarTensor_second_tmul M e.inv U x y
    have h2 := SheafOfModules.scalarTensor_second_tmul M e.hom U x (e.inv.val.app U y)
    have h3 : e.hom.val.app U (e.inv.val.app U y) = y :=
      congrArg (fun f ↦ f.val.app U y) e.inv_hom_id
    exact (congrArg (fun z ↦ (SheafOfModules.siteSheafTensorSecondMap M e.hom).val.app U z)
      h1).trans (h2.trans (congrArg _ h3))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary scalar–line comparison at one module: binary tensor comparison followed by
the signed-power comparison on the second factor.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def sheafComponent (L : integralTowerModules l E X) (N : integralTowerModules l F X)
    (m : ℤ) (B : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1),
      max u (t + 1)} (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m)
    (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l E F ι X).obj ((sheaf l E X L m).obj M) ≅
      (sheaf l F X N m).obj ((completedOrdinaryScalarExtension l E F ι X).obj M) :=
  eqToIso (extension_obj_eq l E X F ι _) ≪≫
    (binary l E X F ι).tensorComparison M (power l E X L m) ≪≫
    tensorSecondIso l X F _ B ≪≫
    (SheafOfModules.siteSheafTensorRight (power l F X N m)).mapIso
      (eqToIso (extension_obj_eq l E X F ι M).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pure-tensor formula of `sheafComponent`.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem sheafComponent_tmul (L : integralTowerModules l E X)
    (N : integralTowerModules l F X)
    (m : ℤ) (B : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1),
      max u (t + 1)} (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m)
    (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (x : M.val.obj U) (a : (power l E X L m).val.obj U) :
    (sheafComponent l E X F ι L N m B M).hom.val.app U
        (completedScalarTensorSection l E F ι X ((sheaf l E X L m).obj M) U s
          (tmul l E X L m M U x a)) =
      tmul l F X N m ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        (completedScalarTensorSection l E F ι X M U s x)
        (B.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a)) := by
  let g2 := ((binary l E X F ι).tensorComparison M (power l E X L m)).hom.val.app U
  let g3 := (tensorSecondIso l X F
    (SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) M) B).hom.val.app U
  let g4 := ((SheafOfModules.siteSheafTensorRight (power l F X N m)).map
      (eqToHom (extension_obj_eq l E X F ι M).symm)).val.app U
  have h1 := extension_obj_eq_section l E X F ι ((sheaf l E X L m).obj M) U s
    (tmul l E X L m M U x a)
  have h2 := (binary l E X F ι).tensor_tmul M (power l E X L m) U s x a
  have h3 := SheafOfModules.scalarTensor_second_tmul
    (SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) M) B.hom U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) M U s x)
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a)
  have h4 := SheafOfModules.scalarTensor_first_tmul
    (eqToHom (extension_obj_eq l E X F ι M).symm) (power l F X N m) U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) M U s x)
    (B.hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))
  have h5 := extension_obj_eq_symm_section l E X F ι M U s x
  exact (congrArg (fun z ↦ g4 (g3 (g2 z))) h1).trans ((congrArg (fun z ↦ g4 (g3 z)) h2).trans
    ((congrArg g4 h3).trans (h4.trans (congrArg (fun y ↦
      SheafOfModules.siteSheafTensorTmul _ (power l F X N m) U y
        (B.hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))) h5))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `sheafComponent` in the module.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem sheafComponent_naturality (L : integralTowerModules l E X)
    (N : integralTowerModules l F X)
    (m : ℤ) (B : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1),
      max u (t + 1)} (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m)
    {M M' : integralTowerModules l E X} (f : M ⟶ M') :
    (completedOrdinaryScalarExtension l E F ι X).map ((sheaf l E X L m).map f) ≫
        (sheafComponent l E X F ι L N m B M').hom =
      (sheafComponent l E X F ι L N m B M).hom ≫
        (sheaf l F X N m).map ((completedOrdinaryScalarExtension l E F ι X).map f) := by
  rw [← cancel_epi (eqToHom (extension_obj_eq l E X F ι ((sheaf l E X L m).obj M)).symm)]
  apply SheafOfModules.scalarExtension_tensor_hom_ext
  intro U s x a
  have h0 := extension_obj_eq_symm_section l E X F ι ((sheaf l E X L m).obj M) U s
    (tmul l E X L m M U x a)
  have hl1 := completedScalarTensorSection_naturality l E F ι X ((sheaf l E X L m).map f) U s
    (tmul l E X L m M U x a)
  have hl2 := SheafOfModules.scalarTensor_first_tmul f (power l E X L m) U x a
  have hl3 := sheafComponent_tmul l E X F ι L N m B M' U s (f.val.app U x) a
  have hr1 := sheafComponent_tmul l E X F ι L N m B M U s x a
  have hr2 := SheafOfModules.scalarTensor_first_tmul
    ((completedOrdinaryScalarExtension l E F ι X).map f) (power l F X N m) U
    (completedScalarTensorSection l E F ι X M U s x)
    (B.hom.val.app U
      (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))
  have hr3 := completedScalarTensorSection_naturality l E F ι X f U s x
  let gl := (sheafComponent l E X F ι L N m B M').hom.val.app U
  let gr := ((sheaf l F X N m).map ((completedOrdinaryScalarExtension l E F ι X).map f)).val.app U
  let ol := ((completedOrdinaryScalarExtension l E F ι X).map ((sheaf l E X L m).map f)).val.app U
  let b := B.hom.val.app U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a)
  have hL := (congrArg (fun z ↦ gl (ol z)) h0).trans ((congrArg gl hl1).trans
    ((congrArg (fun z ↦ gl (completedScalarTensorSection l E F ι X
      ((sheaf l E X L m).obj M') U s z)) hl2).trans hl3))
  have hR := (congrArg (fun z ↦ gr ((sheafComponent l E X F ι L N m B M).hom.val.app U z)) h0).trans
    ((congrArg gr hr1).trans (hr2.trans
      (congrArg (fun y ↦ SheafOfModules.siteSheafTensorTmul _ (power l F X N m) U y b) hr3)))
  exact hL.trans hR.symm

/-- The ordinary scalar–line comparison as a natural isomorphism.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def sheafComparison (L : integralTowerModules l E X) (N : integralTowerModules l F X)
    (m : ℤ) (B : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1),
      max u (t + 1)} (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m) :
    sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m :=
  NatIso.ofComponents (sheafComponent l E X F ι L N m B)
    (fun f ↦ sheafComponent_naturality l E X F ι L N m B f)

section CounitNaturality

attribute [local semireducible] completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedOrdinaryScalarComplex completedScalarChangeData

/-- The recorded cochain model computes the ordinary derived scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem model_functor :
    (completedScalarCochainModel l E F ι X).T = completedDerivedScalarExtension l E F ι X := by
  rfl

/-- The recorded cochain model extends termwise by the ordinary scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem model_complex :
    (completedScalarCochainModel l E F ι X).E.mapHomologicalComplex (.up ℤ) =
      completedOrdinaryScalarComplex l E F ι X := by
  rfl

/-- The cochain model counit is the universal counit.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem model_counit (P : CochainComplex (integralTowerModules l E X) ℤ) :
    HEq ((completedScalarCochainModel l E F ι X).ε.app P)
      (completedScalarCounit l E F ι X P) :=
  heq_of_eq (completedScalarCochainModel_counit l E F ι X P)

end CounitNaturality

/-- Naturality transported along equalities of functors.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem naturality_of_heq {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (G G' : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (D D' : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ D ⟶ G ⋙ DerivedCategory.Q) (hG : G = G') (hD : D = D')
    (c : ∀ P : CochainComplex A ℤ,
      D'.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (G'.obj P))
    (hc : ∀ P, HEq (ε.app P) (c P)) {P P' : CochainComplex A ℤ} (f : P ⟶ P') :
    D'.map (DerivedCategory.Q.map f) ≫ c P' = c P ≫ DerivedCategory.Q.map (G'.map f) := by
  subst hG hD
  rw [← eq_of_heq (hc P), ← eq_of_heq (hc P')]
  exact ε.naturality f

/-- Naturality of the universal counit of ordinary scalar extension along chain maps.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem counit_naturality {P P' : CochainComplex (integralTowerModules l E X) ℤ}
    (f : P ⟶ P') :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map f) ≫
        completedScalarCounit l E F ι X P' =
      completedScalarCounit l E F ι X P ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map f) :=
  naturality_of_heq _ _ _ _ (completedScalarCochainModel l E F ι X).ε
    (model_complex l E X F ι) (model_functor l E X F ι) (completedScalarCounit l E F ι X)
    (model_counit l E X F ι) f

/-- The universal counit as a natural isomorphism; finite free extension inverts it.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def counitIso :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension l E F ι X ≅
      completedOrdinaryScalarComplex l E F ι X ⋙ DerivedCategory.Q :=
  letI : ∀ P, IsIso (completedScalarCounit l E F ι X P) :=
    (finiteFreeScalarCochainProperties l E F ι X).2.2
  NatIso.ofComponents (fun P ↦ asIso (completedScalarCounit l E F ι X P))
    (fun f ↦ counit_naturality l E X F ι f)

/-- Descend a termwise comparison through the localization, given invertible counits.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem exists_derived_comparison {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (TA : DerivedCategory A ⥤ DerivedCategory A) (TB : DerivedCategory B ⥤ DerivedCategory B)
    (D : DerivedCategory A ⥤ DerivedCategory B)
    (cTA : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (cTB : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (cO : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (φA : DerivedCategory.Q ⋙ TA ≅ cTA ⋙ DerivedCategory.Q)
    (φB : DerivedCategory.Q ⋙ TB ≅ cTB ⋙ DerivedCategory.Q)
    (κ : DerivedCategory.Q ⋙ D ≅ cO ⋙ DerivedCategory.Q) (γ : cTA ⋙ cO ≅ cO ⋙ cTB) :
    ∃ e : TA ⋙ D ≅ D ⋙ TB, ∀ P : CochainComplex A ℤ,
      D.map (φA.hom.app P) ≫ κ.hom.app (cTA.obj P) ≫ DerivedCategory.Q.map (γ.hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫ TB.map (κ.hom.app P) ≫
          φB.hom.app (cO.obj P) := by
  let k : DerivedCategory.Q ⋙ (TA ⋙ D) ≅ DerivedCategory.Q ⋙ (D ⋙ TB) :=
    Functor.isoWhiskerRight φA D ≪≫ Functor.isoWhiskerLeft cTA κ ≪≫
      Functor.isoWhiskerRight γ DerivedCategory.Q ≪≫ Functor.isoWhiskerLeft cO φB.symm ≪≫
      Functor.isoWhiskerRight κ.symm TB
  let ff := Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory B)
  refine ⟨ff.preimageIso k, fun P ↦ ?_⟩
  have he := NatTrans.congr_app (ff.map_preimage k.hom) P
  change (ff.preimage k.hom).app (DerivedCategory.Q.obj P) = k.hom.app P at he
  change _ = (ff.preimage k.hom).app (DerivedCategory.Q.obj P) ≫ _
  rw [he]
  change _ = (D.map (φA.hom.app P) ≫ κ.hom.app (cTA.obj P) ≫
    DerivedCategory.Q.map (γ.hom.app P) ≫ φB.inv.app (cO.obj P) ≫ TB.map (κ.inv.app P)) ≫
      TB.map (κ.hom.app P) ≫ φB.hom.app (cO.obj P)
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← TB.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [TB.map_id]
  rw [Category.id_comp, Iso.inv_hom_id_app]
  exact congrArg (fun g ↦ D.map (φA.hom.app P) ≫ κ.hom.app (cTA.obj P) ≫ g)
    (Category.comp_id (DerivedCategory.Q.map (γ.hom.app P))).symm

/-- Normalized ordinary comparisons exist; the derived comparison satisfies the counit
normalization on every complex, not only on good ones.
Source: Stacks 03EL, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: take the normalized signed-power comparisons. The binary tensor comparison followed
by the power comparison on the second factor gives the sheaf comparison with the displayed
pure-tensor formula. Finite free extension has invertible universal counits on every
complex, and line tensor is exact, so the composite of the localized termwise comparison
with these invertible maps descends through the localization to the derived category. -/
theorem pairData_exists (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃ d : PairData l E X F ι L N, IsPairNormalized l E X F ι L N b d ∧
      ∀ (m : ℤ) (P : CochainComplex (integralTowerModules l E X) ℤ),
        (completedDerivedScalarExtension l E F ι X).map ((factors l E X L m).hom.app P) ≫
            completedScalarCounit l E F ι X ((complex l E X L m).obj P) ≫
            DerivedCategory.Q.map
              ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P) =
          (d.ordinary m).hom.app (DerivedCategory.Q.obj P) ≫
            (tensor l F X N m).map (completedScalarCounit l E F ι X P) ≫
            (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P) := by
  obtain ⟨B, hB⟩ := line_exists l E X F ι L N b
  have hD (m : ℤ) := exists_derived_comparison (tensor l E X L m) (tensor l F X N m)
    (completedDerivedScalarExtension l E F ι X) (complex l E X L m) (complex l F X N m)
    (completedOrdinaryScalarComplex l E F ι X) (factors l E X L m) (factors l F X N m)
    (counitIso l E X F ι)
    (comparisonComplex l E X F ι L N m (sheafComparison l E X F ι L N m (B m)))
  choose D hD using hD
  refine ⟨(B, fun m ↦ sheafComparison l E X F ι L N m (B m), D),
    ⟨hB.1, hB.2, ?_, ?_⟩, ?_⟩
  · intro m M U s x a
    exact sheafComponent_tmul l E X F ι L N m (B m) M U s x a
  · intro m P
    exact heq_of_eq (hD m P.obj)
  · intro m P
    exact hD m P

/-- Normalized ordinary comparisons are unique.
Source: Stacks 03EL, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the signed-power comparisons are unique by `line_unique`. The sheaf comparison is
fixed on pure tensors, which generate locally. On good complexes the counit at the source
and the target are invertible, so the derived comparison is fixed on the good
localization, which determines natural transformations. -/
theorem pairData_unique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    {d d' : PairData l E X F ι L N} (hd : IsPairNormalized l E X F ι L N b d)
    (hd' : IsPairNormalized l E X F ι L N b d') : d = d' := by
  have hB : d.line = d'.line :=
    line_unique l E X F ι L N b (B := d.line) (B' := d'.line) ⟨hd.1, hd.2.1⟩ ⟨hd'.1, hd'.2.1⟩
  have hS (m : ℤ) : d.ordinarySheaf m = d'.ordinarySheaf m := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rw [← cancel_epi (eqToHom (extension_obj_eq l E X F ι ((sheaf l E X L m).obj M)).symm)]
    apply SheafOfModules.scalarExtension_tensor_hom_ext
    intro U s x a
    have h0 := extension_obj_eq_symm_section l E X F ι ((sheaf l E X L m).obj M) U s
      (tmul l E X L m M U x a)
    have e1 := congrArg (fun z ↦ ((d.ordinarySheaf m).hom.app M).val.app U z) h0
    have e2 := congrArg (fun z ↦ ((d'.ordinarySheaf m).hom.app M).val.app U z) h0
    have e3 := congrArg (fun B : LineFamily l E X F ι L N ↦
      tmul l F X N m ((completedOrdinaryScalarExtension l E F ι X).obj M) U
        (completedScalarTensorSection l E F ι X M U s x)
        ((B m).hom.val.app U
          (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
            (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a))) hB
    exact e1.trans ((hd.2.2.1 m M U s x a).trans
      (e3.trans ((hd'.2.2.1 m M U s x a).symm.trans e2.symm)))
  have hO (m : ℤ) : d.ordinary m = d'.ordinary m := by
    let Qg := integralOperationsGoodLocalization l E X
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    have : Qg.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
    apply Iso.ext
    apply (Localization.fullyFaithfulWhiskeringLeft Qg W _).map_injective
    apply NatTrans.ext
    funext P
    have h1 := eq_of_heq (hd.2.2.2 m P)
    have h2 := eq_of_heq (hd'.2.2.2 m P)
    rw [← hS m] at h2
    have hc : IsIso (completedScalarCounit l E F ι X P.obj) :=
      (finiteFreeScalarCochainProperties l E F ι X).2.2 P.obj
    have hm : IsIso ((tensor l F X N m).map (completedScalarCounit l E F ι X P.obj)) :=
      Functor.map_isIso _ _
    exact (Iso.cancel_iso_hom_right _ _ (asIso ((tensor l F X N m).map
      (completedScalarCounit l E F ι X P.obj)) ≪≫ (factors l F X N m).app
        ((completedOrdinaryScalarComplex l E F ι X).obj P.obj))).1 (h1.symm.trans h2)
  obtain ⟨B, S, D⟩ := d
  obtain ⟨B', S', D'⟩ := d'
  exact Prod.ext hB (Prod.ext (funext hS) (funext hO))

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary associator inverts to `u ⊗ y ↦ u ⊗ (1 ⊗ y)`.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem associator_inv_section (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (u : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (y : M.val.obj U) :
    (((associatorData l E X F ι G j).sheaf.inv.app M).val.app U
        (completedScalarTensorSection l E G (j.comp ι) X M U u y)) =
      completedScalarTensorSection l F G j X _ U u
        (completedScalarTensorSection l E F ι X M U 1 y) := by
  have h := (associatorData_existsUnique l E X F ι G j).exists.choose_spec.1 M U 1 u y
  rw [map_one, mul_one] at h
  exact (congrArg (fun z ↦ ((associatorData l E X F ι G j).sheaf.inv.app M).val.app U z)
    h.symm).trans (congrArg (fun f ↦ f.val.app U (completedScalarTensorSection l F G j X _ U u
        (completedScalarTensorSection l E F ι X M U 1 y)))
      ((associatorData l E X F ι G j).sheaf.hom_inv_id_app M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The termwise tower identity for the ordinary scalar–line comparisons.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem sheaf_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
            max u (t + 1)} (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    {d10 : PairData l E X F ι L N} {d21 : PairData l F X G j N P}
    {d20 : PairData l E X G (j.comp ι) L P}
    (h10 : IsPairNormalized l E X F ι L N b10 d10)
    (h21 : IsPairNormalized l F X G j N P b21 d21)
    (h20 : IsPairNormalized l E X G (j.comp ι) L P b20 d20)
    (m : ℤ) (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l F G j X).map ((d10.ordinarySheaf m).hom.app M) ≫
        (d21.ordinarySheaf m).hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≫
        (sheaf l G X P m).map ((associatorData l E X F ι G j).sheaf.hom.app M) =
      (associatorData l E X F ι G j).sheaf.hom.app ((sheaf l E X L m).obj M) ≫
        (d20.ordinarySheaf m).hom.app M := by
  rw [← cancel_epi ((associatorData l E X F ι G j).sheaf.inv.app ((sheaf l E X L m).obj M)),
    Iso.inv_hom_id_app_assoc,
    ← cancel_epi (eqToHom (extension_obj_eq l E X G (j.comp ι) ((sheaf l E X L m).obj M)).symm)]
  apply SheafOfModules.scalarExtension_tensor_hom_ext
  intro U u x a
  have hα := (associatorData_existsUnique l E X F ι G j).exists.choose_spec.1 M U 1 u x
  have e1 : u * (completedCoefficientMap l F G j X).hom.app U 1 = u := by rw [map_one, mul_one]
  have e2 : (1 : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) *
      (completedCoefficientMap l F G j X).hom.app U 1 = 1 := by rw [map_one, mul_one]
  replace hα := hα.trans (congrArg (fun s ↦
    completedScalarTensorSection l E G (j.comp ι) X M U s x) e1)
  have hl := line_tower l E X F ι G j L N P b10 b21 b20 hb (B10 := d10.line) (B21 := d21.line)
    (B20 := d20.line) ⟨h10.1, h10.2.1⟩ ⟨h21.1, h21.2.1⟩ ⟨h20.1, h20.2.1⟩ m U 1 1 a
  replace hl := hl.trans (congrArg (fun s ↦ (d20.line m).hom.val.app U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) (power l E X L m) U s a)) e2)
  let O1 := completedOrdinaryScalarExtension l E F ι X
  let O2 := completedOrdinaryScalarExtension l F G j X
  let α := (associatorData l E X F ι G j).sheaf
  let w := tmul l E X L m M U x a
  let b1 := (d10.line m).hom.val.app U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L m) U 1 a)
  let c := (d21.line m).hom.val.app U
    (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) (power l F X N m) U 1 b1)
  let g1 := (α.inv.app ((sheaf l E X L m).obj M)).val.app U
  let g2 := (O2.map ((d10.ordinarySheaf m).hom.app M)).val.app U
  let g4 := ((d21.ordinarySheaf m).hom.app (O1.obj M)).val.app U
  let g5 := ((sheaf l G X P m).map (α.hom.app M)).val.app U
  have s0 := extension_obj_eq_symm_section l E X G (j.comp ι) ((sheaf l E X L m).obj M) U u w
  have s1 := associator_inv_section l E X F ι G j ((sheaf l E X L m).obj M) U u w
  have s2 := completedScalarTensorSection_naturality l F G j X ((d10.ordinarySheaf m).hom.app M)
    U u (completedScalarTensorSection l E F ι X _ U 1 w)
  have s3 := h10.2.2.1 m M U 1 x a
  have s4 := h21.2.2.1 m (O1.obj M) U u (completedScalarTensorSection l E F ι X M U 1 x) b1
  have s5 := SheafOfModules.scalarTensor_first_tmul (α.hom.app M) (power l G X P m) U
    (completedScalarTensorSection l F G j X _ U u (completedScalarTensorSection l E F ι X M U 1 x))
    c
  have c20 := h20.2.2.1 m M U u x a
  have hL := (congrArg (fun z ↦ g5 (g4 (g2 (g1 z)))) s0).trans
    ((congrArg (fun z ↦ g5 (g4 (g2 z))) s1).trans ((congrArg (fun z ↦ g5 (g4 z)) s2).trans
      ((congrArg (fun z ↦ g5 (g4 (completedScalarTensorSection l F G j X _ U u z))) s3).trans
        ((congrArg g5 s4).trans (s5.trans ((congrArg (fun z ↦
          SheafOfModules.siteSheafTensorTmul _ (power l G X P m) U z c) hα).trans
          (congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul _ (power l G X P m) U
            (completedScalarTensorSection l E G (j.comp ι) X M U u x) z) hl)))))))
  have hR := (congrArg (fun z ↦ ((d20.ordinarySheaf m).hom.app M).val.app U z) s0).trans c20
  exact hL.trans hR.symm

/-- Abstract form of the derived tower identity: the counit normalizations of three
scalar–line comparisons and of the associator, together with the termwise identity, give the
derived identity on localized objects.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem derived_tower_of_formulas {KA KB KC DA DB DC : Type*} [Category KA]
    [Category KB] [Category KC] [Category DA] [Category DB] [Category DC]
    (QA : KA ⥤ DA) (QB : KB ⥤ DB) (QC : KC ⥤ DC)
    (cTA : KA ⥤ KA) (cTB : KB ⥤ KB) (cTC : KC ⥤ KC) (TA : DA ⥤ DA) (TB : DB ⥤ DB)
    (TC : DC ⥤ DC) (cO1 : KA ⥤ KB) (cO2 : KB ⥤ KC) (cO3 : KA ⥤ KC)
    (C1 : DA ⥤ DB) (C2 : DB ⥤ DC) (C3 : DA ⥤ DC)
    (φA : QA ⋙ TA ≅ cTA ⋙ QA) (φB : QB ⋙ TB ≅ cTB ⋙ QB) (φC : QC ⋙ TC ≅ cTC ⋙ QC)
    (κ1 : ∀ P, C1.obj (QA.obj P) ⟶ QB.obj (cO1.obj P))
    (κ2 : ∀ P, C2.obj (QB.obj P) ⟶ QC.obj (cO2.obj P))
    (κ3 : ∀ P, C3.obj (QA.obj P) ⟶ QC.obj (cO3.obj P))
    (hκ2 : ∀ {P P' : KB} (f : P ⟶ P'), C2.map (QB.map f) ≫ κ2 P' = κ2 P ≫ QC.map (cO2.map f))
    (D10 : TA ⋙ C1 ≅ C1 ⋙ TB) (D21 : TB ⋙ C2 ≅ C2 ⋙ TC) (D20 : TA ⋙ C3 ≅ C3 ⋙ TC)
    (A : C1 ⋙ C2 ≅ C3)
    (γ10 : cTA ⋙ cO1 ≅ cO1 ⋙ cTB) (γ21 : cTB ⋙ cO2 ≅ cO2 ⋙ cTC) (γ20 : cTA ⋙ cO3 ≅ cO3 ⋙ cTC)
    (α : cO1 ⋙ cO2 ≅ cO3)
    (F10 : ∀ P, C1.map (φA.hom.app P) ≫ κ1 (cTA.obj P) ≫ QB.map (γ10.hom.app P) =
      D10.hom.app (QA.obj P) ≫ TB.map (κ1 P) ≫ φB.hom.app (cO1.obj P))
    (F21 : ∀ P, C2.map (φB.hom.app P) ≫ κ2 (cTB.obj P) ≫ QC.map (γ21.hom.app P) =
      D21.hom.app (QB.obj P) ≫ TC.map (κ2 P) ≫ φC.hom.app (cO2.obj P))
    (F20 : ∀ P, C3.map (φA.hom.app P) ≫ κ3 (cTA.obj P) ≫ QC.map (γ20.hom.app P) =
      D20.hom.app (QA.obj P) ≫ TC.map (κ3 P) ≫ φC.hom.app (cO3.obj P))
    (FA : ∀ P, C2.map (κ1 P) ≫ κ2 (cO1.obj P) ≫ QC.map (α.hom.app P) =
      A.hom.app (QA.obj P) ≫ κ3 P)
    (hchain : ∀ P, cO2.map (γ10.hom.app P) ≫ γ21.hom.app (cO1.obj P) ≫ cTC.map (α.hom.app P) =
      α.hom.app (cTA.obj P) ≫ γ20.hom.app P)
    (hiso : ∀ P, IsIso (κ3 P)) (P : KA) :
    C2.map (D10.hom.app (QA.obj P)) ≫ D21.hom.app (C1.obj (QA.obj P)) ≫
        TC.map (A.hom.app (QA.obj P)) =
      A.hom.app (TA.obj (QA.obj P)) ≫ D20.hom.app (QA.obj P) := by
  have : IsIso (κ3 P) := hiso P
  rw [← cancel_mono (TC.map (κ3 P) ≫ φC.hom.app (cO3.obj P))]
  have hR : (A.hom.app (TA.obj (QA.obj P)) ≫ D20.hom.app (QA.obj P)) ≫ TC.map (κ3 P) ≫
      φC.hom.app (cO3.obj P) = C2.map (C1.map (φA.hom.app P)) ≫ C2.map (κ1 (cTA.obj P)) ≫
        κ2 (cO1.obj (cTA.obj P)) ≫ QC.map (α.hom.app (cTA.obj P)) ≫ QC.map (γ20.hom.app P) := by
    rw [Category.assoc, ← F20 P, ← A.hom.naturality_assoc]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← reassoc_of% (FA (cTA.obj P))]
  have hL : (C2.map (D10.hom.app (QA.obj P)) ≫ D21.hom.app (C1.obj (QA.obj P)) ≫
      TC.map (A.hom.app (QA.obj P))) ≫ TC.map (κ3 P) ≫ φC.hom.app (cO3.obj P) =
      C2.map (C1.map (φA.hom.app P)) ≫ C2.map (κ1 (cTA.obj P)) ≫
        κ2 (cO1.obj (cTA.obj P)) ≫ QC.map (cO2.map (γ10.hom.app P)) ≫
          QC.map (γ21.hom.app (cO1.obj P)) ≫ QC.map (cTC.map (α.hom.app P)) := by
    have hn1 := D21.hom.naturality (κ1 P)
    have hn2 := φC.hom.naturality (α.hom.app P)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn1 hn2
    simp only [Category.assoc]
    rw [← TC.map_comp_assoc, ← FA P, TC.map_comp_assoc, TC.map_comp_assoc, hn2,
      ← reassoc_of% hn1, ← reassoc_of% (F21 (cO1.obj P)), ← C2.map_comp_assoc,
      ← C2.map_comp_assoc, Category.assoc, ← F10 P]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hκ2 (γ10.hom.app P))]
  rw [hL, hR]
  simp only [← QC.map_comp]
  rw [hchain]

/-- A tower identity of natural isomorphisms that holds on the image of a localization
functor holds everywhere.
Source: Stacks 05Q2 (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem tower_of_localization {KA DA DB DC : Type*} [Category KA] [Category DA]
    [Category DB] [Category DC] (Λ : KA ⥤ DA) (W : MorphismProperty KA) [Λ.IsLocalization W]
    (TA : DA ⥤ DA) (TB : DB ⥤ DB) (TC : DC ⥤ DC)
    (C1 : DA ⥤ DB) (C2 : DB ⥤ DC) (C3 : DA ⥤ DC)
    (D10 : TA ⋙ C1 ≅ C1 ⋙ TB) (D21 : TB ⋙ C2 ≅ C2 ⋙ TC) (D20 : TA ⋙ C3 ≅ C3 ⋙ TC)
    (A : C1 ⋙ C2 ≅ C3)
    (h : ∀ P, C2.map (D10.hom.app (Λ.obj P)) ≫ D21.hom.app (C1.obj (Λ.obj P)) ≫
        TC.map (A.hom.app (Λ.obj P)) =
      A.hom.app (TA.obj (Λ.obj P)) ≫ D20.hom.app (Λ.obj P)) (K : DA) :
    C2.map (D10.hom.app K) ≫ D21.hom.app (C1.obj K) ≫ TC.map (A.hom.app K) =
      A.hom.app (TA.obj K) ≫ D20.hom.app K := by
  let τ : (TA ⋙ C1) ⋙ C2 ⟶ C3 ⋙ TC :=
    Functor.whiskerRight D10.hom C2 ≫ Functor.whiskerLeft C1 D21.hom ≫
      Functor.whiskerRight A.hom TC
  let τ' : (TA ⋙ C1) ⋙ C2 ⟶ C3 ⋙ TC := Functor.whiskerLeft TA A.hom ≫ D20.hom
  exact NatTrans.congr_app (Localization.natTrans_ext Λ W (τ := τ) (τ' := τ') h) K

section ChainTower

attribute [local semireducible] completedOrdinaryScalarComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chain-level tower identity, termwise `sheaf_tower`.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem chain_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
            max u (t + 1)} (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    {d10 : PairData l E X F ι L N} {d21 : PairData l F X G j N P}
    {d20 : PairData l E X G (j.comp ι) L P}
    (h10 : IsPairNormalized l E X F ι L N b10 d10)
    (h21 : IsPairNormalized l F X G j N P b21 d21)
    (h20 : IsPairNormalized l E X G (j.comp ι) L P b20 d20)
    (m : ℤ) (Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedOrdinaryScalarComplex l F G j X).map
        ((comparisonComplex l E X F ι L N m (d10.ordinarySheaf m)).hom.app Q) ≫
      (comparisonComplex l F X G j N P m (d21.ordinarySheaf m)).hom.app
        ((completedOrdinaryScalarComplex l E F ι X).obj Q) ≫
      (complex l G X P m).map ((scalarAssociatorComplex l E X F ι G j
        (associatorData l E X F ι G j).sheaf).hom.app Q) =
    (scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf).hom.app
        ((complex l E X L m).obj Q) ≫
      (comparisonComplex l E X G (j.comp ι) L P m (d20.ordinarySheaf m)).hom.app Q := by
  ext i : 1
  simp only [HomologicalComplex.comp_f]
  exact sheaf_tower l E X F ι G j L N P b10 b21 b20 hb h10 h21 h20 m (Q.X i)

end ChainTower

/-- The counit normalization of normalized data holds on every complex.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem pairData_counit {L : integralTowerModules l E X} [L.IsFiniteLocallyFreeOfRank 1]
    {N : integralTowerModules l F X} [N.IsFiniteLocallyFreeOfRank 1]
    {b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N}
    {d : PairData l E X F ι L N} (hd : IsPairNormalized l E X F ι L N b d) (m : ℤ)
    (Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedDerivedScalarExtension l E F ι X).map ((factors l E X L m).hom.app Q) ≫
        completedScalarCounit l E F ι X ((complex l E X L m).obj Q) ≫
        DerivedCategory.Q.map
          ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app Q) =
      (d.ordinary m).hom.app (DerivedCategory.Q.obj Q) ≫
        (tensor l F X N m).map (completedScalarCounit l E F ι X Q) ≫
        (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj Q) := by
  obtain ⟨d0, h0, hf⟩ := pairData_exists l E X F ι L N b
  obtain rfl := pairData_unique l E X F ι L N b h0 hd
  exact hf m Q

/-- The ordinary derived line comparisons commute with the ordinary associator.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf paths send t tensor (s tensor (x tensor a)) to
(t j(s) tensor x) tensor b_20(1 tensor a), by `line_tower`. The counit normalizations of
the line comparisons (on every complex) and of the associator transport this termwise
identity to the derived identity on good complexes; localization concludes. -/
theorem pairData_ordinary_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
            max u (t + 1)} (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    {d10 : PairData l E X F ι L N} {d21 : PairData l F X G j N P}
    {d20 : PairData l E X G (j.comp ι) L P}
    (h10 : IsPairNormalized l E X F ι L N b10 d10)
    (h21 : IsPairNormalized l F X G j N P b21 d21)
    (h20 : IsPairNormalized l E X G (j.comp ι) L P b20 d20)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l F G j X).map ((d10.ordinary m).hom.app K) ≫
      (d21.ordinary m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) ≫
      (tensor l G X P m).map ((associatorData l E X F ι G j).derived.hom.app K) =
    (associatorData l E X F ι G j).derived.hom.app ((tensor l E X L m).obj K) ≫
      (d20.ordinary m).hom.app K := by
  have hP (Q : CochainComplex (integralTowerModules l E X) ℤ) :
      (completedDerivedScalarExtension l F G j X).map
          ((d10.ordinary m).hom.app (DerivedCategory.Q.obj Q)) ≫
        (d21.ordinary m).hom.app
          ((completedDerivedScalarExtension l E F ι X).obj (DerivedCategory.Q.obj Q)) ≫
        (tensor l G X P m).map
          ((associatorData l E X F ι G j).derived.hom.app (DerivedCategory.Q.obj Q)) =
      (associatorData l E X F ι G j).derived.hom.app
          ((tensor l E X L m).obj (DerivedCategory.Q.obj Q)) ≫
        (d20.ordinary m).hom.app (DerivedCategory.Q.obj Q) :=
    derived_tower_of_formulas
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (complex l E X L m) (complex l F X N m) (complex l G X P m)
      (tensor l E X L m) (tensor l F X N m) (tensor l G X P m)
      (completedOrdinaryScalarComplex l E F ι X) (completedOrdinaryScalarComplex l F G j X)
      (completedOrdinaryScalarComplex l E G (j.comp ι) X)
      (completedDerivedScalarExtension l E F ι X) (completedDerivedScalarExtension l F G j X)
      (completedDerivedScalarExtension l E G (j.comp ι) X)
      (factors l E X L m) (factors l F X N m) (factors l G X P m)
      (completedScalarCounit l E F ι X) (completedScalarCounit l F G j X)
      (completedScalarCounit l E G (j.comp ι) X) (counit_naturality l F X G j)
      (d10.ordinary m) (d21.ordinary m) (d20.ordinary m) (associatorData l E X F ι G j).derived
      (comparisonComplex l E X F ι L N m (d10.ordinarySheaf m))
      (comparisonComplex l F X G j N P m (d21.ordinarySheaf m))
      (comparisonComplex l E X G (j.comp ι) L P m (d20.ordinarySheaf m))
      (scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf)
      (pairData_counit l E X F ι h10 m) (pairData_counit l F X G j h21 m)
      (pairData_counit l E X G (j.comp ι) h20 m)
      (associatorData_derived_normalized l E X F ι G j)
      (chain_tower l E X F ι G j L N P b10 b21 b20 hb h10 h21 h20 m)
      (finiteFreeScalarCochainProperties l E G (j.comp ι) X).2.2 Q
  exact tower_of_localization DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (tensor l E X L m) (tensor l F X N m) (tensor l G X P m)
    (completedDerivedScalarExtension l E F ι X) (completedDerivedScalarExtension l F G j X)
    (completedDerivedScalarExtension l E G (j.comp ι) X) (d10.ordinary m) (d21.ordinary m)
    (d20.ordinary m) (associatorData l E X F ι G j).derived hP K

end CompletedLineTensor
end WeilConjectures
