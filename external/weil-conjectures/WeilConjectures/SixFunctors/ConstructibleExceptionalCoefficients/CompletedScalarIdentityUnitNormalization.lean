/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ScalarIdentityComplexFormula

/-! # Comparison of native and completed ordinary scalar identity units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
attribute [local instance 6000] SheafOfModules.instAbelian
attribute [local instance 7000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Fix the native small-site universe for the completed scalar identity calculation.
Source: Mathlib `essentiallySmallSelf`.
(blueprint: lem-sf-completed-scalar-identity-unit-normalization). -/
local instance (priority := 10000) completedScalarIdentitySiteSmall (T : Scheme.{w}) :
    EssentiallySmall.{w + 1} T.ProEt := essentiallySmallSelf.{0, w, w + 1} _

private theorem tensor_section_model (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (M : integralTowerModules l E T) (U : T.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) (x : M.val.obj U) :
    pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T) M U s x =
      completedScalarTensorSection l E E (AlgHom.id (Padic l) E) T M U s x := by
  rfl

attribute [local instance 5000] proEtaleRingModules_hasDerivedCategory

private theorem native_counit_normalized {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) (a : R ⟶ R)
    (P : CochainComplex (pbcModules T R) ℤ) :
    pbcComplexCounit a P =
      (pbcExtensionCounit a).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  simp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors]
  erw [(pbcDerivedExtend a).map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]

private structure ScalarComplexData {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (L : A ⥤ A) [L.Additive] where
  derived : DerivedCategory A ⥤ DerivedCategory A
  counit : ∀ P : CochainComplex A ℤ, derived.obj (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P)

private def dataFormula {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {L : A ⥤ A} [L.Additive] (m : ScalarComplexData L)
    (μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (e : m.derived ≅ 𝟭 (DerivedCategory A)) : Prop :=
  ∀ P : CochainComplex A ℤ, e.hom.app (DerivedCategory.Q.obj P) =
    m.counit P ≫
      DerivedCategory.Q.map (μ.hom.app P)

private theorem dataFormula_transport {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {L L' : A ⥤ A} [L.Additive] [L'.Additive]
    (hL : L = L') {m : ScalarComplexData L} {m' : ScalarComplexData L'}
    (hm : HEq m m')
    {μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ)}
    {μ' : L'.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ)}
    {e : m.derived ≅ 𝟭 (DerivedCategory A)} {e' : m'.derived ≅ 𝟭 (DerivedCategory A)}
    (hμ : HEq μ μ') (he : HEq e e') : dataFormula m μ e → dataFormula m' μ' e' := by
  subst L'
  cases eq_of_heq hm
  cases eq_of_heq hμ
  cases eq_of_heq he
  exact id

private theorem dataFormula_of_representative {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {L : A ⥤ A} [L.Additive]
    (m : ScalarComplexData L)
    (c : ∀ P : CochainComplex A ℤ, m.derived.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (e : m.derived ≅ 𝟭 (DerivedCategory A))
    (hc : ∀ P, c P = m.counit P)
    (he : scalarComplexRepresentativeFormula L m.derived c μ e) :
    dataFormula m μ e := by
  intro P
  exact (he P).trans (congrArg (fun f ↦ f ≫ DerivedCategory.Q.map (μ.hom.app P)) (hc P))

private theorem dataFormula_representative {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {L : A ⥤ A} [L.Additive] (m : ScalarComplexData L)
    (μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (e : m.derived ≅ 𝟭 (DerivedCategory A)) (h : dataFormula m μ e) :
    scalarComplexRepresentativeFormula L m.derived m.counit μ e := h

private theorem unitor_unique {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (L : A ⥤ A) [L.Additive] (F : DerivedCategory A ⥤ DerivedCategory A)
    (c : ∀ P : CochainComplex A ℤ, F.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (good : ObjectProperty (CochainComplex A ℤ))
    (hu : ∃! e : F ≅ 𝟭 (DerivedCategory A), ∀ P : good.FullSubcategory,
      e.hom.app (DerivedCategory.Q.obj P.obj) = c P.obj ≫
        DerivedCategory.Q.map (μ.hom.app P.obj))
    (e e₀ : F ≅ 𝟭 (DerivedCategory A))
    (he : scalarComplexRepresentativeFormula L F c μ e)
    (h₀ : e₀ = hu.exists.choose) : e = e₀ := by
  rw [h₀]
  apply hu.unique
  · intro P
    exact he P.obj
  · exact hu.exists.choose_spec

private def nativeData {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) (a : R ⟶ R) :
    ScalarComplexData (A := pbcModules T R) (pbcExtend a) where
  derived := pbcDerivedExtend a
  counit := pbcComplexCounit a

private def nativeNormalizedData {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) (a : R ⟶ R) :
    ScalarComplexData (A := pbcModules T R) (pbcExtend a) where
  derived := pbcDerivedExtend a
  counit P := (pbcExtensionCounit a).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

private theorem nativeData_eq {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) (a : R ⟶ R) :
    nativeData R a = nativeNormalizedData R a := by
  exact congrArg (fun c ↦ (ScalarComplexData.mk (pbcDerivedExtend a) c))
    (funext (native_counit_normalized R a))

private theorem native_formula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (a : R ⟶ R) (ha : a = 𝟙 R)
    (μ : (pbcExtend a).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (pbcModules T R) ℤ))
    (hμ : ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection a (P.X i) U 1 x) = x) :
    dataFormula (nativeData R a) μ
      (eqToIso (congrArg pbcDerivedExtend ha) ≪≫ PurCompactSupport.tensorIdentity R) := by
  have : EssentiallySmall.{w + 1} T.ProEt := essentiallySmallSelf.{0, w, w + 1} _
  exact dataFormula_of_representative (nativeData R a) (pbcComplexCounit a) μ _
    (fun _ ↦ rfl) (scalar_identity_complex_formula R a ha μ hμ)

private theorem multiplication_one (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (P : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) :
    (((completedScalarIdentityMultiplication l E T).hom.app P).f i).val.app U
      (pbcTensorSection (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T)
        (P.X i) U 1 x) = x := by
  rw [tensor_section_model]
  unfold completedScalarIdentityMultiplication
  have hh := (completedScalarIdentityMultiplication_existsUnique l E T).exists.choose_spec
    P i U 1 x
  rw [one_smul] at hh
  exact hh

attribute [local irreducible] Functor.mapHomologicalComplex DerivedCategory.Q

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted DerivedCategory.Qh

attribute [local instance 8000] integralTowerHasDerivedCategory

private def completedData (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w}) :
    ScalarComplexData (A := integralTowerModules l E T)
      (completedOrdinaryScalarExtension l E E (AlgHom.id (Padic l) E) T) where
  derived := completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) T
  counit := completedScalarCounit l E E (AlgHom.id (Padic l) E) T

private theorem complexData_eq (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w}) :
    nativeData (completedIntegralCommRingSheafUnrestricted l E T)
      (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T) =
      completedData l E T := by
  rw [nativeData_eq]
  unfold nativeNormalizedData completedData completedScalarCounit
    pbcDerivedExtend reductionDerivedChange
    completedAdicDerivedChange pbcExtensionCounit reductionDerivedCounit
    completedDerivedScalarExtension completedScalarChangeData completedAdicChangeData
  with_unfolding_all rfl

private theorem extension_models_eq (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w}) :
    (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T) :
      DerivedCategory (integralTowerModules l E T) ⥤
        DerivedCategory (integralTowerModules l E T)) =
      completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) T := by
  unfold pbcDerivedExtend reductionDerivedChange completedAdicDerivedChange
    completedAdicChangeData completedDerivedScalarExtension completedScalarChangeData
  rfl

private theorem ordinary_models_eq (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w}) :
    pbcExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T) =
      completedOrdinaryScalarExtension l E E (AlgHom.id (Padic l) E) T := by
  unfold pbcExtend reductionChange completedAdicChange completedAdicChangeData
    completedOrdinaryScalarExtension completedScalarChangeData
  rfl

private def pbc_unit_candidate (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : completedCoefficientMap l E E (AlgHom.id (Padic l) E) T = 𝟙 _) :
    pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T) ≅
      𝟭 (DerivedCategory (pbcModules T
        (completedIntegralCommRingSheafUnrestricted l E T))) :=
  eqToIso (congrArg pbcDerivedExtend ha) ≪≫ PurCompactSupport.tensorIdentity
    (completedIntegralCommRingSheafUnrestricted l E T)

private def completed_unit_candidate (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : completedCoefficientMap l E E (AlgHom.id (Padic l) E) T = 𝟙 _) :
    completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) T ≅
      𝟭 (DerivedCategory (integralTowerModules l E T)) := by
  let z := pbc_unit_candidate l E T ha
  rw [← extension_models_eq l E T]
  exact z

private theorem candidate_eq (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : completedCoefficientMap l E E (AlgHom.id (Padic l) E) T = 𝟙 _) :
    pbc_unit_candidate l E T ha = completed_unit_candidate l E T ha := by
  rfl

attribute [local irreducible] completed_unit_candidate

private theorem completed_unit_normalization (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : completedCoefficientMap l E E (AlgHom.id (Padic l) E) T = 𝟙 _) :
    completed_unit_candidate l E T ha = CompletedLineTensor.ordinaryUnit l E T := by
  have hh := native_formula (completedIntegralCommRingSheafUnrestricted l E T) _ ha
    (completedScalarIdentityMultiplication l E T) (multiplication_one l E T)
  change dataFormula
    (nativeData (completedIntegralCommRingSheafUnrestricted l E T)
      (completedCoefficientMap l E E (AlgHom.id (Padic l) E) T))
    (completedScalarIdentityMultiplication l E T) (pbc_unit_candidate l E T ha) at hh
  have hh' : dataFormula (completedData l E T)
      (completedScalarIdentityMultiplication l E T) (completed_unit_candidate l E T ha) :=
    dataFormula_transport (ordinary_models_eq l E T)
      (heq_of_eq (complexData_eq l E T)) (HEq.refl _)
      (heq_of_eq (candidate_eq l E T ha)) hh
  exact unitor_unique
    (completedOrdinaryScalarExtension l E E (AlgHom.id (Padic l) E) T)
    (completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) T)
    (completedScalarCounit l E E (AlgHom.id (Padic l) E) T)
    (completedScalarIdentityMultiplication l E T) (integralOperationsGoodComplex l E T)
    (CompletedLineTensor.ordinaryUnit_existsUnique l E T) _ _
    (dataFormula_representative _ _ _ hh') rfl

private theorem multiplication_unit (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : completedCoefficientMap l E E (AlgHom.id (Padic l) E) T = 𝟙 _) :
    pbc_unit_candidate l E T ha = CompletedLineTensor.ordinaryUnit l E T := by
  exact (candidate_eq l E T ha).trans (completed_unit_normalization l E T ha)

private def scalar_unit_candidate {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) (a : R ⟶ R) (ha : a = 𝟙 R) :
    pbcDerivedExtend a ≅ 𝟭 (DerivedCategory (pbcModules T R)) :=
  eqToIso (congrArg pbcDerivedExtend ha) ≪≫ PurCompactSupport.tensorIdentity R

private theorem scalar_unit_candidate_model (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : (PurCompactSupport.completedChange l E E (AlgHom.id (Padic l) E)).map T = 𝟙 _) :
    scalar_unit_candidate ((PurCompactSupport.completed l E).ring T)
      ((PurCompactSupport.completedChange l E E (AlgHom.id (Padic l) E)).map T) ha =
        pbc_unit_candidate l E T ha := by
  rfl

/-- The two ordinary derived scalar-extension presentations use the same universal data.
Source: Stacks Project Tag 06YY.
(blueprint: lem-sf-completed-scalar-identity-unit-normalization)

Proof: unfold both scalar-change presentations. They select the same derived extension
from the same universal change-of-rings witness. -/
theorem completed_scalar_identity_extension_eq (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w}) :
    pbcDerivedExtend ((PurCompactSupport.completedChange l E E
      (AlgHom.id (Padic l) E)).map T) =
        completedDerivedScalarExtension l E E (AlgHom.id (Padic l) E) T := by
  exact extension_models_eq l E T

/-- The adjunction-normalized scalar identity is the ordinary completed-coefficient unitor.
Source: Stacks Project Tags 03DA and 06YY.
(blueprint: lem-sf-completed-scalar-identity-unit-normalization)

Proof: the sectionwise multiplication sends 1 tensor x to x. Apply the derived complex
representative formula. The two scalar-extension presentations select the same universal
functor and counit; compare this pair before taking components. Uniqueness of the ordinary
unitor with its prescribed complex representatives then gives the equality. -/
theorem completed_scalar_identity_unit_normalization (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : (PurCompactSupport.completedChange l E E (AlgHom.id (Padic l) E)).map T = 𝟙 _) :
    HEq (eqToIso (congrArg pbcDerivedExtend ha) ≪≫
      PurCompactSupport.tensorIdentity ((PurCompactSupport.completed l E).ring T))
      (CompletedLineTensor.ordinaryUnit l E T) := by
  have hh := (scalar_unit_candidate_model l E T ha).trans (multiplication_unit l E T ha)
  have hh' := heq_of_eq hh
  exact hh'

/-- The arrow specified by identity scalar normalization, with the cast kept bundled.
Source: identity coefficient normalization, Stacks Project Tag 06YY.
(blueprint: lem-sf-completed-scalar-identity-unit-normalization). -/
def normalizedScalarIdentityArrow {D : Type*} [Category D] {F G : D ⥤ D}
    (h : F = G) (v : G ≅ 𝟭 D) (K : D) : F.obj K ⟶ K :=
  (eqToIso h).hom.app K ≫ v.hom.app K

private theorem unitor_hom_heq {D : Type*} [Category D] {F G : D ⥤ D}
    (hFG : F = G) (u : F ≅ 𝟭 D) (v : G ≅ 𝟭 D) (huv : HEq u v)
    (K K' : D) (hK : K = K') : HEq (u.hom.app K) (v.hom.app K') := by
  subst G
  subst K'
  cases eq_of_heq huv
  exact HEq.rfl

private theorem normalized_arrow_heq {D : Type*} [Category D] {F F' G : D ⥤ D}
    (h : F = F') (v : F' ≅ 𝟭 D) (j : G ≅ 𝟭 D) (hFG : F = G)
    (hu : HEq (eqToIso h ≪≫ v) j) (K K' : D) (hK : K = K') :
    HEq (normalizedScalarIdentityArrow h v K) (j.hom.app K') := by
  exact unitor_hom_heq hFG (eqToIso h ≪≫ v) j hu K K' hK

/-- The bundled native identity arrow is the completed ordinary unitor component.
Source: Stacks Project Tag 06YY.
(blueprint: lem-sf-completed-scalar-identity-unit-normalization)

Proof: evaluate the equality of normalized unitors at the same derived object, retaining
its source transport as heterogeneous equality. -/
theorem completed_scalar_identity_arrow_normalization (l : ℕ) [Fact l.Prime]
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{w})
    (ha : (PurCompactSupport.completedChange l E E (AlgHom.id (Padic l) E)).map T = 𝟙 _)
    (K : DerivedCategory (integralTowerModules l E T)) :
    HEq (normalizedScalarIdentityArrow (congrArg pbcDerivedExtend ha)
      (PurCompactSupport.tensorIdentity ((PurCompactSupport.completed l E).ring T)) K)
      ((CompletedLineTensor.ordinaryUnit l E T).hom.app K) := by
  exact normalized_arrow_heq (congrArg pbcDerivedExtend ha)
    (PurCompactSupport.tensorIdentity ((PurCompactSupport.completed l E).ring T))
    (CompletedLineTensor.ordinaryUnit l E T)
    (completed_scalar_identity_extension_eq l E T)
    (completed_scalar_identity_unit_normalization l E T ha) K K rfl

end WeilConjectures.ConstructibleExceptionalCoefficients
