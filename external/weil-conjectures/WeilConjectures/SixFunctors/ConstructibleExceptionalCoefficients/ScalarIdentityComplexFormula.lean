/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarComplexAdjunctionNormalization
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedIdentityInverseRepresentative

/-! # Chain representative of the derived scalar identity -/

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

private theorem unitor_transpose {D : Type*} [Category D]
    {L R : D ⥤ D} (adj : L ⊣ R) (r : R ≅ 𝟭 D) (K : D) :
    adj.homEquiv K K (((conjugateIsoEquiv adj Adjunction.id).symm r).inv.app K) =
      r.inv.app K := by
  have hh := unit_conjugateEquiv_symm (Adjunction.id : 𝟭 D ⊣ 𝟭 D) adj r.inv K
  simp only [Adjunction.id, Functor.id_obj, NatTrans.id_app, Category.id_comp] at hh
  exact hh.symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem ordinary_unit_section {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction (𝟙 R)).unit.app M).val.app U x =
      pbcTensorSection (𝟙 R) M U 1 x := by
  unfold pbcScalarAdjunction
  exact (pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec M U x

private theorem ordinary_transpose {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (μ : (pbcExtend (𝟙 R)).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (pbcModules T R) ℤ))
    (hμ : ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection (𝟙 R) (P.X i) U 1 x) = x)
    (P : CochainComplex (pbcModules T R) ℤ) :
    ((pbcScalarAdjunction (𝟙 R)).mapHomologicalComplex (.up ℤ)).homEquiv P P (μ.hom.app P) =
      (NatTrans.mapHomologicalComplex
        (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose.inv (.up ℤ)).app P := by
  ext i U x
  change ((μ.hom.app P).f i).val.app U
    (((pbcScalarAdjunction (𝟙 R)).unit.app (P.X i)).val.app U x) = _
  erw [ordinary_unit_section, hμ]
  let r := (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
  have hr := (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
  have hi := congrArg (fun f ↦ f.val.app U x) (r.inv_hom_id_app (P.X i))
  change x = (r.inv.app (P.X i)).val.app U x
  change (r.hom.app (P.X i)).val.app U ((r.inv.app (P.X i)).val.app U x) = x at hi
  have hr' : ∀ M U x, (r.hom.app M).val.app U x = x := hr
  erw [hr'] at hi
  exact hi.symm

private structure ScalarIdentityModel
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (L R : A ⥤ A) [L.Additive] [R.Additive] where
  leftDerived : DerivedCategory A ⥤ DerivedCategory A
  rightDerived : DerivedCategory A ⥤ DerivedCategory A
  adj : leftDerived ⊣ rightDerived
  rightIso : rightDerived ≅ 𝟭 (DerivedCategory A)
  comparison : DerivedCategory.Q ⋙ rightDerived ≅
    R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  counit : ∀ P : CochainComplex A ℤ,
    leftDerived.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] pbcDerivedScalarAdjunction pbcComplexCounit
  reductionDerivedChange completedAdicDerivedChange reductionChange completedAdicChange
attribute [local instance 5000] proEtaleRingModules_hasDerivedCategory

/-- Fix the native site universe while computing the scalar identity representative.
Source: Mathlib `essentiallySmallSelf`.
(blueprint: lem-sf-scalar-identity-complex-formula). -/
local instance (priority := 10000) scalarIdentitySiteSmall (T : Scheme.{w}) :
    EssentiallySmall.{w + 1} T.ProEt := essentiallySmallSelf.{0, w, w + 1} _

private def old_model {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    ScalarIdentityModel (A := pbcModules T R) (pbcExtend (𝟙 R)) (pbcRestrict (𝟙 R)) where
  leftDerived := pbcDerivedExtend (𝟙 R)
  rightDerived := pbcDerivedRestrict (𝟙 R)
  adj := pbcDerivedScalarAdjunction (𝟙 R)
  rightIso := Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
    Functor.mapDerivedCategoryIdIso _
  comparison := (pbcRestrict (𝟙 R)).mapDerivedCategoryFactors
  counit := pbcComplexCounit (𝟙 R)

private def new_model {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    ScalarIdentityModel (A := pbcModules T R) (pbcExtend (𝟙 R)) (pbcRestrict (𝟙 R)) where
  leftDerived := pbcDerivedExtend (𝟙 R)
  rightDerived := Functor.mapDerivedCategory (C₁ := pbcModules T R) (C₂ := pbcModules T R)
    (pbcRestrict (𝟙 R))
  adj := pbcDerivedScalarAdjunction (𝟙 R)
  rightIso := Functor.mapDerivedCategoryNatIso (C := pbcModules T R)
      (D := pbcModules T R) (G := 𝟭 (pbcModules T R))
      (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
    Functor.mapDerivedCategoryIdIso (pbcModules T R)
  comparison := Functor.mapDerivedCategoryFactors (C₁ := pbcModules T R)
    (C₂ := pbcModules T R) (pbcRestrict (𝟙 R))
  counit := pbcComplexCounit (𝟙 R)

private theorem models_equal {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) : old_model R = new_model R := by
  rfl

private def modelUnit {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {L R : A ⥤ A} [L.Additive] [R.Additive] (m : ScalarIdentityModel L R) :
    m.leftDerived ≅ 𝟭 (DerivedCategory A) :=
  ((conjugateIsoEquiv m.adj Adjunction.id).symm m.rightIso).symm

private def rightFormula {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {L R : A ⥤ A} [L.Additive] [R.Additive] (r : R ≅ 𝟭 A)
    (m : ScalarIdentityModel L R) : Prop :=
  ∀ P : CochainComplex A ℤ,
    m.rightIso.inv.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.inv (.up ℤ)).app P) ≫
        m.comparison.inv.app P

private theorem new_rightFormula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    rightFormula (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
      (new_model R) := by
  intro P
  exact Adjunction.mapDerivedCategoryNatIso_trans_idIso_inv_app_Q_obj
    (D := pbcModules T R) (pbcRestrict (𝟙 R)) _ P

private theorem old_rightFormula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    rightFormula (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
      (old_model R) := by
  rw [models_equal]
  exact new_rightFormula R

private theorem modelUnit_old {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    modelUnit (old_model R) = PurCompactSupport.tensorIdentity R := by
  rfl

private theorem model_formula {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {L R : A ⥤ A} [L.Additive] [R.Additive] (m : ScalarIdentityModel L R)
    (P : CochainComplex A ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ P)
    (g : P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj P)
    (ht : m.adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P)
      (m.counit P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map g ≫ m.comparison.inv.app P)
    (hi : m.rightIso.inv.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map g ≫ m.comparison.inv.app P) :
    (modelUnit m).hom.app (DerivedCategory.Q.obj P) =
      m.counit P ≫ DerivedCategory.Q.map f := by
  apply (m.adj.homEquiv _ _).injective
  exact (unitor_transpose m.adj m.rightIso _).trans (hi.trans ht.symm)

private def scalarFormula {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {L R : A ⥤ A} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (m : ScalarIdentityModel L R) : Prop :=
  ∀ (P K : CochainComplex A ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    m.adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (m.counit P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          m.comparison.inv.app K

private theorem old_scalarFormula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1}) :
    scalarFormula (pbcScalarAdjunction (𝟙 R)) (old_model R) := by
  intro P K f
  exact PurCompactSupport.scalarComplexTranspose (𝟙 R) P K f

private theorem identity_formula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (μ : (pbcExtend (𝟙 R)).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (pbcModules T R) ℤ))
    (hμ : ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection (𝟙 R) (P.X i) U 1 x) = x)
    (P : CochainComplex (pbcModules T R) ℤ) :
    (modelUnit (old_model R)).hom.app (DerivedCategory.Q.obj P) =
      pbcComplexCounit (𝟙 R) P ≫ DerivedCategory.Q.map (μ.hom.app P) := by
  have ho := ordinary_transpose R μ hμ P
  have ht := old_scalarFormula R P P (μ.hom.app P)
  rw [ho] at ht
  exact model_formula (old_model R) P (μ.hom.app P) _ ht (old_rightFormula R P)

/-- The representative equation for a derived isomorphism and a fixed complex counit.
Source: Stacks Project Tag 06YY.
(blueprint: lem-sf-scalar-identity-complex-formula). -/
def scalarComplexRepresentativeFormula {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (L : A ⥤ A) [L.Additive]
    (F : DerivedCategory A ⥤ DerivedCategory A)
    (c : ∀ P : CochainComplex A ℤ, F.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : L.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (e : F ≅ 𝟭 (DerivedCategory A)) : Prop :=
  ∀ P : CochainComplex A ℤ, e.hom.app (DerivedCategory.Q.obj P) =
    c P ≫ DerivedCategory.Q.map (μ.hom.app P)

private theorem transport_formula {I A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (L : I → A ⥤ A) [∀ i, (L i).Additive]
    (F : I → DerivedCategory A ⥤ DerivedCategory A)
    (c : ∀ i (P : CochainComplex A ℤ), (F i).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((L i).mapHomologicalComplex (.up ℤ)).obj P))
    (cond : ∀ i, ((L i).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex A ℤ)) → Prop)
    {i j : I} (h : i = j) (e : F j ≅ 𝟭 (DerivedCategory A))
    (hj : ∀ μ, cond j μ → scalarComplexRepresentativeFormula (L j) (F j) (c j) μ e)
    (μ : (L i).mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex A ℤ))
    (hμ : cond i μ) :
    scalarComplexRepresentativeFormula (L i) (F i) (c i) μ (eqToIso (congrArg F h) ≪≫ e) := by
  subst j
  simpa only [eqToIso_refl, Iso.refl_trans] using hj μ hμ

private theorem tensor_identity_formula_of_eq {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (a : R ⟶ R) (ha : a = 𝟙 R)
    (μ : (pbcExtend a).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (pbcModules T R) ℤ))
    (hμ : ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection a (P.X i) U 1 x) = x) :
    scalarComplexRepresentativeFormula (pbcExtend a) (pbcDerivedExtend a) (pbcComplexCounit a) μ
      (eqToIso (congrArg pbcDerivedExtend ha) ≪≫ modelUnit (old_model R)) := by
  exact transport_formula (fun b : R ⟶ R ↦ pbcExtend b)
    (fun b : R ⟶ R ↦ pbcDerivedExtend b) (fun b ↦ pbcComplexCounit b)
    (fun b μ ↦ ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection b (P.X i) U 1 x) = x)
    ha (modelUnit (old_model R)) (fun μ hμ P ↦ identity_formula R μ hμ P) μ hμ

/-- The derived identity-scalar unitor is represented by the normalized chain multiplication.
Source: Stacks Project Tags 03DA and 06YY.
(blueprint: lem-sf-scalar-identity-complex-formula)

Proof: the ordinary adjunction sends multiplication to the inverse restriction identity,
since its unit sends x to 1 tensor x. The derived transpose theorem and the representative
formula for the exact-derived restriction identity give equal derived transposes. The
adjunction bijection is injective. Finally transport along the equality of coefficient maps. -/
theorem scalar_identity_complex_formula {T : Scheme.{w}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{w + 1})
    (a : R ⟶ R) (ha : a = 𝟙 R)
    (μ : (pbcExtend a).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (pbcModules T R) ℤ))
    (hμ : ∀ (P : CochainComplex (pbcModules T R) ℤ) (i : ℤ) (U : T.ProEtᵒᵖ)
      (x : (P.X i).val.obj U),
      ((μ.hom.app P).f i).val.app U (pbcTensorSection a (P.X i) U 1 x) = x)
    : scalarComplexRepresentativeFormula (pbcExtend a) (pbcDerivedExtend a)
      (pbcComplexCounit a) μ
        (eqToIso (congrArg pbcDerivedExtend ha) ≪≫ PurCompactSupport.tensorIdentity R) := by
  have hh := tensor_identity_formula_of_eq R a ha μ hμ
  rw [modelUnit_old] at hh
  exact hh

end WeilConjectures.ConstructibleExceptionalCoefficients
