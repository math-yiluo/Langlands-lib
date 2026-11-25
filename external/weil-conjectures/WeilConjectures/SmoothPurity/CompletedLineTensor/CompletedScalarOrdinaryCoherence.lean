/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SmoothPurity.CompletedScalarAssociator.CompletedScalarAssociator
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarIdentityUnit
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Ordinary scalar associators and units for completed coefficients

Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

The ordinary (uncompleted) derived scalar extensions along completed coefficient maps
carry an associator and a multiplication unitor, each fixed by its pure-tensor formula
and the universal K-flat counits. This file records them and proves their two unit laws
and the pentagon. The completed comparisons are obtained from them by conjugation in
`CompletedLineTensorCoherence`.

## Main definitions and statements

* `associatorData`, `ordinaryUnit`: the normalized ordinary associator and unitor.
* `associatorData_derived_source_unit`, `associatorData_derived_target_unit`:
  the two unit laws.
* `associatorData_derived_pentagon`: the pentagon.
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
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)


/-- Ordinary scalar associativity, fixed on sheafified tensors and universal K-flat counits.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData :=
  (completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X) ×
  (completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X)

variable {l E X F ι G j}

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.sheaf (d : AssociatorData l E X F ι G j) :
    completedOrdinaryScalarExtension l E F ι X ⋙
    completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X := d.1

/-- Projection of the canonical ordinary comparison package.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def AssociatorData.derived (d : AssociatorData l E X F ι G j) :
    completedDerivedScalarExtension l E F ι X ⋙
    completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X := d.2

variable (l E X F ι G j)

/-- Balanced-tensor multiplication and the universal-counit normalization.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsAssociatorNormalized (d : AssociatorData l E X F ι G j) : Prop :=
  (∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (x : M.val.obj U),
    (d.sheaf.hom.app M).val.app U
        (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
      completedScalarTensorSection l E G (j.comp ι) X M U
        (t * (completedCoefficientMap l F G j X).hom.app U s) x) ∧
  (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P.obj) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι G j d.sheaf).hom.app P.obj) =
      d.derived.hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E G (j.comp ι) X P.obj)

/-- Ordinary scalar associators with exactly the prescribed balanced normalization.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the balanced map t tensor (s tensor x) mapped to t*j(s) tensor x has inverse
u tensor x mapped to u tensor (1 tensor x). The two maps commute with restrictions
and differentials. Sheafification preserves their inverse equations. Ordinary extension
preserves flat-term K-flat complexes, so localization with the specified counits gives
the unique derived comparison. Local generation and the localization equivalence prove
uniqueness of the entire package. -/
theorem associatorData_existsUnique :
    ∃! a : AssociatorData l E X F ι G j, IsAssociatorNormalized l E X F ι G j a := by
  delta AssociatorData IsAssociatorNormalized AssociatorData.sheaf
    AssociatorData.derived scalarAssociatorComplex
  exact CompletedScalarAssociator.exists_unique l E X F ι G j

/-- The normalized ordinary scalar associator, including its representative.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
def associatorData : AssociatorData l E X F ι G j :=
  (associatorData_existsUnique l E X F ι G j).exists.choose

section DerivedUnitProof

/-- The ordinary derived multiplication unitor, fixed by the recorded chain unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: multiplication and x mapped to 1 tensor x are inverse on module sheaves.
They commute with differentials and restrictions. Localization with the canonical
K-flat counit gives the unique derived unitor with the displayed normalization. -/
theorem ordinaryUnit_existsUnique :
    ∃! e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        e.hom.app (DerivedCategory.Q.obj P.obj) =
          completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj ≫
            DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj) :=
              by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨e, he⟩ := ordinaryUnitOnComplexes_exists l E X
    refine ⟨e, fun P ↦ he P.obj, ?_⟩
    intro e' he'
    let Q := integralOperationsGoodLocalization l E X
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    have : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
    apply Iso.ext
    apply (Localization.fullyFaithfulWhiskeringLeft Q W _).map_injective
    apply NatTrans.ext
    funext P
    exact (he' P).trans (he P.obj).symm

end DerivedUnitProof

/-- The ordinary multiplication unitor with its prescribed representative.
Source: blueprint Proof (3) (blueprint: lem-pur-completed-line-tensor-coherence). -/
def ordinaryUnit :
    completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅
      𝟭 (DerivedCategory (integralTowerModules l E X)) :=
  (ordinaryUnit_existsUnique l E X).exists.choose

attribute [local irreducible] associatorData ordinaryUnit

/-- The derived associator normalization holds on every complex, not only on good ones.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the normalized associator is the one built from the composed extension-restriction
adjunctions, whose representative formula holds on all complexes; uniqueness identifies
it with `associatorData`. -/
theorem associatorData_derived_normalized
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf).hom.app P) =
      (associatorData l E X F ι G j).derived.hom.app (DerivedCategory.Q.obj P) ≫
        completedScalarCounit l E G (j.comp ι) X P := by
  obtain ⟨o, d, ho, hd, -, -⟩ := CompletedScalarAssociator.exists_normalized l E X F ι G j
  have hod : associatorData l E X F ι G j = (o, d) := by
    unfold associatorData
    refine (associatorData_existsUnique l E X F ι G j).unique
      (associatorData_existsUnique l E X F ι G j).exists.choose_spec ⟨ho, fun P ↦ ?_⟩
    convert hd P.obj using 0
    delta scalarAssociatorComplex completedOrdinaryScalarComplex
    rfl
  rw [hod]
  convert hd P using 0
  delta scalarAssociatorComplex completedOrdinaryScalarComplex
  rfl

/-- The ordinary unitor is multiplication after the universal counit, on every complex.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: `ordinaryUnitOnComplexes_exists` gives a unitor with this formula on all complexes;
it satisfies the good-complex normalization, so it is `ordinaryUnit` by uniqueness. -/
theorem ordinaryUnit_hom_app_Q (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P) =
      completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P ≫
        DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  obtain ⟨e, he⟩ := ordinaryUnitOnComplexes_exists l E X
  have hu : ordinaryUnit l E X = e := by
    unfold ordinaryUnit
    exact (ordinaryUnit_existsUnique l E X).unique
      (ordinaryUnit_existsUnique l E X).exists.choose_spec fun P ↦ he P.obj
  rw [hu, he]

section CounitNaturality

attribute [local semireducible] completedDerivedScalarExtension completedOrdinaryScalarExtension
  completedScalarCounit completedOrdinaryScalarComplex completedScalarChangeData

set_option backward.isDefEq.respectTransparency false in
/-- Universal counits commute with termwise ordinary extension of chain maps.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem counit_naturality {P P' : CochainComplex (integralTowerModules l E X) ℤ}
    (f : P ⟶ P') :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map f) ≫
        completedScalarCounit l E F ι X P' =
      completedScalarCounit l E F ι X P ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map f) := by
  dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
  with_unfolding_all
    exact homotopyCounit_naturality (completedOrdinaryScalarExtension l E F ι X)
      (completedDerivedScalarExtension l E F ι X)
      ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) f

end CounitNaturality

/-- Natural transformations out of a derived category agree once they agree on complexes.
Source: Stacks 05RU (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem derived_natTrans_app_eq {A D : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] [Category D] {F₁ F₂ : DerivedCategory A ⥤ D} (τ τ' : F₁ ⟶ F₂)
    (h : ∀ P, τ.app (DerivedCategory.Q.obj P) = τ'.app (DerivedCategory.Q.obj P))
    (K : DerivedCategory A) : τ.app K = τ'.app K :=
  congr_app (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) h) K

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
/-- Sheafified pure tensors are scalar multiples of `1 ⊗ x`.
Source: Stacks 03EL (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem changeOfRings_tensor_smul
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}}
    (φ : R ⟶ S)
    (M : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (A : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} φ M)
    (U : X.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) :=
    congrArg (· ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) (mul_one a).symm
  exact (congrArg k ht).trans (k.hom.map_smul a _)

set_option backward.isDefEq.respectTransparency false in
/-- A pure tensor `a ⊗ x` in an ordinary scalar extension is `a • (1 ⊗ x)`.
Source: Stacks 03EL (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem completedScalarTensorSection_smul (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection l E F ι X M U a x =
      a • completedScalarTensorSection l E F ι X M U 1 x := by
  unfold completedScalarTensorSection completedOrdinaryScalarExtension
  exact changeOfRings_tensor_smul X (completedCoefficientMap l E F ι X) M _
    ((completedScalarChangeData l E F ι X).choose_spec.choose M) U a x

/-- The normalized ordinary associator satisfies its defining normalization.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem associatorData_isNormalized :
    IsAssociatorNormalized l E X F ι G j (associatorData l E X F ι G j) := by
  unfold associatorData
  exact (associatorData_existsUnique l E X F ι G j).exists.choose_spec

/-- The ordinary associator sends `t ⊗ (s ⊗ x)` to `t*j(s) ⊗ x`.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem associatorData_sheaf_hom_tensor (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U) :
    ((associatorData l E X F ι G j).sheaf.hom.app M).val.app U
        (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
      completedScalarTensorSection l E G (j.comp ι) X M U
        (t * (completedCoefficientMap l F G j X).hom.app U s) x :=
  (associatorData_isNormalized l E X F ι G j).1 M U s t x

/-- The inverse ordinary associator sends `t ⊗ x` to `t ⊗ (1 ⊗ x)`.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem associatorData_sheaf_inv_tensor (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
    (x : M.val.obj U) :
    ((associatorData l E X F ι G j).sheaf.inv.app M).val.app U
        (completedScalarTensorSection l E G (j.comp ι) X M U t x) =
      completedScalarTensorSection l F G j X _ U t
        (completedScalarTensorSection l E F ι X M U 1 x) := by
  have h1 := associatorData_sheaf_hom_tensor l E X F ι G j M U 1 t x
  rw [map_one, mul_one] at h1
  rw [← h1]
  exact congrArg (fun φ ↦ φ.val.app U (completedScalarTensorSection l F G j X _ U t
    (completedScalarTensorSection l E F ι X M U 1 x)))
    ((associatorData l E X F ι G j).sheaf.hom_inv_id_app M)

set_option backward.isDefEq.respectTransparency false in
/-- With identity first step, an associator with the inverse tensor formula is the
extension of multiplication.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the inverse followed by the extended multiplication fixes every `t ⊗ x`. -/
private theorem sheaf_source_unit_aux
    (o : completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) X ⋙
      completedOrdinaryScalarExtension l E F ι X ≅ completedOrdinaryScalarExtension l E F ι X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.inv.app M).val.app U (completedScalarTensorSection l E F ι X M U t x) =
        completedScalarTensorSection l E F ι X _ U t
          (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X M U 1 x))
    (N : integralTowerModules l E X)
    (g : (completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) X).obj N ⟶ N)
    (hg : ∀ (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : N.val.obj U),
      g.val.app U (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X N U s x) = s • x) :
    o.hom.app N = (completedOrdinaryScalarExtension l E F ι X).map g := by
  have h : (o.app N).inv ≫ (completedOrdinaryScalarExtension l E F ι X).map g = 𝟙 _ := by
    apply completedScalar_tensor_ext l E F ι X
    intro U s x
    exact (congrArg (fun z ↦ ((completedOrdinaryScalarExtension l E F ι X).map g).val.app U z)
        (ho N U s x)).trans <|
      (completedScalarTensorSection_naturality l E F ι X g U s _).trans
        (congrArg (completedScalarTensorSection l E F ι X N U s) ((hg U 1 x).trans (one_smul _ x)))
  rw [Iso.inv_comp_eq, Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- With identity second step, an associator with the inverse tensor formula is
multiplication.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the inverse followed by multiplication sends `t ⊗ x` to `t • (1 ⊗ x) = t ⊗ x`. -/
private theorem sheaf_target_unit_aux
    (o : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅
        completedOrdinaryScalarExtension l E F ι X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.inv.app M).val.app U (completedScalarTensorSection l E F ι X M U t x) =
        completedScalarTensorSection l F F (AlgHom.id ℚ_[l] F) X _ U t
          (completedScalarTensorSection l E F ι X M U 1 x))
    (M : integralTowerModules l E X)
    (g : (completedOrdinaryScalarExtension l F F (AlgHom.id ℚ_[l] F) X).obj
      ((completedOrdinaryScalarExtension l E F ι X).obj M) ⟶
        (completedOrdinaryScalarExtension l E F ι X).obj M)
    (hg : ∀ (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (y : ((completedOrdinaryScalarExtension l E F ι X).obj M).val.obj U),
      g.val.app U (completedScalarTensorSection l F F (AlgHom.id ℚ_[l] F) X _ U s y) = s • y) :
    o.hom.app M = g := by
  have h : (o.app M).inv ≫ g = 𝟙 _ := by
    apply completedScalar_tensor_ext l E F ι X
    intro U s x
    exact (congrArg (fun z ↦ g.val.app U z) (ho M U s x)).trans <|
      (hg U s _).trans (completedScalarTensorSection_smul l E X F ι M U s x).symm
  rw [Iso.inv_comp_eq, Category.comp_id] at h
  exact h.symm

/-- Four associators with the balanced tensor formulas satisfy the pentagon on sheaves.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: precomposed with the inverse of the right route, the left route fixes `u ⊗ x`. -/
private theorem sheaf_pentagon_aux
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H) (ρ₁ : E →ₐ[ℚ_[l]] G) (ρ₂ : F →ₐ[ℚ_[l]] H) (ρ : E →ₐ[ℚ_[l]] H)
    (o₁ : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F G j X ≅ completedOrdinaryScalarExtension l E G ρ₁ X)
    (o₂ : completedOrdinaryScalarExtension l E G ρ₁ X ⋙
      completedOrdinaryScalarExtension l G H k X ≅ completedOrdinaryScalarExtension l E H ρ X)
    (o₃ : completedOrdinaryScalarExtension l F G j X ⋙
      completedOrdinaryScalarExtension l G H k X ≅ completedOrdinaryScalarExtension l F H ρ₂ X)
    (o₄ : completedOrdinaryScalarExtension l E F ι X ⋙
      completedOrdinaryScalarExtension l F H ρ₂ X ≅ completedOrdinaryScalarExtension l E H ρ X)
    (h₁ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o₁.hom.app M).val.app U (completedScalarTensorSection l F G j X _ U t
          (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G ρ₁ X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x)
    (h₂ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₂.hom.app M).val.app U (completedScalarTensorSection l G H k X _ U t
          (completedScalarTensorSection l E G ρ₁ X M U s x)) =
        completedScalarTensorSection l E H ρ X M U
          (t * (completedCoefficientMap l G H k X).hom.app U s) x)
    (h₃ : ∀ (N : integralTowerModules l F X) (U : X.ProEtᵒᵖ)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (y : N.val.obj U),
      (o₃.inv.app N).val.app U (completedScalarTensorSection l F H ρ₂ X N U t y) =
        completedScalarTensorSection l G H k X _ U t
          (completedScalarTensorSection l F G j X N U 1 y))
    (h₄ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₄.inv.app M).val.app U (completedScalarTensorSection l E H ρ X M U t x) =
        completedScalarTensorSection l F H ρ₂ X _ U t
          (completedScalarTensorSection l E F ι X M U 1 x))
    (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M) ≫ o₂.hom.app M =
      o₃.hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≫ o₄.hom.app M := by
  let a := o₃.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≪≫ o₄.app M
  have h : a.inv ≫ (completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M) ≫
      o₂.hom.app M = 𝟙 _ := by
    apply completedScalar_tensor_ext l E H ρ X
    intro U s x
    exact (congrArg (fun z ↦ (o₂.hom.app M).val.app U
        (((completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M)).val.app U
          ((o₃.inv.app _).val.app U z))) (h₄ M U s x)).trans <|
      (congrArg (fun z ↦ (o₂.hom.app M).val.app U
        (((completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M)).val.app U z))
          (h₃ _ U s _)).trans <|
      (congrArg (fun z ↦ (o₂.hom.app M).val.app U z)
        (completedScalarTensorSection_naturality l G H k X (o₁.hom.app M) U s _)).trans <|
      (congrArg (fun z ↦ (o₂.hom.app M).val.app U
        (completedScalarTensorSection l G H k X _ U s z)) (h₁ M U 1 1 x)).trans <|
      (h₂ M U _ s x).trans (congrArg (fun t ↦ completedScalarTensorSection l E H ρ X M U t x)
        (by rw [one_mul, map_one, map_one, mul_one]))
  rw [Iso.inv_comp_eq, Category.comp_id] at h
  exact h

section Chain

attribute [local semireducible] completedOrdinaryScalarComplex

/-- With identity first step, the termwise ordinary associator is the extension of
multiplication.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem scalarAssociatorComplex_source_unit
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (scalarAssociatorComplex l E X E (AlgHom.id ℚ_[l] E) F ι
        (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).sheaf).hom.app P =
      (completedOrdinaryScalarComplex l E F ι X).map
        ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  ext i : 1
  exact sheaf_source_unit_aux l E X F ι (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).sheaf
    (associatorData_sheaf_inv_tensor l E X E (AlgHom.id ℚ_[l] E) F ι) (P.X i)
    (((completedScalarIdentityMultiplication l E X).hom.app P).f i)
    (completedScalarIdentityMultiplication_spec l E X P i)

/-- With identity second step, the termwise ordinary associator is multiplication.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem scalarAssociatorComplex_target_unit
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (scalarAssociatorComplex l E X F ι F (AlgHom.id ℚ_[l] F)
        (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).sheaf).hom.app P =
      (completedScalarIdentityMultiplication l F X).hom.app
        ((completedOrdinaryScalarComplex l E F ι X).obj P) := by
  ext i : 1
  exact sheaf_target_unit_aux l E X F ι (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).sheaf
    (associatorData_sheaf_inv_tensor l E X F ι F (AlgHom.id ℚ_[l] F)) (P.X i)
    (((completedScalarIdentityMultiplication l F X).hom.app
      ((completedOrdinaryScalarComplex l E F ι X).obj P)).f i)
    (completedScalarIdentityMultiplication_spec l F X
      ((completedOrdinaryScalarComplex l E F ι X).obj P) i)

/-- The termwise ordinary associators satisfy the pentagon.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem scalarAssociatorComplex_pentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H) (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedOrdinaryScalarComplex l G H k X).map
        ((scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf).hom.app P) ≫
      (scalarAssociatorComplex l E X G (j.comp ι) H k
        (associatorData l E X G (j.comp ι) H k).sheaf).hom.app P =
    (scalarAssociatorComplex l F X G j H k (associatorData l F X G j H k).sheaf).hom.app
        ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
      (scalarAssociatorComplex l E X F ι H (k.comp j)
        (associatorData l E X F ι H (k.comp j)).sheaf).hom.app P := by
  ext i : 1
  exact sheaf_pentagon_aux l E X F ι G j H k (j.comp ι) (k.comp j) (k.comp (j.comp ι))
    (associatorData l E X F ι G j).sheaf (associatorData l E X G (j.comp ι) H k).sheaf
    (associatorData l F X G j H k).sheaf (associatorData l E X F ι H (k.comp j)).sheaf
    (associatorData_sheaf_hom_tensor l E X F ι G j)
    (associatorData_sheaf_hom_tensor l E X G (j.comp ι) H k)
    (associatorData_sheaf_inv_tensor l F X G j H k)
    (associatorData_sheaf_inv_tensor l E X F ι H (k.comp j)) (P.X i)

end Chain

/-- A derived associator normalized by the unitor's chain formula extends the unitor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: after the invertible counit both sides become the counits followed by the
termwise multiplication; localization extends the equality to all objects. -/
private theorem derived_source_unit_aux
    (d : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ⋙
      completedDerivedScalarExtension l E F ι X ≅ completedDerivedScalarExtension l E F ι X)
    (A : completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X ⋙
      completedOrdinaryScalarComplex l E F ι X ≅ completedOrdinaryScalarComplex l E F ι X)
    (hd : ∀ P, (completedDerivedScalarExtension l E F ι X).map
        (completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P) ≫
      completedScalarCounit l E F ι X
        ((completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X).obj P) ≫
      DerivedCategory.Q.map (A.hom.app P) =
        d.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E F ι X P)
    (hA : ∀ P, A.hom.app P = (completedOrdinaryScalarComplex l E F ι X).map
      ((completedScalarIdentityMultiplication l E X).hom.app P))
    (K : DerivedCategory (integralTowerModules l E X)) :
    d.hom.app K = (completedDerivedScalarExtension l E F ι X).map
      ((ordinaryUnit l E X).hom.app K) := by
  refine (derived_natTrans_app_eq d.hom
    (Functor.whiskerRight (ordinaryUnit l E X).hom (completedDerivedScalarExtension l E F ι X) ≫
      (Functor.leftUnitor (completedDerivedScalarExtension l E F ι X)).hom)
    (fun P ↦ ?_) K).trans (Category.comp_id _)
  have := (finiteFreeScalarCochainProperties l E F ι X).2.2 P
  have hn : (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map
        ((completedScalarIdentityMultiplication l E X).hom.app P)) ≫
      completedScalarCounit l E F ι X P =
      completedScalarCounit l E F ι X
          ((completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X).obj P) ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map
          ((completedScalarIdentityMultiplication l E X).hom.app P)) :=
    counit_naturality l E X F ι _
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id]
  rw [
    ← cancel_mono (completedScalarCounit l E F ι X P), ← hd, ordinaryUnit_hom_app_Q,
    Functor.map_comp, Category.assoc, hn, hA]

/-- A derived associator normalized by the unitor's chain formula is the unitor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: after the invertible counit, naturality of the unitor reduces both sides to the
counits followed by termwise multiplication; localization concludes. -/
private theorem derived_target_unit_aux
    (d : completedDerivedScalarExtension l E F ι X ⋙
      completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅
        completedDerivedScalarExtension l E F ι X)
    (A : completedOrdinaryScalarComplex l E F ι X ⋙
      completedOrdinaryScalarComplex l F F (AlgHom.id ℚ_[l] F) X ≅
        completedOrdinaryScalarComplex l E F ι X)
    (hd : ∀ P, (completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X).map
        (completedScalarCounit l E F ι X P) ≫
      completedScalarCounit l F F (AlgHom.id ℚ_[l] F) X
        ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
      DerivedCategory.Q.map (A.hom.app P) =
        d.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E F ι X P)
    (hA : ∀ P, A.hom.app P = (completedScalarIdentityMultiplication l F X).hom.app
      ((completedOrdinaryScalarComplex l E F ι X).obj P))
    (K : DerivedCategory (integralTowerModules l E X)) :
    d.hom.app K =
      (ordinaryUnit l F X).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) := by
  refine (derived_natTrans_app_eq d.hom
    (Functor.whiskerLeft (completedDerivedScalarExtension l E F ι X) (ordinaryUnit l F X).hom ≫
      (Functor.rightUnitor (completedDerivedScalarExtension l E F ι X)).hom)
    (fun P ↦ ?_) K).trans (Category.comp_id _)
  have := (finiteFreeScalarCochainProperties l E F ι X).2.2 P
  have hn : (ordinaryUnit l F X).hom.app
        ((completedDerivedScalarExtension l E F ι X).obj (DerivedCategory.Q.obj P)) ≫
      completedScalarCounit l E F ι X P =
      (completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X).map
          (completedScalarCounit l E F ι X P) ≫
        (ordinaryUnit l F X).hom.app
          (DerivedCategory.Q.obj ((completedOrdinaryScalarComplex l E F ι X).obj P)) :=
    ((ordinaryUnit l F X).hom.naturality _).symm
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id]
  rw [
    ← cancel_mono (completedScalarCounit l E F ι X P), ← hd, hn, ordinaryUnit_hom_app_Q, hA]

/-- Derived associators normalized by termwise associators satisfying the pentagon satisfy
the pentagon.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: after the invertible composite counit, the normalizations and counit naturality
reduce both routes to the counits followed by the two termwise routes. -/
private theorem derived_pentagon_aux
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H) (ρ₁ : E →ₐ[ℚ_[l]] G) (ρ₂ : F →ₐ[ℚ_[l]] H) (ρ : E →ₐ[ℚ_[l]] H)
    (d₁ : completedDerivedScalarExtension l E F ι X ⋙
      completedDerivedScalarExtension l F G j X ≅ completedDerivedScalarExtension l E G ρ₁ X)
    (d₂ : completedDerivedScalarExtension l E G ρ₁ X ⋙
      completedDerivedScalarExtension l G H k X ≅ completedDerivedScalarExtension l E H ρ X)
    (d₃ : completedDerivedScalarExtension l F G j X ⋙
      completedDerivedScalarExtension l G H k X ≅ completedDerivedScalarExtension l F H ρ₂ X)
    (d₄ : completedDerivedScalarExtension l E F ι X ⋙
      completedDerivedScalarExtension l F H ρ₂ X ≅ completedDerivedScalarExtension l E H ρ X)
    (A₁ : completedOrdinaryScalarComplex l E F ι X ⋙
      completedOrdinaryScalarComplex l F G j X ≅ completedOrdinaryScalarComplex l E G ρ₁ X)
    (A₂ : completedOrdinaryScalarComplex l E G ρ₁ X ⋙
      completedOrdinaryScalarComplex l G H k X ≅ completedOrdinaryScalarComplex l E H ρ X)
    (A₃ : completedOrdinaryScalarComplex l F G j X ⋙
      completedOrdinaryScalarComplex l G H k X ≅ completedOrdinaryScalarComplex l F H ρ₂ X)
    (A₄ : completedOrdinaryScalarComplex l E F ι X ⋙
      completedOrdinaryScalarComplex l F H ρ₂ X ≅ completedOrdinaryScalarComplex l E H ρ X)
    (hd₁ : ∀ P, (completedDerivedScalarExtension l F G j X).map
        (completedScalarCounit l E F ι X P) ≫
      completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
      DerivedCategory.Q.map (A₁.hom.app P) =
        d₁.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E G ρ₁ X P)
    (hd₂ : ∀ P, (completedDerivedScalarExtension l G H k X).map
        (completedScalarCounit l E G ρ₁ X P) ≫
      completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l E G ρ₁ X).obj P) ≫
      DerivedCategory.Q.map (A₂.hom.app P) =
        d₂.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E H ρ X P)
    (hd₃ : ∀ P, (completedDerivedScalarExtension l G H k X).map
        (completedScalarCounit l F G j X P) ≫
      completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l F G j X).obj P) ≫
      DerivedCategory.Q.map (A₃.hom.app P) =
        d₃.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l F H ρ₂ X P)
    (hd₄ : ∀ P, (completedDerivedScalarExtension l F H ρ₂ X).map
        (completedScalarCounit l E F ι X P) ≫
      completedScalarCounit l F H ρ₂ X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
      DerivedCategory.Q.map (A₄.hom.app P) =
        d₄.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E H ρ X P)
    (hA : ∀ P, (completedOrdinaryScalarComplex l G H k X).map (A₁.hom.app P) ≫ A₂.hom.app P =
      A₃.hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫ A₄.hom.app P)
    (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l G H k X).map (d₁.hom.app K) ≫ d₂.hom.app K =
      d₃.hom.app ((completedDerivedScalarExtension l E F ι X).obj K) ≫ d₄.hom.app K := by
  refine (derived_natTrans_app_eq
    (Functor.whiskerRight d₁.hom (completedDerivedScalarExtension l G H k X) ≫ d₂.hom)
    ((Functor.associator (completedDerivedScalarExtension l E F ι X)
        (completedDerivedScalarExtension l F G j X)
        (completedDerivedScalarExtension l G H k X)).hom ≫
      Functor.whiskerLeft (completedDerivedScalarExtension l E F ι X) d₃.hom ≫ d₄.hom)
    (fun P ↦ ?_) K).trans (Category.id_comp _)
  have := (finiteFreeScalarCochainProperties l E H ρ X).2.2 P
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
    ← cancel_mono (completedScalarCounit l E H ρ X P), Category.assoc, Category.assoc, ← hd₂,
    ← Functor.map_comp_assoc, ← hd₁, ← hd₄, ← d₃.hom.naturality_assoc, ← reassoc_of% (hd₃ _)]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
  have hn : (completedDerivedScalarExtension l G H k X).map
        (DerivedCategory.Q.map (A₁.hom.app P)) ≫
      completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l E G ρ₁ X).obj P) =
      completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l F G j X).obj
          ((completedOrdinaryScalarComplex l E F ι X).obj P)) ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l G H k X).map (A₁.hom.app P)) :=
    counit_naturality l G X H k _
  rw [reassoc_of% hn, ← Functor.map_comp DerivedCategory.Q, hA, Functor.map_comp]

/-- The ordinary associator with an identity first step is the extension of the unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf maps send t tensor (s tensor x) to t*s tensor x.
The universal counits are invertible for finite free extensions, so the derived
equation follows from the chain equation on good complexes and localization. -/
theorem associatorData_derived_source_unit (K : DerivedCategory (integralTowerModules l E X)) :
    (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).derived.hom.app K =
      (completedDerivedScalarExtension l E F ι X).map ((ordinaryUnit l E X).hom.app K) :=
  derived_source_unit_aux l E X F ι (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).derived
    (scalarAssociatorComplex l E X E (AlgHom.id ℚ_[l] E) F ι
      (associatorData l E X E (AlgHom.id ℚ_[l] E) F ι).sheaf)
    (associatorData_derived_normalized l E X E (AlgHom.id ℚ_[l] E) F ι)
    (scalarAssociatorComplex_source_unit l E X F ι) K

/-- The ordinary associator with an identity second step is the unitor.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf maps send t tensor (s tensor x) to t*s tensor x.
Invertible universal counits and localization give the derived equation. -/
theorem associatorData_derived_target_unit (K : DerivedCategory (integralTowerModules l E X)) :
    (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).derived.hom.app K =
      (ordinaryUnit l F X).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) :=
  derived_target_unit_aux l E X F ι (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).derived
    (scalarAssociatorComplex l E X F ι F (AlgHom.id ℚ_[l] F)
      (associatorData l E X F ι F (AlgHom.id ℚ_[l] F)).sheaf)
    (associatorData_derived_normalized l E X F ι F (AlgHom.id ℚ_[l] F))
    (scalarAssociatorComplex_target_unit l E X F ι) K

/-- The ordinary associators satisfy the pentagon.
Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: for three transitions both routes send u tensor (t tensor (s tensor x)) to
u*k(t)*k(j(s)) tensor x. Ordinary extension preserves good complexes and its universal
counits are invertible, so the counit normalizations transport this chain identity to
the derived pentagon on good complexes; localization concludes. -/
theorem associatorData_derived_pentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H) (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l G H k X).map
        ((associatorData l E X F ι G j).derived.hom.app K) ≫
      (associatorData l E X G (j.comp ι) H k).derived.hom.app K =
    (associatorData l F X G j H k).derived.hom.app
        ((completedDerivedScalarExtension l E F ι X).obj K) ≫
      (associatorData l E X F ι H (k.comp j)).derived.hom.app K :=
  derived_pentagon_aux l E X F ι G j H k (j.comp ι) (k.comp j) (k.comp (j.comp ι))
    (associatorData l E X F ι G j).derived (associatorData l E X G (j.comp ι) H k).derived
    (associatorData l F X G j H k).derived (associatorData l E X F ι H (k.comp j)).derived
    (scalarAssociatorComplex l E X F ι G j (associatorData l E X F ι G j).sheaf)
    (scalarAssociatorComplex l E X G (j.comp ι) H k (associatorData l E X G (j.comp ι) H k).sheaf)
    (scalarAssociatorComplex l F X G j H k (associatorData l F X G j H k).sheaf)
    (scalarAssociatorComplex l E X F ι H (k.comp j) (associatorData l E X F ι H (k.comp j)).sheaf)
    (associatorData_derived_normalized l E X F ι G j)
    (associatorData_derived_normalized l E X G (j.comp ι) H k)
    (associatorData_derived_normalized l F X G j H k)
    (associatorData_derived_normalized l E X F ι H (k.comp j))
    (scalarAssociatorComplex_pentagon l E X F ι G j H k) K

end CompletedLineTensor
end WeilConjectures
