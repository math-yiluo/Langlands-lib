/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.BifunctorLinear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Scalar linearity of the completed tensor

Source: Stacks 06YS and 0941; completed tensor-Hom transpose, proof step 3
(blueprint: lem-coef-completed-tensor-scalar-linearity).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] unrestrictedIntegralReductionExistence HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

private noncomputable abbrev ScalarRing := Padic.coefficientExtensionIntegers l E

private noncomputable abbrev Coeff := completedIntegralCommRingSheafUnrestricted.{u, u} l E W

private theorem scalar_ext (U : W.ProEtᵒᵖ)
    {x y : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U}
    (h : ∀ n : ℕ,
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E W)
        (op n)).hom.app U) x =
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E W)
        (op n)).hom.app U) y) : x = y := by
  let h₁ := CategoryTheory.Limits.isLimitOfPreserves
    (sheafToPresheaf (Scheme.ProEt.topology W) RingCat)
    (CategoryTheory.Limits.limit.isLimit (integralCoefficientSheafSystem l E W))
  let h₂ := CategoryTheory.Limits.isLimitOfPreserves ((evaluation _ _).obj U) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  exact h n.unop

private theorem scalar_naturality {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (a : ScalarRing l E) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.map f
      (integralScalarConstant l E W U a) = integralScalarConstant l E W V a := by
  apply scalar_ext l E W V
  intro n
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E W U a))
    ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E W)
      (op n)).hom.naturality f)
  change ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E W)
      (op n)).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E W).obj.map f
        (integralScalarConstant l E W U a)) =
      (integralCoefficientSheaf l E W n).obj.map f
        (((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E W)
          (op n)).hom.app U) (integralScalarConstant l E W U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E W U a).exists.choose_spec n,
    (integralScalarConstant_existsUnique l E W V a).exists.choose_spec n]
  exact (congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    ((toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality f)).symm

private noncomputable abbrev finiteConstantMap (n : ℕ) (U : W.ProEtᵒᵖ) :=
  ((toSheafify (Scheme.ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U).hom

private noncomputable def scalarSections : ScalarRing l E →+*
    RingCat.sectionsSubring ((Coeff l E W).obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  toFun a := ⟨fun U ↦ integralScalarConstant l E W U a,
    fun f ↦ scalar_naturality l E W f a⟩
  map_one' := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E W U
    intro n
    erw [(integralScalarConstant_existsUnique l E W U 1).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, OneMemClass.coe_one, Pi.one_apply, map_one]
    exact map_one (finiteConstantMap l E W n U)
  map_mul' a b := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E W U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E W) (op n)).hom.app U
        (integralScalarConstant l E W U a * integralScalarConstant l E W U b)
    rw [map_mul]
    erw [(integralScalarConstant_existsUnique l E W U (a * b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E W U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E W U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_mul]
    exact map_mul (finiteConstantMap l E W n U) _ _
  map_zero' := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E W U
    intro n
    erw [(integralScalarConstant_existsUnique l E W U 0).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, ZeroMemClass.coe_zero, Pi.zero_apply, map_zero]
    exact map_zero (finiteConstantMap l E W n U)
  map_add' a b := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E W U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E W) (op n)).hom.app U
        (integralScalarConstant l E W U a + integralScalarConstant l E W U b)
    rw [map_add]
    erw [(integralScalarConstant_existsUnique l E W U (a + b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E W U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E W U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_add]
    exact map_add (finiteConstantMap l E W n U) _ _

@[instance_reducible]
private noncomputable def sectionsLinear
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (A : Sheaf J CommRingCat.{u + 1})
    (s : ScalarRing l E →+*
      RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    Linear (ScalarRing l E)
      (SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) := by
  letI : Linear (RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :=
    SheafOfModules.homLinear A.obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
      smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (s r) f g
      comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (s r) g }

@[instance_reducible]
private noncomputable def moduleLinear :
    Linear (ScalarRing l E) (integralTowerModules l E W) :=
  sectionsLinear l E (Coeff l E W) (scalarSections l E W)

attribute [local instance] moduleLinear

private theorem module_smul_apply
    {M N : integralTowerModules l E W} (f : M ⟶ N) (a : ScalarRing l E)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (a • f).val.app U x = integralScalarConstant l E W U a • f.val.app U x := rfl

private noncomputable def mapSections
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u + 1}} (φ : A ⟶ B) :
    RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) →+*
      RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  toFun s := ⟨fun U ↦ φ.hom.app U (s.val U), fun {U V} f ↦ by
    change B.obj.map f (φ.hom.app U (s.val U)) = φ.hom.app V (s.val V)
    have hn := ConcreteCategory.congr_hom (φ.hom.naturality f) (s.val U)
    change φ.hom.app V (A.obj.map f (s.val U)) =
      B.obj.map f (φ.hom.app U (s.val U)) at hn
    exact hn.symm.trans (congrArg (φ.hom.app V) (s.property f))⟩
  map_one' := Subtype.ext (funext fun U ↦ map_one (φ.hom.app U).hom)
  map_mul' s t := Subtype.ext (funext fun U ↦ map_mul (φ.hom.app U).hom _ _)
  map_zero' := Subtype.ext (funext fun U ↦ map_zero (φ.hom.app U).hom)
  map_add' s t := Subtype.ext (funext fun U ↦ map_add (φ.hom.app U).hom _ _)

private noncomputable def finiteSections (n : ℕ) : ScalarRing l E →+*
    RingCat.sectionsSubring
      ((integralCoefficientCommRingSheaf.{u, u} l E W n).obj ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (mapSections (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n)).comp
    (scalarSections l E W)

@[instance_reducible]
private noncomputable def finiteSheafLinear (n : ℕ) :
    Linear (ScalarRing l E)
      (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralCoefficientCommRingSheaf.{u, u} l E W n))) :=
  sectionsLinear l E (integralCoefficientCommRingSheaf.{u, u} l E W n)
    (finiteSections l E W n)

attribute [local instance] finiteSheafLinear

@[instance_reducible]
private noncomputable def finiteLinear (n : ℕ) :
    Linear (ScalarRing l E) (integralOperationsFiniteModules l E W n) :=
  finiteSheafLinear l E W n

attribute [local instance] finiteLinear

private theorem reduction_linear (n : ℕ) :
    (unrestrictedIntegralReductionFunctor.{u, u} l E W n).Linear (ScalarRing l E) := by
  let F := unrestrictedIntegralReductionFunctor.{u, u} l E W n
  let A := Coeff l E W
  let B := integralCoefficientCommRingSheaf.{u, u} l E W n
  let φ := completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n
  let O := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let h := (unrestrictedIntegralReductionExistence.{u, u} l E W n).choose_spec.choose
  have hm {M N : integralTowerModules l E W} (f : M ⟶ N) :
      F.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (h N).symm :=
    (unrestrictedIntegralReductionExistence.{u, u} l E W n).choose_spec.choose_spec.choose f
  rw [Functor.linear_iff]
  intro M a
  have hc : SheafOfModules.changeOfRingsHom φ M (a • 𝟙 M) =
      a • 𝟙 (SheafOfModules.changeOfRings (R₁ := A) (R₂ := B) φ M) := by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
    let t : SheafOfModules.changeOfRingsPresheaf (R₁ := A) (R₂ := B) φ M ⟶
        SheafOfModules.changeOfRingsPresheaf (R₁ := A) (R₂ := B) φ M :=
      { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map
          ((a • (𝟙 M : M ⟶ M)).val.app U)
        naturality := SheafOfModules.changeOfRingsHom_naturality φ M (a • 𝟙 M) }
    change (PresheafOfModules.sheafification (𝟙 O.obj)).map t = _
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hn := adj.unit.naturality t
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [Functor.comp_map]
    rw [← hn]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf (R₁ := A) (R₂ := B) φ M)).app U).hom
        ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom]
          ((a • (𝟙 M : M ⟶ M)).val.app U x)) =
      (φ.hom.app U (integralScalarConstant l E W U a)) •
        ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf (R₁ := A) (R₂ := B) φ M)).app U).hom
          ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x)
    rw [module_smul_apply]
    let r : A.obj.obj U := integralScalarConstant l E W U a
    let η := ((adj.unit.app
      (SheafOfModules.changeOfRingsPresheaf (R₁ := A) (R₂ := B) φ M)).app U).hom
    change η ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] (r • x)) =
      φ.hom.app U r • η ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x)
    have ht : (1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] (r • x) =
        φ.hom.app U r • ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x) := by
      let : Module (A.obj.obj U) (B.obj.obj U) :=
        Module.compHom _ (φ.hom.app U).hom
      change (1 : B.obj.obj U) ⊗ₜ[A.obj.obj U] (r • x) = _
      rw [TensorProduct.tmul_smul (R' := A.obj.obj U)]
      rfl
    rw [ht]
    exact η.map_smul _ _
  let e : F.obj M ≅ SheafOfModules.changeOfRings (R₁ := A) (R₂ := B) φ M :=
    eqToIso (h M)
  rw [hm, hc]
  change e.hom ≫ (a • 𝟙 _) ≫ e.inv = a • 𝟙 (F.obj M)
  calc
    _ = a • (e.hom ≫ 𝟙 _ ≫ e.inv) := by
      exact (congrArg (fun z ↦ e.hom ≫ z)
        (Linear.smul_comp _ _ _ a (𝟙 _) e.inv)).trans
          (Linear.comp_smul _ _ _ e.hom a (𝟙 _ ≫ e.inv))
    _ = _ := congrArg (fun z ↦ a • z)
      ((congrArg (fun z ↦ e.hom ≫ z) (Category.id_comp e.inv)).trans e.hom_inv_id)

private theorem finiteSiteTensor_linear (n : ℕ)
    (N : integralOperationsFiniteModules l E W n) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := integralCoefficientCommRingSheaf.{u, u} l E W n) N).Linear
      (ScalarRing l E) := by
  let B := integralCoefficientCommRingSheaf.{u, u} l E W n
  let O := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  constructor
  intro M M' f b
  change (PresheafOfModules.sheafification (𝟙 O.obj)).map
      (SheafOfModules.siteTensorHom (b • f).val N.val) =
    b • (PresheafOfModules.sheafification (𝟙 O.obj)).map
      (SheafOfModules.siteTensorHom f.val N.val)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality (SheafOfModules.siteTensorHom (b • f).val N.val)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [Functor.comp_map]
  rw [← hn]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hf := adj.unit.naturality (SheafOfModules.siteTensorHom f.val N.val)
  have hf' := congrArg (fun h ↦ (h.app U).hom (x ⊗ₜ[B.obj.obj U] y)) hf
  let r : B.obj.obj U := ((finiteSections l E W n) b).val U
  change ((adj.unit.app (SheafOfModules.siteTensorPresheaf M'.val N.val)).app U).hom
      (r • (f.val.app U).hom x ⊗ₜ[B.obj.obj U] y) =
    r •
      ((PresheafOfModules.sheafification (𝟙 O.obj)).map
        (SheafOfModules.siteTensorHom f.val N.val)).val.app U
          ((adj.unit.app (SheafOfModules.siteTensorPresheaf M.val N.val)).app U
            (x ⊗ₜ[B.obj.obj U] y))
  let η := ((adj.unit.app (SheafOfModules.siteTensorPresheaf M'.val N.val)).app U).hom
  calc
    _ = η (r • ((f.val.app U).hom x ⊗ₜ[B.obj.obj U] y)) :=
      congrArg η (TensorProduct.smul_tmul'
        (R := B.obj.obj U) (R' := B.obj.obj U) r ((f.val.app U).hom x) y).symm
    _ = r • η ((f.val.app U).hom x ⊗ₜ[B.obj.obj U] y) := η.map_smul _ _
    _ = _ := congrArg (fun z ↦ r • z) hf'

private theorem finiteTensor_linear (n : ℕ)
    (N : integralOperationsFiniteModules l E W n) :
    Functor.Linear (ScalarRing l E)
      ((MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).flip.obj N) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  have := finiteSiteTensor_linear l E W n N
  exact Functor.linear_of_iso (ScalarRing l E)
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf.{u, u} l E W n) N)

private theorem restrict_linear (n : ℕ) :
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n))).Linear
      (ScalarRing l E) := by
  constructor
  intro M N f a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem tensorLevel_smul (n : ℕ)
    {P P' Q Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : ScalarRing l E) :
    (integralOperationsTensorLevel l E W n).map (Prod.mkHom (a • f) g) =
      a • (integralOperationsTensorLevel l E W n).map (Prod.mkHom f g) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  let := reduction_linear l E W n
  let := restrict_linear l E W n
  have (N : integralOperationsFiniteModules l E W n) :
      Functor.Linear (ScalarRing l E)
        ((MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).flip.obj N) :=
    finiteTensor_linear l E W n N
  let R := integralOperationsRestrict l E W n
  let red := unrestrictedIntegralFiniteComplex l E W n
  have : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf.{u, u} l E W n)
  let F := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)
  let G := F.map₂CochainComplex
  have hR : R.Linear (ScalarRing l E) := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  have hG (h : red.obj P ⟶ red.obj P') :
      (G.map (a • h)).app (red.obj Q) = a • (G.map h).app (red.obj Q) :=
    by
      dsimp only [G, F, Functor.map₂CochainComplex]
      exact HomologicalComplex.mapBifunctorMap_smul₁ (ScalarRing l E) a h
        (𝟙 (red.obj Q))
        (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) (.up ℤ)
  change R.map ((G.map (red.map (a • f))).app (red.obj Q) ≫
      (G.obj (red.obj P')).map (red.map g)) =
    a • R.map ((G.map (red.map f)).app (red.obj Q) ≫
      (G.obj (red.obj P')).map (red.map g))
  rw [red.map_smul, hG, Linear.smul_comp, R.map_smul]

private theorem roos_smul
    {C C' : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ}
    (f : C ⟶ C') (a : ScalarRing l E) :
    integralOperationsRoosMap (a • f) = a • integralOperationsRoosMap f := by
  have hp : CategoryTheory.Limits.Pi.map (fun n ↦ (a • f).app (op n)) =
      a • CategoryTheory.Limits.Pi.map (fun n ↦ f.app (op n)) := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro n
    simp
  unfold integralOperationsRoosMap
  simp only [hp]
  rw [← (shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) (-1 : ℤ)).map_smul]
  congr 1
  ext i : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X
    (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
      (integralOperationsTowerStep C)) (i + 1) i rfl
  all_goals try simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]

private theorem tensorComplex_smul
    {P P' Q Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : ScalarRing l E) :
    (integralOperationsTensorComplexFunctor l E W).map (Prod.mkHom (a • f) g) =
      a • (integralOperationsTensorComplexFunctor l E W).map (Prod.mkHom f g) := by
  have ht : (integralOperationsTensorTowerFunctor l E W).map (Prod.mkHom (a • f) g) =
      a • (integralOperationsTensorTowerFunctor l E W).map (Prod.mkHom f g) := by
    apply NatTrans.ext
    funext n
    exact tensorLevel_smul l E W n.unop f g a
  change integralOperationsRoosMap _ = _
  rw [ht]
  exact roos_smul l E W _ a

private theorem scalarChain_eq (a : ScalarRing l E)
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    (integralScalarChainAction l E W a).app P = a • 𝟙 P := by
  ext i : 1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  exact (integralScalarChainAction_existsUnique l E W a).exists.choose_spec P i U x

private theorem localization_linear :
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E W) ℤ ⥤
      DerivedCategory (integralTowerModules l E W)).Linear (ScalarRing l E) := by
  constructor
  intro P Q f a
  have h := NatTrans.congr_app
    ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E W) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ))
      (DerivedCategory (integralTowerModules l E W))).map_preimage
        (X := 𝟭 (DerivedCategory (integralTowerModules l E W)))
        (Y := 𝟭 (DerivedCategory (integralTowerModules l E W)))
        (Functor.whiskerRight (integralScalarChainAction l E W a) DerivedCategory.Q)) P
  let α := (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E W) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ))
    (DerivedCategory (integralTowerModules l E W))).preimage
      (X := 𝟭 (DerivedCategory (integralTowerModules l E W)))
      (Y := 𝟭 (DerivedCategory (integralTowerModules l E W)))
      (Functor.whiskerRight (integralScalarChainAction l E W a) DerivedCategory.Q)
  have hα : integralScalarDerivedAction l E W a = α := by
    exact (existsUnique_eq (a' := α)).exists.choose_spec
  have hscalar : (integralScalarDerivedAction l E W a).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((integralScalarChainAction l E W a).app P) := by
    rw [hα]
    exact h
  rw [(integralCoefficientLinear_existsUnique l E W).exists.choose_spec, hscalar,
    ← DerivedCategory.Q.map_comp, scalarChain_eq]
  simp

private theorem good_representative (K : DerivedCategory (integralTowerModules l E W)) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  obtain ⟨K, ⟨eK⟩⟩ := Functor.EssSurj.mem_essImage
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E W) ℤ ⥤ _) K
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (C := W.ProEt) (J := Scheme.ProEt.topology W) (R := Coeff l E W) K
  have : QuasiIso f := hq
  have hflat (i : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := Coeff l E W) (P.X i) :=
    (exactFunctor (integralTowerModules l E W) (integralTowerModules l E W)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} (Coeff l E W) (P.X i)).symm (hf i)
  exact ⟨⟨P, hP, hflat⟩, ⟨(asIso (DerivedCategory.Q.map f)) ≪≫ eK⟩⟩

set_option backward.isDefEq.respectTransparency.types true in
private theorem ambientTensor_smul_id
    (M N : DerivedCategory (integralTowerModules l E W)) (a : ScalarRing l E) :
    (integralCompletedTensor l E W).map (Prod.mkHom (a • 𝟙 M) (𝟙 N)) =
      a • 𝟙 ((integralCompletedTensor l E W).obj (M, N)) := by
  let T := integralCompletedTensor l E W
  let d := integralCompletedTensorComparison l E W
  have := localization_linear l E W
  have hgood (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
      T.map (Prod.mkHom (a • 𝟙 (DerivedCategory.Q.obj P.obj)) (𝟙 (DerivedCategory.Q.obj Q.obj))) =
        a • 𝟙 (T.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) := by
    apply (cancel_mono (d.hom.app (P, Q))).mp
    have hd := d.hom.naturality
      (Prod.mkHom (a • 𝟙 P) (𝟙 Q))
    change T.map (Prod.mkHom (DerivedCategory.Q.map (a • 𝟙 P.obj))
        (DerivedCategory.Q.map (𝟙 Q.obj))) ≫ d.hom.app (P, Q) =
      d.hom.app (P, Q) ≫ DerivedCategory.Q.map
        ((integralOperationsTensorComplexFunctor l E W).map
          (Prod.mkHom (a • 𝟙 P.obj) (𝟙 Q.obj))) at hd
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      tensorComplex_smul, Functor.map_smul] at hd
    have hi : (integralOperationsTensorComplexFunctor l E W).map
        (Prod.mkHom (𝟙 P.obj) (𝟙 Q.obj)) = 𝟙 _ :=
      (integralOperationsTensorComplexFunctor l E W).map_id (P.obj, Q.obj)
    rw [hi] at hd
    have hqid := DerivedCategory.Q.map_id
      ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))
    have hd' := congrArg (fun z ↦ d.hom.app (P, Q) ≫ (a • z)) hqid
    have hd := hd.trans hd'
    have hd'' : d.hom.app (P, Q) ≫ (a • 𝟙 _) = a • d.hom.app (P, Q) :=
      (Linear.comp_smul _ _ _ (d.hom.app (P, Q)) a (𝟙 _)).trans
        (congrArg (fun z ↦ a • z) (Category.comp_id (d.hom.app (P, Q))))
    have hi' : (a • 𝟙 _) ≫ d.hom.app (P, Q) = a • d.hom.app (P, Q) :=
      (Linear.smul_comp _ _ _ a (𝟙 _) (d.hom.app (P, Q))).trans
        (congrArg (fun z ↦ a • z) (Category.id_comp (d.hom.app (P, Q))))
    exact hd.trans (hd''.trans hi'.symm)
  obtain ⟨P, ⟨e⟩⟩ := good_representative l E W M
  obtain ⟨Q, ⟨f⟩⟩ := good_representative l E W N
  let i := T.mapIso (Iso.prod e f)
  have hprod : Prod.mkHom (a • 𝟙 M) (𝟙 N) =
      Prod.mkHom e.inv f.inv ≫
        Prod.mkHom (a • 𝟙 (DerivedCategory.Q.obj P.obj)) (𝟙 (DerivedCategory.Q.obj Q.obj)) ≫
        Prod.mkHom e.hom f.hom := by
    apply Prod.ext <;> simp
  change T.map _ = _
  rw [hprod, T.map_comp, T.map_comp, hgood]
  change i.inv ≫ (a • 𝟙 _) ≫ i.hom = a • 𝟙 (T.obj (M, N))
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.inv_hom_id]

variable [∀ w : W, Invertible (l : W.residueField w)]

/-- Completed tensor is linear in its first morphism with the second fixed.
Source: Stacks 06YS and 0941; parent transpose proof step 3.
Proof: on flat-term K-flat representatives, scalar multiplication acts by the
constant completed section in each degree. The balanced total tensor sends
(c f) tensor g to c times (f tensor g), componentwise, with unchanged signs.
Every quotient and tower transition commutes with the constant section.
The Roos maps and derived localization preserve this equality. Conjugating by
the normalized descent comparison gives the equality for all derived arrows.
Restriction to the constructible full subcategory changes no morphism or scalar.
Zero objects, zero scalars and arbitrary torsion inputs require no cancellation.
(blueprint: lem-coef-completed-tensor-scalar-linearity). -/
theorem completedTensor_map_smul_left
    (M M' N N' : sfIntegralConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N')
    (c : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralTensor l E W).map (Prod.mkHom (c • f) g) =
      c • (constructibleIntegralTensor l E W).map (Prod.mkHom f g) := by
  apply ObjectProperty.hom_ext
  change (integralCompletedTensor l E W).map (Prod.mkHom (c • f.hom) g.hom) =
    c • (integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom)
  have h : Prod.mkHom (c • f.hom) g.hom =
      Prod.mkHom (c • 𝟙 M.obj) (𝟙 N.obj) ≫ Prod.mkHom f.hom g.hom := by
    apply Prod.ext <;> simp
  rw [h, Functor.map_comp, ambientTensor_smul_id]
  simp

end WeilConjectures
