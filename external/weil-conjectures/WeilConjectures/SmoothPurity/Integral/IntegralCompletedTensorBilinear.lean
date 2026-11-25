/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear
import WeilConjectures.Algebra.Homology.BifunctorLinear
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

/-! # Constant-scalar bilinearity of the normalized integral completed tensor

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks Project,
Tags 06YS and 099N; the assigned integral-to-rational tensor construction.
(blueprint: lem-sf-integral-completed-tensor-bilinear).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

open CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

private def tensorPartialRightIso
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    (L : C ⥤ D) (F : D × D ⥤ B) (Q : B ⥤ A) (P : C) :
    (Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).obj P ≅
      L ⋙ (Functor.curry.obj F).obj (L.obj P) ⋙ Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp
    rw [L.map_id]
    simp)

private def tensorPartialLeftIso
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    (L : C ⥤ D) (F : D × D ⥤ B) (Q : B ⥤ A) (P : C) :
    (Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).flip.obj P ≅
      L ⋙ (Functor.curry.obj F).flip.obj (L.obj P) ⋙ Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp
    rw [L.map_id]
    simp)

private theorem tensorPartialComposite_linear
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    [Preadditive C] [Preadditive D] [Preadditive B] [Preadditive A]
    (R : Type*) [Ring R] [Linear R C] [Linear R D] [Linear R B] [Linear R A]
    (L : C ⥤ D) (F : D × D ⥤ B) (Q : B ⥤ A) (P : C)
    [L.Additive] [L.Linear R] [Q.Additive] [Q.Linear R]
    (h : ((Functor.curry.obj F).obj (L.obj P)).Additive ∧
      ((Functor.curry.obj F).obj (L.obj P)).Linear R ∧
      ((Functor.curry.obj F).flip.obj (L.obj P)).Additive ∧
      ((Functor.curry.obj F).flip.obj (L.obj P)).Linear R) :
    ((Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).obj P).Additive ∧
      ((Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).obj P).Linear R ∧
      ((Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).flip.obj P).Additive ∧
      ((Functor.curry.obj (L.prod L ⋙ F ⋙ Q)).flip.obj P).Linear R := by
  obtain ⟨ha, hs, hb, ht⟩ := h
  let er := tensorPartialRightIso L F Q P
  let el := tensorPartialLeftIso L F Q P
  exact ⟨Functor.additive_of_iso
      (F := L ⋙ (Functor.curry.obj F).obj (L.obj P) ⋙ Q) er.symm,
    Functor.linear_of_iso R (F := L ⋙ (Functor.curry.obj F).obj (L.obj P) ⋙ Q) er.symm,
    Functor.additive_of_iso (F := L ⋙ (Functor.curry.obj F).flip.obj (L.obj P) ⋙ Q) el.symm,
    Functor.linear_of_iso R (F := L ⋙ (Functor.curry.obj F).flip.obj (L.obj P) ⋙ Q) el.symm⟩

section TensorRepresentatives

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

private noncomputable abbrev ScalarRing := Padic.coefficientExtensionIntegers l E

attribute [local instance] coefficientModuleLinear
attribute [local instance 3000] integralCoefficientLinear
attribute [local irreducible] unrestrictedIntegralReductionExistence HasDerivedCategory.standard

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
    (coefficient_scalarSections l E W)

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

private theorem tensorFiniteAction_eq (n : ℕ) (a : ScalarRing l E)
    (M : integralOperationsFiniteModules l E W n) :
    (finiteAction l E W n a).app M = a • 𝟙 M := by
  ext U x
  change integralScalarFiniteConstant l E W n U a • x =
    ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) • x
  rw [show ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) = integralScalarFiniteConstant l E W n U a
    from (integralScalarConstant_existsUnique l E W U a).exists.choose_spec n]

private instance tensorReduction_linear (n : ℕ) :
    (unrestrictedIntegralReductionFunctor.{u, u} l E W n).Linear (ScalarRing l E) := by
  rw [Functor.linear_iff]
  intro M a
  rw [← moduleAction_eq, reduction_action, tensorFiniteAction_eq]

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

private instance tensorFiniteRight_linear (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) :
    ((MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).obj M).Linear
      (ScalarRing l E) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  let : SymmetricCategory (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesSymmetric.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf l E W n)
  have := finiteTensor_linear l E W n M
  exact Functor.linear_of_iso (ScalarRing l E)
    (BraidedCategory.tensorLeftIsoTensorRight M).symm

private theorem tensorLevel_linear (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    ((Functor.curry.obj (integralOperationsTensorLevel l E W n)).obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorLevel l E W n)).obj P).Linear
        (ScalarRing l E) ∧
      ((Functor.curry.obj (integralOperationsTensorLevel l E W n)).flip.obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorLevel l E W n)).flip.obj P).Linear
        (ScalarRing l E) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let : MonoidalCategory (integralOperationsFiniteModules l E W n) :=
    integralOperationsFiniteMonoidal l E W n
  let : MonoidalPreadditive (integralOperationsFiniteModules l E W n) :=
    SheafOfModules.cochainModulesPreadditive.{u + 1, u, u + 1}
      (integralCoefficientCommRingSheaf.{u, u} l E W n)
  have (N : integralOperationsFiniteModules l E W n) :
      ((MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)).flip.obj N).Linear
        (ScalarRing l E) := finiteTensor_linear l E W n N
  have := restrict_linear l E W n
  let R := integralOperationsRestrict l E W n
  let red := unrestrictedIntegralFiniteComplex l E W n
  let G := (MonoidalCategory.curriedTensor
    (integralOperationsFiniteModules l E W n)).map₂CochainComplex
  have : R.Additive := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  have : R.Linear (ScalarRing l E) := by
    dsimp [R, integralOperationsRestrict]
    infer_instance
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro Q Q' f g
    change R.map ((G.map (red.map (𝟙 P))).app (red.obj Q) ≫
        (G.obj (red.obj P)).map (red.map (f + g))) = _
    simp only [Functor.map_add, Preadditive.comp_add]
    rfl
  · intro Q Q' f a
    change R.map ((G.map (red.map (𝟙 P))).app (red.obj Q) ≫
        (G.obj (red.obj P)).map (red.map (a • f))) = _
    simp only [Functor.map_smul, Linear.comp_smul]
    rfl
  · intro Q Q' f g
    change R.map ((G.map (red.map (f + g))).app (red.obj P) ≫
        (G.obj (red.obj Q')).map (red.map (𝟙 P))) = _
    simp only [Functor.map_add, NatTrans.app_add, Preadditive.add_comp]
    rfl
  · intro Q Q' f a
    change R.map ((G.map (red.map (a • f))).app (red.obj P) ≫
        (G.obj (red.obj Q')).map (red.map (𝟙 P))) = _
    rw [red.map_smul]
    have hg : (G.map (a • red.map f)).app (red.obj P) =
        a • (G.map (red.map f)).app (red.obj P) :=
      (G.flip.obj (red.obj P)).map_smul a (red.map f)
    rw [hg, Linear.smul_comp, R.map_smul]
    rfl

private theorem tensorComplex_linear
    (P : CochainComplex (integralTowerModules l E W) ℤ) :
    ((Functor.curry.obj (integralOperationsTensorComplexFunctor l E W)).obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorComplexFunctor l E W)).obj P).Linear
        (ScalarRing l E) ∧
      ((Functor.curry.obj (integralOperationsTensorComplexFunctor l E W)).flip.obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorComplexFunctor l E W)).flip.obj P).Linear
        (ScalarRing l E) := by
  let T := integralOperationsTensorTowerFunctor l E W
  have hr : (integralOperationsRoosFunctor (A := integralTowerModules l E W)).Additive :=
    roos_additive
  have hs : (integralOperationsRoosFunctor (A := integralTowerModules l E W)).Linear
      (ScalarRing l E) := roos_linear _
  have ha : ((Functor.curry.obj T).obj P).Additive := by
    constructor
    intro Q Q' f g
    apply NatTrans.ext
    funext n
    exact (tensorLevel_linear l E W n.unop P).1.map_add
  have hb : ((Functor.curry.obj T).obj P).Linear (ScalarRing l E) := by
    constructor
    intro Q Q' f a
    apply NatTrans.ext
    funext n
    exact (tensorLevel_linear l E W n.unop P).2.1.map_smul f a
  have hc : ((Functor.curry.obj T).flip.obj P).Additive := by
    constructor
    intro Q Q' f g
    apply NatTrans.ext
    funext n
    exact (tensorLevel_linear l E W n.unop P).2.2.1.map_add
  have hd : ((Functor.curry.obj T).flip.obj P).Linear (ScalarRing l E) := by
    constructor
    intro Q Q' f a
    apply NatTrans.ext
    funext n
    exact (tensorLevel_linear l E W n.unop P).2.2.2.map_smul f a
  change (((Functor.curry.obj T).obj P) ⋙ integralOperationsRoosFunctor).Additive ∧
    (((Functor.curry.obj T).obj P) ⋙ integralOperationsRoosFunctor).Linear (ScalarRing l E) ∧
    (((Functor.curry.obj T).flip.obj P) ⋙ integralOperationsRoosFunctor).Additive ∧
    (((Functor.curry.obj T).flip.obj P) ⋙ integralOperationsRoosFunctor).Linear (ScalarRing l E)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem tensorLocalization_linear :
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E W) ℤ ⥤
      DerivedCategory (integralTowerModules l E W)).Linear (ScalarRing l E) := by
  have hs : integralCoefficientLinear l E W = coefficientDerivedLinear l E W := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique l E W).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  rw [hs]
  exact Localization.functor_linear _ _ _

attribute [local irreducible] integralOperationsTensorComplexFunctor

private theorem tensorGood_linear
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    ((Functor.curry.obj (integralOperationsTensorOnGood l E W)).obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorOnGood l E W)).obj P).Linear
        (ScalarRing l E) ∧
      ((Functor.curry.obj (integralOperationsTensorOnGood l E W)).flip.obj P).Additive ∧
      ((Functor.curry.obj (integralOperationsTensorOnGood l E W)).flip.obj P).Linear
        (ScalarRing l E) := by
  have := tensorLocalization_linear l E W
  let ι := (integralOperationsGoodComplex l E W).ι
  have heq : integralOperationsTensorOnGood l E W =
      ι.prod ι ⋙ integralOperationsTensorComplexFunctor l E W ⋙ DerivedCategory.Q := rfl
  rw [heq]
  exact tensorPartialComposite_linear (ScalarRing l E) ι
    (integralOperationsTensorComplexFunctor l E W) DerivedCategory.Q P
    (tensorComplex_linear l E W (ι.obj P))

end TensorRepresentatives

private theorem partial_descent
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (R : Type*) [Ring R] [Linear R C] [Linear R D] [Linear R B]
    (L : C ⥤ D) (V : MorphismProperty C) [L.IsLocalization V]
    [L.Additive] [L.Linear R] (F : D ⥤ D ⥤ B)
    (h : ∀ P : C, (L ⋙ F.obj (L.obj P)).Additive ∧
      (L ⋙ F.obj (L.obj P)).Linear R) (M : D) :
    (F.obj M).Additive ∧ (F.obj M).Linear R := by
  let : L.EssSurj := Localization.essSurj L V
  have hgood (P : C) : (F.obj (L.obj P)).Additive ∧ (F.obj (L.obj P)).Linear R := by
    obtain ⟨ha, hs⟩ := h P
    let : Localization.Lifting L V (L ⋙ F.obj (L.obj P)) (F.obj (L.obj P)) := ⟨Iso.refl _⟩
    exact ⟨IntegralScalarAux.additive_descent L _,
      (Localization.functor_linear_iff L V R _ _).mp hs⟩
  obtain ⟨P, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L M
  obtain ⟨ha, hs⟩ := hgood P
  exact ⟨Functor.additive_of_iso (F.mapIso e), Functor.linear_of_iso R (F.mapIso e)⟩

section TensorDescent

attribute [local instance] coefficientModuleLinear
attribute [local instance 3000] integralCoefficientLinear

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

private theorem tensorDerived_linear (M : DerivedCategory (integralTowerModules l E W)) :
    ((Functor.curry.obj (integralCompletedTensor l E W)).obj M).Additive ∧
      ((Functor.curry.obj (integralCompletedTensor l E W)).obj M).Linear
        (Padic.coefficientExtensionIntegers l E) ∧
      ((Functor.curry.obj (integralCompletedTensor l E W)).flip.obj M).Additive ∧
      ((Functor.curry.obj (integralCompletedTensor l E W)).flip.obj M).Linear
        (Padic.coefficientExtensionIntegers l E) := by
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let L := integralOperationsGoodLocalization l E W
  let T := Functor.curry.obj (integralCompletedTensor l E W)
  let H := Functor.curry.obj (integralOperationsTensorOnGood l E W)
  let : L.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  let : HasBinaryBiproducts (integralOperationsGoodComplex l E W).FullSubcategory :=
    integralScalarGood_biproducts l E W
  let : L.Additive := by
    dsimp [L, integralOperationsGoodLocalization]
    infer_instance
  let : L.Linear (Padic.coefficientExtensionIntegers l E) := by
    have := tensorLocalization_linear l E W
    dsimp [L, integralOperationsGoodLocalization]
    infer_instance
  let d := integralCompletedTensorComparison l E W
  have e (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      L ⋙ T.obj (L.obj P) ≅ H.obj P :=
    NatIso.ofComponents (fun Q ↦ d.app (P, Q)) (by
      intro Q Q' f
      have hd := d.hom.naturality (Prod.mkHom (𝟙 P) f)
      dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map] at hd
      rw [CategoryTheory.Functor.map_id] at hd
      exact hd)
  have e' (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      L ⋙ T.flip.obj (L.obj P) ≅ H.flip.obj P :=
    NatIso.ofComponents (fun Q ↦ d.app (Q, P)) (by
      intro Q Q' f
      have hd := d.hom.naturality (Prod.mkHom f (𝟙 P))
      dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map] at hd
      rw [CategoryTheory.Functor.map_id] at hd
      exact hd)
  have h (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      (L ⋙ T.obj (L.obj P)).Additive ∧
        (L ⋙ T.obj (L.obj P)).Linear (Padic.coefficientExtensionIntegers l E) := by
    obtain ⟨ha, hs, _, _⟩ := tensorGood_linear l E W P
    exact ⟨Functor.additive_of_iso (e P).symm,
      Functor.linear_of_iso _ (e P).symm⟩
  have h' (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      (L ⋙ T.flip.obj (L.obj P)).Additive ∧
        (L ⋙ T.flip.obj (L.obj P)).Linear (Padic.coefficientExtensionIntegers l E) := by
    obtain ⟨_, _, ha, hs⟩ := tensorGood_linear l E W P
    exact ⟨Functor.additive_of_iso (e' P).symm,
      Functor.linear_of_iso _ (e' P).symm⟩
  obtain ⟨ha, hs⟩ := partial_descent (Padic.coefficientExtensionIntegers l E) L V T h M
  obtain ⟨ha', hs'⟩ := partial_descent (Padic.coefficientExtensionIntegers l E) L V T.flip h' M
  exact ⟨ha, hs, ha', hs'⟩

end TensorDescent

/-- The normalized ambient completed tensor has a separately linear arrow action
for the published constant valuation-ring action.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks Project,
Tags 06YS and 099N; the integral-to-rational tensor construction in blueprint
`prose-03-02`.
(blueprint: lem-sf-integral-completed-tensor-bilinear).

Proof: represent both inputs by K-flat complexes with flat terms. Finite reduction
is extension of scalars, so it preserves addition and the constant valuation-ring
action on maps. On each summand of the total tensor its arrow map is the ordinary
balanced tensor of the two component maps. Tensor balancing identifies the action
of a constant scalar on either input with that scalar acting on the output;
additivity in each input holds on every summand. The signed differential and the
finite-reduction transitions commute with these identities. Restriction of scalars,
products and the shifted cone defining the Roos complex preserve them, giving
separate linearity on good representatives. Derived localization preserves the
published constant action, since the scalar chain transformation descends to the
scalar derived transformation defining that action. Every derived object has a
good representative; derived arrows are roofs between such representatives.
Naturality of the normalized descent comparison transports the equations to those
roofs. Inverses of quasi-isomorphisms commute with the same scalar action, so the
equations hold for all arrows, independently of the roofs. Package separate
additivity and scalar preservation as the two nested linear maps below. This
argument uses no torsion cancellation, boundedness or constructibility hypothesis;
in particular it also applies to zero maps, zero objects and torsion inputs. -/
theorem integralCompletedTensor_bilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u})
    (M M' N N' : DerivedCategory (integralTowerModules l E W)) :
    ∃ b : (M ⟶ M') →ₗ[Padic.coefficientExtensionIntegers l E]
        (N ⟶ N') →ₗ[Padic.coefficientExtensionIntegers l E]
        ((integralCompletedTensor l E W).obj (M, N) ⟶
          (integralCompletedTensor l E W).obj (M', N')),
      ∀ a b', b a b' = (integralCompletedTensor l E W).map (Prod.mkHom a b') := by
  let F := integralCompletedTensor l E W
  let T := Functor.curry.obj F
  obtain ⟨ha, hs, _, _⟩ := tensorDerived_linear l E W M'
  obtain ⟨_, _, hb, ht⟩ := tensorDerived_linear l E W N
  refine ⟨
    { toFun := fun f ↦
        { toFun := fun g ↦ (T.flip.obj N).map f ≫ (T.obj M').map g
          map_add' := by
            intro g h
            rw [Functor.map_add, Preadditive.comp_add]
          map_smul' := by
            intro a g
            rw [Functor.map_smul, Linear.comp_smul]
            rfl }
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro h
        change (T.flip.obj N).map (f + g) ≫ (T.obj M').map h = _
        rw [Functor.map_add, Preadditive.add_comp]
        rfl
      map_smul' := by
        intro a f
        apply LinearMap.ext
        intro h
        change (T.flip.obj N).map (a • f) ≫ (T.obj M').map h = _
        rw [Functor.map_smul, Linear.smul_comp]
        rfl }, ?_⟩
  intro a b'
  change F.map (Prod.mkHom a (𝟙 N)) ≫ F.map (Prod.mkHom (𝟙 M') b') = _
  rw [← F.map_comp]
  congr 1
  apply Prod.ext <;> simp

end WeilConjectures
