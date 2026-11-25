/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node lemma-change-coefficients-internal-hom--1 (blueprint:
def-sf-etale-finite-coefficient-hom-arrow). Indices n and m below denote exponents n + 1 and m + 1;
thus every positive exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Signed total tensor with its object and map data kept explicit before specialization.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomCochainTensorGeneral
    (C : Type a) [Category.{b} C] [Preadditive C] [HasZeroObject C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C] :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ := by
  let (P Q : CochainComplex C ℤ) : HomologicalComplex.HasTensor P Q := inferInstance
  exact
    { obj := fun P ↦ HomologicalComplex.tensorObj P.1 P.2
      map := fun f ↦ HomologicalComplex.tensorHom f.1 f.2
      map_id := fun P ↦ by
        apply HomologicalComplex.Hom.ext
        funext k
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        simp only [HomologicalComplex.tensorHom, HomologicalComplex.ι_mapBifunctorMap,
          prod_id_fst, prod_id_snd, HomologicalComplex.id_f,
          curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc,
          id_tensorHom_id, Category.id_comp, Category.comp_id]
      map_comp := fun f g ↦ by
        apply HomologicalComplex.Hom.ext
        funext k
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        simp only [HomologicalComplex.tensorHom, prod_comp_fst, prod_comp_snd,
          HomologicalComplex.comp_f,
          HomologicalComplex.ι_mapBifunctorMap_assoc,
          HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app,
          curriedTensor_obj_map, ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc] }

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Native tensor and its localization map, shared as a single real construction.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomNativeTensorData
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  cochain : Type (max a b)
  [cochainCategory : Category.{b} cochain]
  cochainTensor : cochain × cochain ⥤ cochain
  localization : cochain ⥤ DerivedCategory C
  tensor : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C
  model (P Q : cochain) :
    tensor.obj (localization.obj P, localization.obj Q) ⟶
      localization.obj (cochainTensor.obj (P, Q))

attribute [local instance] FiniteHomNativeTensorData.cochainCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The published derived tensor together with the published localization tensorator.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomNativeTensorDataGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] : FiniteHomNativeTensorData C where
  cochain := CochainComplex C ℤ
  cochainCategory := inferInstance
  cochainTensor := finiteHomCochainTensorGeneral C
  localization := DerivedCategory.Q
  tensor := tensor (DerivedCategory C)
  model P Q := Functor.LaxMonoidal.μ DerivedCategory.Q P Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native localization tensorator projected from its shared tensor data.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomLocalizationTensorModelGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : (finiteHomNativeTensorDataGeneral C).cochain) :=
  (finiteHomNativeTensorDataGeneral C).model P Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native tensor functor projected from its shared tensor data.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomDerivedTensorGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :=
  (finiteHomNativeTensorDataGeneral C).tensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native complex, localization and tensor data before coefficient specialization.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleNativeTensorDataGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomNativeTensorDataGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Source category, signed tensor and localization kept in one real record.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomTensorSourceData (D : Type a) [Category.{b} D] where
  cochain : Type c
  [cochainCategory : Category.{b} cochain]
  cochainTensor : cochain × cochain ⥤ cochain
  localization : cochain ⥤ D

attribute [local instance] FiniteHomTensorSourceData.cochainCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native etale source data, sharing its category before coefficient specialization.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorSourceGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  FiniteHomTensorSourceData.mk
    (cochainCategory := (finiteHomEtaleNativeTensorDataGeneral A W).cochainCategory)
    (finiteHomEtaleNativeTensorDataGeneral A W).cochain
    (finiteHomEtaleNativeTensorDataGeneral A W).cochainTensor
    (finiteHomEtaleNativeTensorDataGeneral A W).localization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same cochain category, projected before coefficient specialization.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleCochainGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) := (finiteHomEtaleTensorSourceGeneral A W).cochain

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native category on the shared cochain type.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
@[instance_reducible] def finiteHomEtaleCochainCategoryGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) : Category.{u + 1} (finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleTensorSourceGeneral A W).cochainCategory

attribute [instance] finiteHomEtaleCochainCategoryGeneral

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same signed total tensor, projected before coefficient specialization.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTotalObjectGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleTensorSourceGeneral A W).cochainTensor.obj (P, Q)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The native derived tensor functor shared before coefficient specialization.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleDerivedTensorGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  (finiteHomEtaleNativeTensorDataGeneral A W).tensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same small etale localization tensorator before coefficient specialization.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleLocalizationTensorModelGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W) :=
  (finiteHomEtaleNativeTensorDataGeneral A W).model P Q

/-- Right-tensor adjunction obtained from the published internal Hom and braiding.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomRightAdjunction {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] (P : C) :
    tensorRight P ⊣ Prod.sectR (op P) C ⋙
      Functor.uncurry.obj (MonoidalClosed.internalHom (C := C)) :=
  ((ihom.adjunction P).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight P)).ofNatIsoRight
    (((Functor.currying (C := Cᵒᵖ) (D := C) (E := C)).unitIso.app
      (MonoidalClosed.internalHom (C := C))).app (op P))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Naturality of the right-tensor evaluation obtained by symmetry.
Source: blueprint evaluation paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: move the braiding across the internal-Hom map by naturality, then use
internalHomAdjunction₂'s counit naturality in its parameter. -/
theorem finiteHomEvaluation_naturality
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (P P' Q : C) (f : P' ⟶ P) :
    (tensorRight P').map ((Functor.uncurry.obj (MonoidalClosed.internalHom (C := C))).map
        (Prod.mkHom f.op (𝟙 Q))) ≫
      ((finiteHomRightAdjunction P').counit.app Q) =
    (tensorLeft ((ihom P).obj Q)).map f ≫
      ((finiteHomRightAdjunction P).counit.app Q) := by
  have ev (T : C) : (finiteHomRightAdjunction T).counit.app Q =
      (β_ T ((ihom T).obj Q)).inv ≫ (ihom.ev T).app Q := by
    change (tensorRight T).map (𝟙 ((ihom T).obj Q)) ≫
      ((β_ T ((ihom T).obj Q)).inv ≫ (ihom.ev T).app Q) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ev P, ev P']
  simp only [Functor.uncurry_obj_map, MonoidalClosed.internalHom_map,
    Quiver.Hom.unop_op,
    CategoryTheory.Functor.map_id, Category.comp_id]
  change (MonoidalClosed.pre f).app Q ▷ P' ≫
      (β_ P' ((ihom P').obj Q)).inv ≫ (ihom.ev P').app Q =
    ((ihom P).obj Q) ◁ f ≫ (β_ P ((ihom P).obj Q)).inv ≫ (ihom.ev P).app Q
  rw [← Category.assoc, BraidedCategory.braiding_inv_naturality_left]
  rw [Category.assoc, MonoidalClosed.id_tensor_pre_app_comp_ev]
  rw [← Category.assoc, ← BraidedCategory.braiding_inv_naturality_right, Category.assoc]

/-- The existing closed structure, with Hom tensor P evaluation order.
Source: blueprint tensor-Hom adjunction paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomClosed {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] :
    CoefficientClosedStructure (Functor.uncurry.obj (MonoidalClosed.internalHom (C := C))) where
  monoidal := inferInstance
  adjunction := finiteHomRightAdjunction
  evaluation_naturality := finiteHomEvaluation_naturality

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual positive-level etale category.
Source: blueprint coefficient convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtale (n : ℕ) :=
  Etale.DerivedCategoryModule (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- The etale derived category uses the published small morphism universe.
Source: blueprint etale size convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
@[instance_reducible] def finiteHomEtaleCategory (n : ℕ) :
    Category.{u + 1} (finiteHomEtale l E X n) := inferInstance

attribute [instance] finiteHomEtaleCategory

/-- Canonical quotient A_(n + 1) to A_(m + 1).
Source: blueprint coefficient convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomQuotient {n m : ℕ} (h : m ≤ n) :=
  Scheme.flatModelReductionCoefficientMap l E (m + 1) (n + 1) (Nat.add_le_add_right h 1)

/-- The published Koszul isomorphism, computed before coefficient specialization.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomKoszulIso (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : DerivedCategory C) :=
  letI : HasColimitsOfShape ℤ C := HasColimitsOfSize.has_colimits_of_shape ℤ
  letI : HasExactColimitsOfShape ℤ C := hasExactColimitsOfShape_int C
  letI : ∀ T : C, PreservesColimitsOfShape ℤ (tensorLeft T) := fun T ↦
    letI : PreservesColimitsOfSize.{0, 0} (tensorLeft T) :=
      (ihom.adjunction T).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesColimitsOfShape
  letI : ∀ T : C, PreservesColimitsOfShape ℤ (tensorRight T) := fun T ↦
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight T)
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) P Q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteHomBraided_ext {C : Type a} [Category.{b} C]
    [MonoidalCategory C] (S T : BraidedCategory C) (h : S.braiding = T.braiding) :
    S = T := by
  cases S
  cases T
  cases h
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The braid structure is fixed componentwise by the actual Koszul isomorphism.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the published derived braiding, whose components are these isomorphisms.
Naturality and the hexagons descend from complexes. Equality of all components
and proof irrelevance give uniqueness. -/
theorem finiteHomDerivedBraiding_existsUnique (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    ∃! S : BraidedCategory (DerivedCategory C),
      ∀ P Q : DerivedCategory C, HEq (S.braiding P Q) (finiteHomKoszulIso C P Q) := by
  refine ⟨DerivedMonoidal.braidedCategory' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)), ?_, ?_⟩
  · intro P Q
    rfl
  · intro S hS
    have h : S.braiding = (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).braiding := by
      funext P Q
      exact eq_of_heq (hS P Q)
    apply finiteHomBraided_ext
    exact h

/-- The uniquely normalized Koszul braid structure.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
@[instance_reducible] def finiteHomDerivedBraiding (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :=
  (finiteHomDerivedBraiding_existsUnique C).choose

/-- The prescribed right-tensor adjunction before specializing the category.
Source: blueprint tensor-Hom adjunction paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomDerivedRightAdjunctionGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P : DerivedCategory C) :=
  letI := finiteHomDerivedBraiding C
  finiteHomRightAdjunction P

/-- The native derived internal Hom before choosing an etale coefficient category.
Source: blueprint tensor-Hom paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomDerivedInternalHomGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :=
  Functor.uncurry.obj (MonoidalClosed.internalHom (C := DerivedCategory C))

/-- The prescribed native derived closed normalization, with all data shared.
Source: blueprint tensor-Hom paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomDerivedClosedNormalization
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : CoefficientClosedStructure (finiteHomDerivedInternalHomGeneral C)) : Prop :=
  S.monoidal = (inferInstance : MonoidalCategory (DerivedCategory C)) ∧
  ∀ P : DerivedCategory C, HEq (S.adjunction P) (finiteHomDerivedRightAdjunctionGeneral C P)

/-- The published etale internal Hom, with its category data shared before
specializing the coefficient category. Source: blueprint derived Hom
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleInternalHomGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomDerivedInternalHomGeneral (Sheaf W.smallEtaleTopology A)

/-- The closed record has the published tensor and the specified right adjunction.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomEtaleClosedNormalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (S : CoefficientClosedStructure (finiteHomEtaleInternalHomGeneral A W)) : Prop :=
  FiniteHomDerivedClosedNormalization (Sheaf W.smallEtaleTopology A) S

section ClosedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

private theorem finiteHomClosed_ext
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S T : CoefficientClosedStructure H) (hm : S.monoidal = T.monoidal)
    (ha : ∀ P : D, HEq (S.adjunction P) (T.adjunction P)) : S = T := by
  cases S with
  | mk sm sa se =>
    cases T with
    | mk tm ta te =>
      dsimp only at hm
      cases hm
      have h : sa = ta := funext (fun P ↦ eq_of_heq (ha P))
      cases h
      rfl

private theorem finiteHomClosed_normalized
    {D : Type a} [Category.{b} D] [MonoidalCategory D] [BraidedCategory D]
    [MonoidalClosed D] :
    ∃! S : CoefficientClosedStructure
        (Functor.uncurry.obj (MonoidalClosed.internalHom (C := D))),
      S.monoidal = (inferInstance : MonoidalCategory D) ∧
      ∀ P : D, HEq (S.adjunction P) (finiteHomRightAdjunction P) := by
  let S : CoefficientClosedStructure
      (Functor.uncurry.obj (MonoidalClosed.internalHom (C := D))) :=
    { monoidal := inferInstance
      adjunction := fun P ↦ finiteHomRightAdjunction (C := D) P
      evaluation_naturality := finiteHomEvaluation_naturality }
  refine ⟨S, ⟨rfl, fun P ↦ HEq.refl (finiteHomRightAdjunction P)⟩, ?_⟩
  intro T hT
  exact finiteHomClosed_ext T S hT.1 hT.2

private theorem finiteHomDerivedClosed_normalized
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    ∃! S, FiniteHomDerivedClosedNormalization C S := by
  let := finiteHomDerivedBraiding C
  exact finiteHomClosed_normalized

/-- Existence and uniqueness of the normalized closed record.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the published derived monoidal instance and the specified braiding of
its tensor-Hom adjunction. Naturality of evaluation supplies the last field.
The normalization fixes both data fields; all remaining fields are propositions. -/
theorem finiteHomEtaleClosed_existsUnique
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) : ∃! S, FiniteHomEtaleClosedNormalization A W S := by
  exact finiteHomDerivedClosed_normalized (Sheaf W.smallEtaleTopology A)

end ClosedProof

/-- The uniquely normalized etale closed structure, before specializing coefficients.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) := (finiteHomEtaleClosed_existsUnique A W).choose

/-- Closed etale structure for an arbitrary coefficient ring.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedRing (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :=
  finiteHomEtaleClosedGeneral (ModuleCat.{u + 1} R) W

/-- Shared closed and tensor data for the positive coefficient quotient diagram.
Source: blueprint successive quotient comparisons
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomQuotientClosedData
    (C : ℕ → Type a) [∀ n : ℕ, Category.{b} (C n)]
    (H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n)
    (F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m) where
  closed : ∀ n : ℕ, CoefficientClosedStructure (H n)
  tensor : ∀ {n m : ℕ} (h : m ≤ n),
    (closed n).tensor ⋙ F h ≅ (F h).prod (F h) ⋙ (closed m).tensor

/-- The canonical transpose within shared quotient data.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomQuotientClosedData.comparison
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F) {n m : ℕ} (h : m ≤ n) :=
  coefficientBaseChangeHom (S.closed n) (S.closed m) (F h) (S.tensor h)

/-- The published etale Hom, with its contravariant first input.
Source: blueprint derived Hom (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleInternalHom (n : ℕ) :=
  finiteHomEtaleInternalHomGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X

/-- Derived scalar extension in the recorded etale presentation.
Source: blueprint definition of T_B (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleReduction {n m : ℕ} (h : m ≤ n) :=
  Etale.scalarExtension (finiteHomQuotient l E h) X

/-- A closed family is fixed by its canonical records, with all category data shared.
Source: blueprint evaluation normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomClosedFamilyNormalizationAux
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    {V : ℕ → Type (max a b)} (v : ∀ n : ℕ, V n) : Prop :=
  ∀ n : ℕ, HEq (S.closed n) (v n)

/-- A scalar tensor family is fixed by its published isomorphisms.
Source: blueprint scalar tensor normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomTensorFamilyNormalizationAux
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    {V : ∀ {n m : ℕ}, m ≤ n → Type (max a b)}
    (v : ∀ {n m : ℕ} (h : m ≤ n), V h) : Prop :=
  ∀ (n m : ℕ) (h : m ≤ n), HEq (S.tensor h) (v h)

/-- The canonical derived closed record, specialized without changing its data.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedWitnessRing (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :=
  finiteHomEtaleClosedRing R W

/-- The canonical closed record at every positive coefficient level.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedWitness (n : ℕ) :=
  finiteHomEtaleClosedWitnessRing
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- The published tensor isomorphism at every positive quotient.
Source: blueprint scalar tensor normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTensorWitness {n m : ℕ} (h : m ≤ n) :=
  Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X

/-- The canonical normalization fixes every data field of the coefficient diagram.
Source: blueprint evaluation and scalar tensor maps
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomEtaleDataNormalization
    (S : FiniteHomQuotientClosedData (finiteHomEtale l E X)
      (finiteHomEtaleInternalHom l E X) (finiteHomEtaleReduction l E X)) : Prop where
  closed : FiniteHomClosedFamilyNormalizationAux S (finiteHomEtaleClosedWitness l E X)
  tensor : FiniteHomTensorFamilyNormalizationAux S (finiteHomEtaleTensorWitness l E X)

section

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteHomTensor_uncurry {D : Type a} [Category.{b} D]
    [MonoidalCategory D] : tensor D = Functor.uncurry.obj (curriedTensor D) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro P Q f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, tensor_map,
    Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using
      (MonoidalCategory.tensorHom_def f.1 f.2)

private theorem finiteHomClosed_tensor_uncurry
    {D : Type a} [Category.{b} D] (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (M : MonoidalCategory D)
    (h : S.monoidal = M) :
    S.tensor = Functor.uncurry.obj (@curriedTensor D _ M) := by
  let := M
  cases h
  exact finiteHomTensor_uncurry

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteHomClosedGeneral_tensor_uncurry
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :
    (finiteHomEtaleClosedGeneral A W).tensor =
      Functor.uncurry.obj (Etale.derivedTensor A W) := by
  unfold Etale.derivedTensor
  exact finiteHomClosed_tensor_uncurry _ _ _
    (finiteHomEtaleClosed_existsUnique A W).choose_spec.1.1

attribute [local irreducible] finiteHomEtaleClosedGeneral Etale.derivedHom
  finiteHomEtaleClosedWitness finiteHomEtaleClosedWitnessRing finiteHomEtaleClosedRing

private theorem finiteHomQuotientData_normalized
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (c : ∀ n, CoefficientClosedStructure (H n))
    (T : ∀ n, C n × C n ⥤ C n) (hc : (fun n ↦ (c n).tensor) = T)
    (t : ∀ {n m : ℕ} (h : m ≤ n), T n ⋙ F h ≅ (F h).prod (F h) ⋙ T m) :
    ∃! S : FiniteHomQuotientClosedData C H F,
      (∀ n, S.closed n = c n) ∧ ∀ n m h, HEq (S.tensor (n := n) (m := m) h) (t h) := by
  cases hc
  refine ⟨⟨c, t⟩, ⟨fun _ ↦ rfl, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨c', t'⟩ ⟨hc', ht'⟩
  have hclosed : c' = c := funext hc'
  cases hclosed
  have htensor : @t' = @t := by
    funext n m h
    exact eq_of_heq (ht' n m h)
  cases htensor
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient diagram has uniquely normalized closed and tensor data.
Source: blueprint evaluation and coefficient-change paragraphs
(blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the canonical derived closed structure and the published scalar tensor
isomorphisms. The site's tensor and Hom are their underlying functors, so these
components have the required types. Heterogeneous equality fixes each field;
function extensionality and record extensionality prove uniqueness. -/
theorem finiteHomEtaleData_existsUnique :
    ∃! S, FiniteHomEtaleDataNormalization l E X S := by
  have hc (n : ℕ) : (finiteHomEtaleClosedWitness l E X n).tensor =
      Functor.uncurry.obj (Etale.derivedTensor (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) := by
    unfold finiteHomEtaleClosedWitness finiteHomEtaleClosedWitnessRing finiteHomEtaleClosedRing
    exact finiteHomClosedGeneral_tensor_uncurry _ X
  obtain ⟨S, hS, huniq⟩ := finiteHomQuotientData_normalized
    (finiteHomEtaleClosedWitness l E X) _ (funext hc)
    (fun {_ _} h ↦ finiteHomEtaleTensorWitness l E X h)
  refine ⟨S, ⟨fun n ↦ heq_of_eq (hS.1 n), hS.2⟩, ?_⟩
  intro S' hS'
  apply huniq S'
  exact ⟨fun n ↦ eq_of_heq (hS'.closed n), hS'.tensor⟩

end

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The canonical etale coefficient diagram, with every data field fixed.
Source: blueprint evaluation and coefficient-change paragraphs
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleData := (finiteHomEtaleData_existsUnique l E X).choose

/-- The canonical closed structure at one coefficient level.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosed (n : ℕ) :
    CoefficientClosedStructure (finiteHomEtaleInternalHom l E X n) :=
  (finiteHomEtaleData l E X).closed n

/-- The published canonical scalar tensor comparison.
Source: blueprint coefficient change (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensor {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomEtaleReduction l E X h ≅
      (finiteHomEtaleReduction l E X h).prod (finiteHomEtaleReduction l E X h) ⋙
        (finiteHomEtaleClosed l E X m).tensor :=
  (finiteHomEtaleData l E X).tensor h

/-- The etale arrow is exactly the closed transpose of reduced evaluation.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
The body is the evaluation-defined `coefficientBaseChangeHom`; it does not
select an unconstrained arrow from an existence theorem. -/
abbrev etaleFiniteHomCanonical {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    (finiteHomEtaleReduction l E X h).obj
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ⟶
      (finiteHomEtaleInternalHom l E X m).obj
        (op ((finiteHomEtaleReduction l E X h).obj K),
          (finiteHomEtaleReduction l E X h).obj M) :=
  coefficientBaseChangeHom (finiteHomEtaleClosed l E X n)
    (finiteHomEtaleClosed l E X m) (finiteHomEtaleReduction l E X h)
    (finiteHomEtaleTensor l E X h) K M

/-- The intrinsic pro-etale arrow is the published normalized quotient transpose.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev proEtaleFiniteHomCanonical {n m : ℕ} (h : m ≤ n)
    (K M : normalizedDVRDerived l E X n) := finiteIntrinsicReductionHom l E X h K M

/-- The canonical reassociation of intrinsic scalar extensions, as a left-adjoint mate.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomIntrinsicAssoc {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :=
  Adjunction.leftAdjointCompIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction k)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (k.trans h)) (normalizedDVRResComp l E X h k)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteHomLift_comp
    {R : Type a} [CommRing R] (I J K : Ideal R) (h : I ≤ J) (k : J ≤ K) :
    (Ideal.Quotient.factor (h.trans k)).ulift =
      (Ideal.Quotient.factor k).ulift.comp (Ideal.Quotient.factor h).ulift := by
  apply RingHom.ext
  intro x
  apply ULift.down_injective
  exact (Ideal.Quotient.factor_comp_apply h k x.down).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Quotient maps compose as the actual quotient factor homomorphisms.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: lift to the valuation ring using quotient induction; both composites send
an element to its residue class at exponent r + 1. -/
theorem finiteHomQuotient_comp {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    finiteHomQuotient l E (k.trans h) =
      (finiteHomQuotient l E k).comp (finiteHomQuotient l E h) := by
  apply finiteHomLift_comp

/-- The canonical etale scalar associator, with quotient-factor equality.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleAssoc {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :=
  ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology
    (finiteHomQuotient l E h) (finiteHomQuotient l E k)
    (finiteHomQuotient l E (k.trans h)) (finiteHomQuotient_comp l E h k)

/-- Small coproducts of etale module sheaves, exposed before totalizing complexes.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
instance finiteHomEtaleSmallColimits (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  hasColimitsOfSizeShrink _

/-- Every pair of etale module complexes has its signed total tensor product.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: module-valued sheaves have small coproducts. In each integer degree the
required coproduct is indexed by the set of pairs of integers with prescribed sum,
which is small. These coproducts provide HasMapBifunctor and hence HasTensor. -/
@[instance] theorem finiteHomEtaleHasTensor
    (R : Type (u + 1)) [CommRing R] (W : Scheme.{u})
    (P Q : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
    HomologicalComplex.HasTensor P Q := by
  infer_instance

/-- The ordinary sheaf tensor generator before deriving.
Source: blueprint pure-tensor comparison; Stacks 03EK
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorSection (n : ℕ)
    (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)) :
    (M ⊗ N).obj.obj (op U) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) M N).app (op U))
      (x ⊗ₜ y)

/-- Inclusion of one signed-total-tensor summand with shared monoidal data.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomTensorInclusionGeneral
    {C : Type a} [Category.{b} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (HomologicalComplex.tensorObj P Q).X k :=
  HomologicalComplex.ιTensorObj P Q p q k h

/-- Signed-total inclusion with its shared native tensor object as codomain.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomNativeTensorInclusionGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : (finiteHomNativeTensorDataGeneral C (hD := hD)).cochain)
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶
      ((finiteHomNativeTensorDataGeneral C (hD := hD)).cochainTensor.obj (P, Q)).X k :=
  finiteHomTensorInclusionGeneral P Q p q k h

/-- The same native summand inclusion before specializing the coefficient category.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorInclusionGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : finiteHomEtaleCochainGeneral A W)
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (finiteHomEtaleTotalObjectGeneral A W P Q).X k :=
  finiteHomNativeTensorInclusionGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf W.smallEtaleTopology A))) P Q p q k h

/-- Localization in the published small etale derived category.
Source: blueprint etale size convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleQ (n : ℕ) :=
  (finiteHomEtaleTensorSourceGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).localization

/-- Localization in the recorded intrinsic standard derived category.
Source: blueprint intrinsic size convention
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomIntrinsicQ (n : ℕ) :
    CochainComplex (normalizedDVRModules l E X n) ℤ ⥤ normalizedDVRDerived l E X n :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  DerivedCategory.Q

/-- Tensor representatives with all category and functor data kept shared.
Source: blueprint tensor representative calculation
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomQuotientClosedData.Representatives
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (A : ℕ → Type c) [∀ n : ℕ, Category.{d} (A n)]
    (Q : ∀ n : ℕ, A n ⥤ C n) (T : ∀ n : ℕ, A n → A n → A n)
    (I : Type e) (V : I → Type f) where
  generator : ∀ i : I, V i
  model : ∀ (n : ℕ) (P R : A n),
    (S.closed n).tensor.obj ((Q n).obj P, (Q n).obj R) ⟶ (Q n).obj (T n P R)

/-- Representative fields from a family of shared tensor source records.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev FiniteHomQuotientClosedData.Representatives.fromSources
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (N : ∀ n, FiniteHomTensorSourceData (C n)) (I : Type e) (V : I → Type f) :=
  letI : ∀ n, Category (N n).cochain := fun n ↦ (N n).cochainCategory
  S.Representatives (fun n ↦ (N n).cochain) (fun n ↦ (N n).localization)
    (fun n P Q ↦ (N n).cochainTensor.obj (P, Q)) I V

/-- Pointwise normalization of representative generators and model maps.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomQuotientClosedData.Representatives.Normalization
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    {S : FiniteHomQuotientClosedData C H F}
    {A : ℕ → Type c} [∀ n : ℕ, Category.{d} (A n)]
    {Q : ∀ n : ℕ, A n ⥤ C n} {T : ∀ n : ℕ, A n → A n → A n}
    {I : Type e} {V : I → Type f}
    (R : S.Representatives A Q T I V) (v : ∀ i : I, V i)
    {M : ∀ n : ℕ, A n → A n → Type b} (t : ∀ n P Z, M n P Z) : Prop where
  generator : ∀ i, HEq (R.generator i) (v i)
  model : ∀ n P Z, HEq (R.model n P Z) (t n P Z)

/-- A local pair of sections in a prescribed total-tensor degree.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomEtaleTensorSectionInput where
  n : ℕ
  P : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
  Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
  p : ℤ
  q : ℤ
  k : ℤ
  h : p + q = k
  U : X.Etale
  x : (P.X p).obj.obj (op U)
  y : (Q.X q).obj.obj (op U)

/-- The actual total tensor object of two etale cochain complexes.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTotalObject (n : ℕ)
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) :=
  finiteHomEtaleTotalObjectGeneral _ X P Q

/-- The carrier in which a prescribed total-tensor generator lies.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTensorSectionCarrier (i : FiniteHomEtaleTensorSectionInput l E X) :
    Type (u + 1) :=
  ((finiteHomEtaleTotalObject l E X i.n i.P i.Q).X i.k).obj.obj (op i.U)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The total-summand generator before specializing the coefficient ring.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleCanonicalTensorSectionGeneral
    (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1} B) W)
    (p q k : ℤ) (h : p + q = k) (U : W.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    ((finiteHomEtaleTotalObjectGeneral (ModuleCat.{u + 1} B) W P Q).X k).obj.obj (op U) :=
  ((finiteHomEtaleTensorInclusionGeneral (ModuleCat.{u + 1} B) W
      P Q p q k h).hom.app (op U)).hom'
    (((Functor.LaxMonoidal.μ (sheafToPresheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} B)) (P.X p) (Q.X q)).app (op U)).hom' (x ⊗ₜ y))

/-- The prescribed total-summand generator, with its carrier shared explicitly.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleCanonicalTensorSection (i : FiniteHomEtaleTensorSectionInput l E X) :
    finiteHomEtaleTensorSectionCarrier l E X i :=
  finiteHomEtaleCanonicalTensorSectionGeneral _ X i.P i.Q i.p i.q i.k i.h i.U i.x i.y

/-- Canonical generators and localization tensorators in the recorded etale categories.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev FiniteHomEtaleRepresentativeData :=
  FiniteHomQuotientClosedData.Representatives.fromSources (finiteHomEtaleData l E X)
    (fun n ↦ finiteHomEtaleTensorSourceGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
    (FiniteHomEtaleTensorSectionInput l E X) (finiteHomEtaleTensorSectionCarrier l E X)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Both representative maps are fixed by existing tensor constructions.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop :=
  S.Normalization (finiteHomEtaleCanonicalTensorSection l E X)
    (fun n ↦ finiteHomEtaleLocalizationTensorModelGeneral
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) X)

section RepresentativeProof
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

private theorem finiteHomClosedGeneral_tensor_native
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :
    (finiteHomEtaleClosedGeneral A W).tensor = finiteHomEtaleDerivedTensorGeneral A W := by
  exact congrArg (fun M : MonoidalCategory (DerivedCategory (Sheaf W.smallEtaleTopology A)) ↦
    @tensor _ _ M) (finiteHomEtaleClosed_existsUnique A W).choose_spec.1.1

private theorem finiteHomRepresentatives_normalized
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (A : ℕ → Type c) [∀ n : ℕ, Category.{d} (A n)]
    (Q : ∀ n : ℕ, A n ⥤ C n) (T : ∀ n : ℕ, A n → A n → A n)
    {I : Type e} {V : I → Type f} (v : ∀ i : I, V i)
    (U : ∀ n : ℕ, C n × C n ⥤ C n)
    (hU : (fun n ↦ (S.closed n).tensor) = U)
    (t : ∀ (n : ℕ) (P R : A n),
      (U n).obj ((Q n).obj P, (Q n).obj R) ⟶ (Q n).obj (T n P R)) :
    ∃! R : S.Representatives A Q T I V, R.Normalization v t := by
  cases hU
  refine ⟨⟨v, t⟩, ⟨fun _ ↦ HEq.rfl, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨v', t'⟩ h
  have hv' : v' = v := funext (fun i ↦ eq_of_heq (h.generator i))
  have ht' : t' = t := by
    funext n P Z
    exact eq_of_heq (h.model n P Z)
  cases hv'
  cases ht'
  rfl

/-- The local generators and localization tensorator determine the representative data.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: define totalSection by the ordinary sheaf tensor generator followed by the
actual total-summand inclusion. The closed normalization identifies its tensor
with the published derived tensor. Transport the localization tensorator along
that equality to define tensorModel. These constructions give the stated
heterogeneous equalities. Each equality fixes a field value; function and record
extensionality therefore prove uniqueness of the entire representative family. -/
theorem finiteHomEtaleRepresentativeData_existsUnique :
    ∃! S, FiniteHomEtaleRepresentativeNormalization l E X S := by
  let : ∀ n : ℕ, Category.{u + 1} (finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) :=
    fun n ↦ (finiteHomEtaleTensorSourceGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X).cochainCategory
  have hc (n : ℕ) : ((finiteHomEtaleData l E X).closed n).tensor =
      finiteHomEtaleDerivedTensorGeneral (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X := by
    exact (congrArg CoefficientClosedStructure.tensor
      (eq_of_heq ((finiteHomEtaleData_existsUnique l E X).choose_spec.1.closed n))).trans
        (finiteHomClosedGeneral_tensor_native _ X)
  exact finiteHomRepresentatives_normalized
    (finiteHomEtaleData l E X) _ (finiteHomEtaleQ l E X)
    (finiteHomEtaleTotalObject l E X) (finiteHomEtaleCanonicalTensorSection l E X)
    _ (funext hc) (fun n ↦ finiteHomEtaleLocalizationTensorModelGeneral
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) X)

end RepresentativeProof

/-- The uniquely specified local generators and localization tensorator.
Source: blueprint site formula (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleRepresentativeData :=
  (finiteHomEtaleRepresentativeData_existsUnique l E X).choose

/-- The actual localization tensorator with the normalized closed-tensor endpoint.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorModel (n : ℕ)
    (P Q : finiteHomEtaleCochainGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) :=
  (finiteHomEtaleRepresentativeData l E X).model n P Q

end WeilConjectures
