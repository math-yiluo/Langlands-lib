/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # The canonical successive condensed scalar mate

Source: the formal-properties paragraph of the current blueprint scalar
direct-image proof. The two coefficient changes are the published integral
localization and finite-field inclusion into the finite-subextension-valued
condensed algebraic closure.
(blueprint: def-sf-native-proper-scalar-mate-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom
  AlgebraicGeometry.ProEtale.CondensedRing.localizedDirectImageComparison

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicGeometry.ProEtale

/-- Tensoring internal modules preserves the coproducts used in the fourfold
graded tensor comparison, since the module category is closed monoidal.
Source: Mathlib's closed monoidal colimit preservation.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
@[instance_reducible] def nativeScalarModuleClosed (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R] :
    MonoidalClosed (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :=
  @Mod.monoidalClosed _ _ _ _ _ _ _ R _ hcomm

attribute [local instance] nativeScalarModuleClosed

/-- Symmetry of the canonical relative module tensor.
Source: the relative tensor construction in the adopted library.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
@[instance_reducible] def nativeScalarModuleSymmetric (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R] :
    SymmetricCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :=
  @Mod.symmetricCategory _ _ _ _ _ _ _ R _ hcomm

/-- Canonical functorial flat resolutions of internal modules.
Source: the adopted library's module-object flat resolution.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleFlatResolution (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :=
  @Mod.hasFunctorialFlatResolution _ _ _ _ _ _ _ R _ hcomm _

attribute [local instance] nativeScalarModuleSymmetric nativeScalarModuleFlatResolution

/-- Left tensor of internal modules preserves small colimits.
Source: closed monoidal adjunction.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleLeftColimits (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
  have := nativeScalarModuleClosed T R
  infer_instance

/-- Right tensor of internal modules preserves small colimits.
Source: closed symmetric monoidal adjunction.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleRightColimits (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) := by
  have := nativeScalarModuleClosed T R
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

attribute [local instance] nativeScalarModuleLeftColimits nativeScalarModuleRightColimits

/-- Fourfold graded tensor compatibility from closedness.
Source: Mathlib closed monoidal colimit preservation.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleTensorFour (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C D : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasTensor₄ObjExt A B C D := by
  intro A B C D i j
  have : MonoidalClosed (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R) :=
    nativeScalarModuleClosed T R
  have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft (A i)) := inferInstance
  change PreservesColimit _ (MonoidalCategory.tensorLeft (A i))
  infer_instance

/-- The left-associated graded tensor commutes with the defining coproduct.
Source: Mathlib graded monoidal associator construction.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleGoodTensorLeft (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro A B C
  infer_instance

/-- The right-associated graded tensor commutes with the defining coproduct.
Source: Mathlib graded monoidal associator construction.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarModuleGoodTensorRight (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro A B C
  infer_instance

attribute [local instance] nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft
  nativeScalarModuleGoodTensorRight
attribute [local irreducible] Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct

/-- Integral coefficient localization is exact.
Source: the proved localization theorem `padicIntegers_invertEll`.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
theorem nativeScalarIntegralExact (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield T l E)) :=
  (padicIntegers_invertEll T l E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2

attribute [local instance] nativeScalarIntegralExact

/-- The published derived integral-to-field scalar functor, named once.
Source: the canonical derived extension of scalars along integral localization.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
def nativeScalarIntegralDerived (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) T)) :=
  (Mod.extendScalars (padicIntegersToPadicSubfield T l E)).leftDerivedFunctor

/-- The published derived finite-field-to-closure scalar functor, named once.
Source: the canonical derived extension for the finite-subfield inclusion.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
def nativeScalarClosureDerived (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) T)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)) :=
  (Mod.extendScalars (coefficientMap
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)).leftDerivedFunctor

/-- The actual composite of the two published coefficient-change mates.
Both factors are constructed for arbitrary morphisms and unbounded complexes.
Source: the formal-properties paragraph of the blueprint scalar direct-image proof.
(blueprint: def-sf-native-proper-scalar-mate-data). -/
def nativeScalarCondensedComposite (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {U V : Scheme.{u}} (g : U ⟶ V)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) U))) :
    (nativeScalarClosureDerived V l E).obj
        ((nativeScalarIntegralDerived V l E).obj
          ((CondensedRing.moduleObjectDerivedPushforward
            (Profinite.padicIntegersRingObj l E.1) g).obj C)) ⟶
      (CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) g).obj
          ((nativeScalarClosureDerived U l E).obj
            ((nativeScalarIntegralDerived U l E).obj C)) :=
  (nativeScalarClosureDerived V l E).map
      (CondensedRing.localizedDirectImageComparison l E g C) ≫
    (CondensedRing.derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g).app
        ((nativeScalarIntegralDerived U l E).obj C)

end WeilConjectures.LocallyFiniteAdicCompactSupport
