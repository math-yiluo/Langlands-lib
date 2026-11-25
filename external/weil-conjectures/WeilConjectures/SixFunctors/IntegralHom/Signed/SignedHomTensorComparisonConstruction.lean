/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Naturality of the uncurried tensor--Hom construction

Source: the finite-free construction in the first paragraph of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 08J9 and 0A8X.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a₀ b₀
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

include Y R

open CategoryTheory.MonoidalCategory CategoryTheory.RingedDerivedNative
attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose

@[instance_reducible]
private noncomputable def signedModuleMonoidal : MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.cochainModulesMonoidal R
attribute [local instance] signedModuleMonoidal
@[instance_reducible]
private noncomputable def signedModuleSymmetric : SymmetricCategory (Modules.{t, u} Y R) :=
  SheafOfModules.cochainModulesSymmetric R
attribute [local instance] signedModuleSymmetric
private theorem signedModulePreadditive : MonoidalPreadditive (Modules.{t, u} Y R) :=
  SheafOfModules.cochainModulesPreadditive R
attribute [local instance] signedModulePreadditive
@[instance_reducible]
private noncomputable def signedModuleClosed : MonoidalClosed (Modules.{t, u} Y R) :=
  baseClosed.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
attribute [local instance] signedModuleClosed
private theorem signedModuleLimits : HasLimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  baseLimits.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
attribute [local instance] signedModuleLimits
private theorem signedModuleColimits : HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  baseColimits.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
attribute [local instance] signedModuleColimits
private theorem signedGradedTensor (X Z : GradedObject ℤ (Modules.{t, u} Y R)) :
    X.HasTensor Z :=
  gradedTensor.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R X Z
attribute [local instance] signedGradedTensor
private theorem signedGradedTensorFour (W X Z V : GradedObject ℤ (Modules.{t, u} Y R)) :
    GradedObject.HasTensor₄ObjExt W X Z V :=
  gradedTensorFour.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R W X Z V
attribute [local instance] signedGradedTensorFour
private theorem signedGradedTensorLeft (X Z V : GradedObject ℤ (Modules.{t, u} Y R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Z V :=
  gradedTensorLeft.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R X Z V
attribute [local instance] signedGradedTensorLeft
private theorem signedGradedTensorRight (X Z V : GradedObject ℤ (Modules.{t, u} Y R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Z V :=
  gradedTensorRight.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R X Z V
attribute [local instance] signedGradedTensorRight

@[instance_reducible]
private noncomputable def signedComplexMonoidal :
    MonoidalCategory (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  HomologicalComplex.monoidalCategory (Modules.{t, u} Y R) (.up ℤ)
attribute [local instance 5000] signedComplexMonoidal
@[instance_reducible]
private noncomputable def signedComplexStruct :
    MonoidalCategoryStruct (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  (signedComplexMonoidal Y R).toMonoidalCategoryStruct
attribute [local instance 10000] signedComplexStruct
@[instance_reducible]
private noncomputable def signedComplexBraided :
    BraidedCategory (CochainComplex (Modules.{t, u} Y R) ℤ) :=
  CochainComplex.Monoidal.braidedCategory
attribute [local instance 5000] signedComplexBraided

omit Y R

/-- The uncurry expression for tensor--Hom exchange is natural in its coefficient object.
Source: associator and braiding naturality in Mathlib, used in the finite-free
construction of the blueprint's first paragraph
(blueprint: lem-sf-braided-hom-tensor-exchange-naturality).

Proof: move the coefficient map through the first associator, through the middle
braiding, and through the inverse associator; interchange it with evaluation
on the other tensor factor. Each move is a monoidal naturality identity. -/
theorem braidedTensorExchange_naturality {V : Type a₀} [Category.{b₀} V]
    [MonoidalCategory V] [BraidedCategory V]
    (M P I Q Q' : V) (ev : M ⊗ P ⟶ I) (g : Q ⟶ Q') :
    ((M ◁ g) ▷ P) ≫ (α_ M Q' P).hom ≫ M ◁ (β_ Q' P).hom ≫
        (α_ M P Q').inv ≫ ev ▷ Q' =
      (α_ M Q P).hom ≫ M ◁ (β_ Q P).hom ≫
        (α_ M P Q).inv ≫ ev ▷ Q ≫ I ◁ g := by
  rw [associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
    ← whisker_exchange]

include Y R

attribute [local irreducible] homComplexFunctor chainEquiv SheafOfModules.monoidalCategory

private noncomputable def signedGenerator
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ)
    (a b k : ℤ) (h : a + b = k) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (y : (B.X b).val.obj U) :
    ((A ⊗ B).X k).val.obj U :=
  coefficientTensorGenerator.{u, t + 1, t}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R A B a b k h U x y

attribute [local irreducible] signedGenerator

private noncomputable def exchangeEquiv
    (A P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    (A ⊗ P ⟶ I) ≃
      (A ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) :=
  chainEquiv.{t + 1, t, u} (AlgebraicGeometry.Scheme.ProEt.topology Y) R A P I

attribute [local irreducible] exchangeEquiv

private theorem exchangeEquiv_symm_pure
    (A P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (v : A ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)
    (a p k : ℤ) (h : a + p = k) (h' : p + a = k)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (y : (P.X p).val.obj U) :
    (((exchangeEquiv.{t, u} Y R A P I).symm v).f k).val.app U
        (signedGenerator.{t, u} Y R A P a p k h U x y) =
      (((v.f a ≫ homComplexπ P I a p k h').val.app U x).app
        (op (Over.mk (𝟙 U.unop))) y) := by
  unfold exchangeEquiv signedGenerator
  exact chainEquiv_symm_pure.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R A P I v a p k h h' U x y

private noncomputable def exchangeUncurry
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) :
    (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I ⊗ Q) ⊗ P ⟶ I ⊗ Q :=
  (α_ _ _ _).hom ≫ _ ◁ (β_ Q P).hom ≫ (α_ _ _ _).inv ≫
    (exchangeEquiv.{t, u} Y R
      (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) P I).symm (𝟙 _) ▷ Q

attribute [local irreducible] exchangeUncurry

private theorem exchangeUncurry_naturality
    (P I Q Q' : CochainComplex (Modules.{t, u} Y R) ℤ) (g : Q ⟶ Q') :
    ((homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I ◁ g) ▷ P) ≫
        exchangeUncurry.{t, u} Y R P I Q' =
      exchangeUncurry.{t, u} Y R P I Q ≫ I ◁ g := by
  unfold exchangeUncurry
  exact braidedTensorExchange_naturality _ _ _ _ _ _ g

private noncomputable def exchangeMap
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) :
    homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I ⊗ Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P (I ⊗ Q) :=
  exchangeEquiv.{t, u} Y R
    _ _ _ (exchangeUncurry.{t, u} Y R P I Q)

attribute [local irreducible] exchangeMap

private theorem uncurry_precompose
    (A B P I : CochainComplex (Modules.{t, u} Y R) ℤ) (f : A ⟶ B)
    (v : B ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) :
    (exchangeEquiv.{t, u} Y R
      A P I).symm (f ≫ v) = f ▷ P ≫
        (exchangeEquiv.{t, u} Y R
          B P I).symm v := by
  unfold exchangeEquiv
  have h := chainEquiv_symm_naturality.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R B A P P I I f (𝟙 P) (𝟙 I) v
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.comp_id] at h
  erw [totalTensor_map_eq, tensorHom_id] at h
  exact h

private theorem uncurry_postcompose
    (A P I I' : CochainComplex (Modules.{t, u} Y R) ℤ) (f : I ⟶ I')
    (v : A ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) :
    (exchangeEquiv.{t, u} Y R
      A P I').symm (v ≫
        ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op P)).map f) =
      (exchangeEquiv.{t, u} Y R
        A P I).symm v ≫ f := by
  unfold exchangeEquiv
  have h := chainEquiv_symm_naturality.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R A A P P I I' (𝟙 A) (𝟙 P) f v
  have hi := (coefficientTotalTensor.{u, t + 1, t}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R).map_id (A, P)
  erw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, hi,
    Category.id_comp, Category.id_comp] at h
  exact h

private theorem exchangeMap_uncurry (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ) :
    (exchangeEquiv.{t, u} Y R
      (_ ⊗ Q) P (I ⊗ Q)).symm (exchangeMap.{t, u} Y R P I Q) =
        exchangeUncurry.{t, u} Y R P I Q := by
  unfold exchangeMap
  exact Equiv.symm_apply_apply _ _

private theorem exchangeMap_precompose
    (P I Q Q' : CochainComplex (Modules.{t, u} Y R) ℤ) (g : Q ⟶ Q') :
    (exchangeEquiv.{t, u} Y R
      (_ ⊗ Q) P (I ⊗ Q')).symm
        ((_ ◁ g) ≫ exchangeMap.{t, u} Y R P I Q') =
      ((_ ◁ g) ▷ P) ≫ exchangeUncurry.{t, u} Y R P I Q' := by
  let M := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  exact (uncurry_precompose.{t, u} Y R (M ⊗ Q) (M ⊗ Q') P (I ⊗ Q')
    (M ◁ g) (exchangeMap.{t, u} Y R P I Q')).trans
    (congrArg (fun v : (M ⊗ Q') ⊗ P ⟶ I ⊗ Q' ↦ ((M ◁ g) ▷ P) ≫ v)
      (exchangeMap_uncurry.{t, u} Y R P I Q'))

private theorem exchangeMap_postcompose
    (P I Q Q' : CochainComplex (Modules.{t, u} Y R) ℤ) (g : Q ⟶ Q') :
    (exchangeEquiv.{t, u} Y R
      (_ ⊗ Q) P (I ⊗ Q')).symm
        (exchangeMap.{t, u} Y R P I Q ≫
          ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := R)).obj (op P)).map (I ◁ g)) =
      exchangeUncurry.{t, u} Y R P I Q ≫ I ◁ g := by
  let M := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  exact (uncurry_postcompose.{t, u} Y R (M ⊗ Q) P (I ⊗ Q) (I ⊗ Q')
    (I ◁ g) (exchangeMap.{t, u} Y R P I Q)).trans
    (congrArg (fun v : (M ⊗ Q) ⊗ P ⟶ I ⊗ Q ↦ v ≫ I ◁ g)
      (exchangeMap_uncurry.{t, u} Y R P I Q))

private noncomputable def exchangeNatural
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) :
    (totalTensor.{t, u} Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I) ⟶
      (totalTensor.{t, u} Y R).obj I ⋙
        (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op P) where
  app Q := exchangeMap.{t, u} Y R P I Q
  naturality {Q Q'} g := by
    change (_ ◁ g) ≫ exchangeMap.{t, u} Y R P I Q' =
      exchangeMap.{t, u} Y R P I Q ≫
        ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
          (R := R)).obj (op P)).map (I ◁ g)
    apply (exchangeEquiv.{t, u} Y R
      (_ ⊗ Q) P (I ⊗ Q')).symm.injective
    exact (exchangeMap_precompose.{t, u} Y R P I Q Q' g).trans
      ((exchangeUncurry_naturality.{t, u} Y R P I Q Q' g).trans
        (exchangeMap_postcompose.{t, u} Y R P I Q Q' g).symm)

end WeilConjectures.IntegralHom
