/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionScalarNormalization
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

set_option linter.privateModule false

/-! # Computing integral reduction on an arbitrary representative

Source: the finite-free quotient resolution in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7, and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

private noncomputable def tensorTowerFunctor
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex (Modules.{t, u} Y R) ℤ ⥤ (ℕᵒᵖ ⥤ Derived.{t, u} Y R) where
  obj N := S ⋙ (totalTensor.{t, u} Y R).obj N ⋙ DerivedCategory.Q
  map f := Functor.whiskerRight
    (Functor.whiskerLeft S ((totalTensor.{t, u} Y R).map f)) DerivedCategory.Q
  map_id N := by ext n; simp
  map_comp f g := by ext n; simp

private theorem koszul_augmentation_tensor_quasiIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P) (n : ℕ) :
    QuasiIso ((PrincipalKoszulStrictReplacement.comparison l E Y P).app (op n)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let M := PrincipalKoszulStrictReplacement.Modules l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let : MonoidalCategory M := SheafOfModules.monoidalCategory R
  let : SymmetricCategory M := SheafOfModules.symmetricCategory R
  let : MonoidalPreadditive M := SheafOfModules.tensorPreadditive R
  have (X : M) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X) := by
    have : PreservesColimitsOfSize.{max u (t + 1), max u (t + 1)}
        (MonoidalCategory.tensorLeft X) :=
      SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R X
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft X)
  have (X : M) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let f := PrincipalKoszulStrictReplacement.augmentation l E Y n
  have hf := PrincipalKoszulStrictReplacement.augmentation_quasiIso l E Y n
  have := kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
  exact PrincipalKoszulStrictReplacement.quasiIso_conjugate
    (CochainComplex.Monoidal.braiding P (PrincipalKoszulStrictReplacement.koszul l E Y n))
    (CochainComplex.Monoidal.braiding P
      ((CochainComplex.singleFunctor M 0).obj
        (PrincipalKoszulStrictReplacement.residue l E Y n)))
    _ ((koszulTensorFunctor R P).map f)
    (CochainComplex.Monoidal.braiding_naturality_right (K := P) f)

private noncomputable def scalarReductionTowerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    PrincipalKoszulStrictReplacement.targetTower l E Y P ⋙ DerivedCategory.Q ≅
      integralReductionTower l E Y D hl P := by
  let F := ((CompletedTowerIndependent.reductionComplex l E Y).obj P).asFunctor
  let a : F ⋙ DerivedCategory.Q ⟶ integralReductionTower l E Y D hl P :=
    NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (by
      intro n
      dsimp only [Functor.comp_map]
      rw [FiniteReductionTower.reduction_step]
      simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rw [integralTowerTransition_eq]
      rfl)
  exact Functor.isoWhiskerRight (FiniteReductionTower.scalarTowerIso l E Y P)
    DerivedCategory.Q ≪≫ NatIso.ofComponents (fun n ↦ Iso.refl _) (fun f ↦ a.naturality f)

end WeilConjectures.IntegralHom
