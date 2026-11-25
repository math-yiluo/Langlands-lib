/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Underlying sheaf extensionality for nested scalar tensors

Source: Stacks Project, Tag 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-nested-chosen-scalar-tensor-val-ext)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] completedScalarChangeData
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

namespace NestedChosenTensorProof

private abbrev restriction := SheafOfModules.restrictScalars.{u + 1, u, u + 1, u + 1}
  ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedCoefficientMap.{u, u} l L F j X))

private theorem adjData :
    ∃ a : completedOrdinaryScalarExtension.{u, u} l L F j X ⊣ restriction l L F j X,
      ∀ (M : integralTowerModules.{u, u} l L X) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          completedScalarTensorSection.{u, u} l L F j X M U 1 x := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} X
  have hobj (M : integralTowerModules.{u, u} l L X) :
      (completedOrdinaryScalarExtension.{u, u} l L F j X).obj M =
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (completedCoefficientMap.{u, u} l L F j X) M :=
    completedOrdinaryScalarExtension_obj.{u, u} l L F j X M
  have hmap {M N : integralTowerModules.{u, u} l L X} (f : M ⟶ N) :
      (completedOrdinaryScalarExtension.{u, u} l L F j X).map f =
        eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
            (completedCoefficientMap.{u, u} l L F j X) M f ≫
          eqToHom (hobj N).symm :=
    completedOrdinaryScalarExtension_map.{u, u} l L F j X f
  obtain ⟨a, ha⟩ :=
    (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction.{u + 1, u + 1, u}
      (C := X.ProEt) (J := Scheme.ProEt.topology X)
      (O := completedIntegralCommRingSheafUnrestricted.{u, u} l L X)
      (O' := completedIntegralCommRingSheafUnrestricted.{u, u} l F X)
      (completedCoefficientMap.{u, u} l L F j X)).choose_spec.choose_spec
        (completedOrdinaryScalarExtension.{u, u} l L F j X)
        hobj hmap
  refine ⟨a, ?_⟩
  intro M U x
  change (show ((completedOrdinaryScalarExtension.{u, u} l L F j X).obj M).val.obj U from
    (a.unit.app M).val.app U x) = _
  let e := eqToIso (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M)
  have h := ha M ((completedOrdinaryScalarExtension.{u, u} l L F j X).obj M) e.inv U x
  have he : eqToHom (completedOrdinaryScalarExtension_obj.{u, u} l L F j X M) ≫ e.inv =
      𝟙 _ := e.hom_inv_id
  rw [he] at h
  rw [Adjunction.homEquiv_id] at h
  dsimp only [completedScalarTensorSection, e, eqToIso.inv,
    completedOrdinaryScalarExtension] at h ⊢
  with_unfolding_all exact h

end NestedChosenTensorProof

/--
Tensor induction and sheafification identify the underlying presheaf maps of two
morphisms in a nested completed scalar extension whenever they agree on nested
pure tensor sections. This is the sectionwise tensor-induction substep; the
categorical equality of morphisms is obtained by `SheafOfModules.hom_ext`.

Source: Stacks 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-nested-chosen-scalar-tensor-val-ext)
-/
theorem nestedChosenScalarTensor_val_ext
    (M : integralTowerModules l E X)
    (Q : integralTowerModules l F X)
    (f g : (completedOrdinaryScalarExtension l L F j X).obj
      ((completedOrdinaryScalarExtension l E L ι X).obj M) ⟶ Q)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : M.val.obj U),
      f.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x)) =
      g.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x))) :
    f.val = g.val := by
  obtain ⟨a, ha⟩ := NestedChosenTensorProof.adjData l L F j X
  obtain ⟨b, hb⟩ := NestedChosenTensorProof.adjData l E L ι X
  have hf : f = g := by
    apply (a.homEquiv _ _).injective
    apply (b.homEquiv _ _).injective
    ext U x
    simp only [Adjunction.homEquiv_unit]
    change f.val.app U ((a.unit.app _).val.app U ((b.unit.app M).val.app U x)) =
      g.val.app U ((a.unit.app _).val.app U ((b.unit.app M).val.app U x))
    rw [ha, hb]
    exact h U 1 1 x
  exact congrArg (fun k ↦ k.val) hf

end WeilConjectures
