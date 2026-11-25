/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexes
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Explicit reassociation of native total tensor complexes

Source: Stacks 0FPQ, 06YU, 0FPT. All constructions precede derived localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

/-- The total in actual tensor-factor order, reversing the curried parameters.
Source: Stacks 0FPQ (blueprint: lem-sf-native-weil-ringed-triple-complex). -/
abbrev nativeTensorComplex (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
  CochainComplex.mapBifunctor Q P T

/-- Identify the left-associated total with its ringed counterpart.
Source: Stacks 0FPQ (blueprint: lem-sf-native-weil-ringed-triple-complex). -/
def nativeRingedTripleLeft (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (nativeTensorComplex T (nativeTensorComplex T P Q) N) ≅
      (coefficientTotalTensor b.J b.R).obj
        ((coefficientTotalTensor b.J b.R).obj
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P,
            (b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q),
          (b.native.functor.mapHomologicalComplex (.up ℤ)).obj N) :=
  A.chain N (nativeTensorComplex T P Q) ≪≫
    (coefficientTotalTensor b.J b.R).mapIso ((A.chain Q P).prod (Iso.refl _))

/-- Identify the right-associated total with its ringed counterpart.
Source: Stacks 0FPQ (blueprint: lem-sf-native-weil-ringed-triple-complex). -/
def nativeRingedTripleRight (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (nativeTensorComplex T P (nativeTensorComplex T Q N)) ≅
      (coefficientTotalTensor b.J b.R).obj
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P,
          (coefficientTotalTensor b.J b.R).obj
            ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
              (b.native.functor.mapHomologicalComplex (.up ℤ)).obj N)) :=
  A.chain (nativeTensorComplex T Q N) P ≪≫
    (coefficientTotalTensor b.J b.R).mapIso ((Iso.refl _).prod (A.chain N Q))

/-- Reassociate by the actual ringed cochain associator, then take its unique preimage.
Source: Stacks 0FPQ (blueprint: lem-sf-native-weil-ringed-triple-complex). -/
def nativeRingedAssociatorComplex (P Q N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    nativeTensorComplex T (nativeTensorComplex T P Q) N ≅
      nativeTensorComplex T P (nativeTensorComplex T Q N) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI : ∀ W X Y Z : GradedObject ℤ (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R),
      GradedObject.HasTensor₄ObjExt W X Y Z := fun _ _ _ _ ↦ inferInstance
  letI : ∀ Y Z : GradedObject ℤ (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R),
      Y.HasTensor Z := fun _ _ ↦ inferInstance
  letI : ∀ W Y Z : GradedObject ℤ (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R),
      GradedObject.HasGoodTensor₁₂Tensor W Y Z := fun _ _ _ ↦ inferInstance
  letI : ∀ W Y Z : GradedObject ℤ (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R),
      GradedObject.HasGoodTensorTensor₂₃ W Y Z := fun _ _ _ ↦ inferInstance
  (b.native.functor.mapHomologicalComplex (.up ℤ)).preimageIso
    (nativeRingedTripleLeft b T adj A P Q N ≪≫
      (α_
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj N)) ≪≫
      (nativeRingedTripleRight b T adj A P Q N).symm)

include b adj A in
/-- Native K-flat complexes are closed under their actual tensor total.
Source: Stacks 06YU (blueprint: lem-sf-native-weil-ringed-triple-complex).

Proof: the ringed comparison identifies the image of the tensor with the tensor
of the images. The latter is K-flat. Apply its acyclic-test property to an image
test, and reflect acyclicity through the additive equivalence. -/
theorem nativeTensorComplex_kflat
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    NativeTensorKFlat k₀ l X T (nativeTensorComplex T P Q) := by
  have : b.native.inverse.Additive := b.native.inverse_additive
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor b.J b.R
  have h := coefficientTotalTensor_isKFlat b.J b.R (Ec.obj P) (Ec.obj Q)
    (A.flat P hP) (A.flat Q hQ)
  intro N hN
  have ht := h (Ec.obj N) (hN.map b.native.functor)
  let i := A.chain (nativeTensorComplex T P Q) N ≪≫
    B.mapIso ((Iso.refl (Ec.obj N)).prod (A.chain Q P))
  have hm : (Ec.obj (CochainComplex.mapBifunctor (nativeTensorComplex T P Q) N T)).Acyclic :=
    fun n ↦ (ht n).of_iso i.symm
  have hi := hm.map b.native.inverse
  exact fun n ↦ (hi n).of_iso
    ((b.native.mapHomologicalComplex (.up ℤ)).unitIso.app _).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
