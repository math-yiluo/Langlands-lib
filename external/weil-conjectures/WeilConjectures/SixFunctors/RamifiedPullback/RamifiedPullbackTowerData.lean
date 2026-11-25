/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
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

/-! # Ramified identification of finite pullback towers

Source: Stacks Project, Tags 093M, 03EK and 03EL; Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-weil-ramified-pullback-tower-identification).

Level n means positive exponent n+1. All scalar extensions below are the existing
sheafified balanced tensor, applied termwise, without a flatness hypothesis.

(blueprint: def-weil-ramified-pullback-tower-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

namespace WeilConjectures.RamifiedPullback

/-- The existing ring-sheaf forgetful operation at the actual site sizes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev ring {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R

/-- Module sheaves in the common coefficient universe; the site is unchanged.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev Mod {W : Scheme.{t}} (R : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) := SheafOfModules.{max u (t + 1)} (ring.{t, u} R)

set_option linter.defProp false in
/-- The existing canonical tensor witness, with standard derived localizations.
Only its ordinary functor is used here.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalarWitness {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  letI := HasDerivedCategory.standard (Mod.{t, u} R)
  letI := HasDerivedCategory.standard (Mod.{t, u} S)
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{_, max u (t + 1), t + 1, t} c

/-- Ordinary scalar extension, with exactly the existing tensor objects and maps.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def scalar {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    Mod.{t, u} R ⥤ Mod.{t, u} S := (scalarWitness.{t, u} c).choose

/-- Additivity from the existing tensor witness.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
instance scalar_additive {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    (scalar.{t, u} c).Additive :=
  (scalarWitness.{t, u} c).choose_spec.choose_spec.choose_spec.choose

/-- Termwise ordinary scalar extension on all cochain complexes.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev scalarCx {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :=
  (scalar.{t, u} c).mapHomologicalComplex (.up ℤ)

/-- The local tensor s⊗x, with the target scalar written first as in Mathlib.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def tensor {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalar.{t, u} c).obj M).val.obj U :=
  (eqToHom ((scalarWitness.{t, u} c).choose_spec.choose M).symm).val.app U
    ((toSheafify (Scheme.ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))

/-- Constant sheafification of a quotient coefficient homomorphism.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def constantMap (W : Scheme.{t}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} A)) ⟶
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} B)) :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom.comp
      (f.comp (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom)))

/-- The zero-based index of the e-subsequence.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def index (e n : ℕ) : ℕ := e * (n + 1) - 1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A finite coefficient sheaf as a module over its actual completed ring.
Source: Stacks 093M (blueprint: lem-weil-ramified-pullback-tower-identification). -/
abbrev coefficientModule (W : Scheme.{t}) (n : ℕ) :
    integralTowerModules l E W :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n))).obj
        (SheafOfModules.unit (ring (integralCoefficientCommRingSheaf l E W n)))

/-- Composite transition in the specified pullback tower, including equal indices.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def transition {X Y : Scheme.{t}} (g : X ⟶ Y) (a b : ℕ) (h : a ≤ b)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralOperationsPullbackLevel l E g b).obj P ⟶
      (integralOperationsPullbackLevel l E g a).obj P :=
  ((integralOperationsPullbackTowerFunctor l E g).obj P).map (homOfLE h).op

/-- The local section ((g⁻¹(p⊗a))⊗b), using the actual pullback adjunction unit.
Source: Stacks 03EL (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def pullTensor {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)) :
    (((integralOperationsPullbackLevel l E g n).obj P).X i).val.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  b • @id (((integralOperationsLevelPullback l E g n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
    (integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The ramified quotient map on the already recorded coefficient sheaves.
Source: Stacks 03EK (blueprint: lem-weil-ramified-pullback-tower-identification). -/
def ramifiedMap (W : Scheme.{t}) (e n : ℕ)
    (j : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) :
    integralCoefficientCommRingSheaf l E W n ⟶
      integralCoefficientCommRingSheaf l L W (index e n) := constantMap W j

/-- Normalized coefficient identification on one of the two small pro-etale sites.
The maps are fixed by inclusion, the actual completed projections, and pure tensors.
Source: Stacks 093M and 03EK
(blueprint: lem-weil-ramified-pullback-tower-identification). -/
structure Coefficients (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1)) (W : Scheme.{t}) where
  completedMap : completedIntegralCommRingSheafUnrestricted l E W ⟶
    completedIntegralCommRingSheafUnrestricted l L W
  projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W n =
      integralScalarRho l E L ι W n
  ramified_projection : ∀ n : ℕ,
    completedMap ≫ completedIntegralCommRingProjectionUnrestricted l L W (index e n) =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫ ramifiedMap l E L W e n (j n)
  coefficientIso : ∀ n : ℕ,
    (scalar.{t, u} completedMap).obj (coefficientModule l E W n) ≅
      coefficientModule l L W (index e n)
  coefficient_formula : ∀ (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso n).hom.val.app U
      (tensor completedMap (coefficientModule l E W n) U s a) =
        (ramifiedMap l E L W e n (j n)).hom.app U a *
          (completedIntegralCommRingProjectionUnrestricted l L W (index e n)).hom.app U s
  coefficient_transitions : ∀ (a b : ℕ) (h : a ≤ b) (h' : index e a ≤ index e b)
    (U : W.ProEtᵒᵖ)
    (x : (integralCoefficientCommRingSheaf l E W b).obj.obj U)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U),
    (coefficientIso a).hom.val.app U
      (tensor completedMap (coefficientModule l E W a) U s
        ((((integralCoefficientSheafSystem l E W).map (homOfLE h).op).hom.app U) x)) =
      (((integralCoefficientSheafSystem l L W).map (homOfLE h').op).hom.app U)
        ((coefficientIso b).hom.val.app U
          (tensor completedMap (coefficientModule l E W b) U s x))

end WeilConjectures.RamifiedPullback
