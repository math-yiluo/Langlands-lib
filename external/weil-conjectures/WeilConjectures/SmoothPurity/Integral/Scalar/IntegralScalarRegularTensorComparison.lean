/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Comparing the regular coefficient tensor presentations

Source: Stacks, Tags 03EK and 010V; latest blueprint scalar-extension proof, step (4).
(blueprint: lem-sf-integral-scalar-regular-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The tensor unit identifies the two regular coefficient complex constructions.
Source: Stacks, Modules on Sites, Tag 03EK; blueprint scalar-extension proof, step (4).
(blueprint: lem-sf-integral-scalar-regular-tensor-comparison).
Proof: the constant sheaf of the regular B-module is the unit B_Y. The tensor
unitor sends (b tensor p) tensor c to bc tensor p and its inverse inserts 1 in the
last factor. These balanced linear maps commute with restrictions and descend
through module sheafification. The two composites are identity on pure tensors,
hence on their sheafifications. Naturality in P makes them commute with d_P.
They identify filteredCoefficientTensorComplex with integralScalarFiniteComplex:
use integralScalarReduction_eqConcrete to expose the latter's sheafified tensor
construction, and the unit isomorphism of the constant regular B-module to
remove the last tensor factor. This is a complex isomorphism before localization;
no flatness, constructibility, completeness, or boundedness is needed. The
construction also applies to zero P and the empty scheme. -/
theorem integralScalarRegularTensorIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    Nonempty (filteredCoefficientTensorComplex Y B
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (integralScalarRho l E L ι Y n) P (ModuleCat.of B B) ≅
        (integralScalarFiniteComplex l E L ι Y n).obj P) := by
  let J := ProEt.topology Y
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
  let S := adicLisseConstantRing Y B
  let U := (adicLisseConstantModules Y B).obj (ModuleCat.of B B)
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} S
  let := SheafOfModules.monoidalCategory S
  let eU : U ≅ 𝟙_ (pbcModules Y S) :=
    CategoryTheory.FlatConstantUnitProof.regularIso.{u + 1, u} J B
  let eT : filteredCoefficientTensorFunctor Y B (ModuleCat.of B B) ≅ 𝟭 _ :=
    SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} S U ≪≫
      (tensoringRight (pbcModules Y S)).mapIso eU ≪≫ rightUnitorNatIso _
  let C := (integralScalarFiniteComplex l E L ι Y n).obj P
  let eX (i : ℤ) : (filteredCoefficientTensorComplex Y B
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (integralScalarRho l E L ι Y n) P (ModuleCat.of B B)).X i ≅ C.X i :=
    eT.app _ ≪≫ (eqToIso (integralScalarReduction_obj l E L ι Y n (P.X i))).symm
  refine ⟨HomologicalComplex.Hom.isoOfComponents eX ?_⟩
  intro i j hij
  change (eX i).hom ≫ (integralScalarReduction l E L ι Y n).map (P.d i j) =
    (filteredCoefficientTensorFunctor Y B (ModuleCat.of B B)).map
      (SheafOfModules.changeOfRingsHom (integralScalarRho l E L ι Y n)
        (P.X i) (P.d i j)) ≫ (eX j).hom
  dsimp only [eX, Iso.trans_hom, Iso.symm_hom, eqToIso.inv]
  rw [integralScalarReduction_map]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simpa only [Functor.id_map, Category.assoc, Iso.app_hom] using
    congrArg (fun f ↦ f ≫ eqToHom
      (integralScalarReduction_obj l E L ι Y n (P.X j)).symm)
      (eT.hom.naturality (SheafOfModules.changeOfRingsHom
        (integralScalarRho l E L ι Y n) (P.X i) (P.d i j))).symm

/-- Transport the finite-model constructibility and vanishing predicates across
this tensor unitor and the localization homology comparison.
Source: Stacks, Tags 03EK, 010V, 09AJ and 099Y
(blueprint: lem-sf-integral-scalar-regular-tensor-comparison). -/
theorem integralScalarRegularTensorComparison
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    let C := filteredCoefficientTensorComplex Y B
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (integralScalarRho l E L ι Y n) P (ModuleCat.of B B)
    let H := (DerivedCategory.homologyFunctor
      (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l L (n + 1)))) i).obj
      (DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P))
    (IsConstructibleProEtaleCoefficientModuleSheaf Y B (C.homology i) ↔
      IsConstructibleProEtaleModuleSheaf Y
        (Padic.coefficientExtensionRing l L (n + 1)) H) ∧
    (IsZero (C.homology i) ↔ IsZero H) := by
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  let A := Padic.coefficientExtensionRing l L (n + 1)
  let B := ULift.{u + 1} A
  obtain ⟨e⟩ := integralScalarRegularTensorIso l E L ι Y P n
  let h := (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso e ≪≫
    ((DerivedCategory.homologyFunctorFactors _ i).app _).symm
  have hpred (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
      IsConstructibleProEtaleModuleSheaf Y A M ↔
        IsConstructibleProEtaleCoefficientModuleSheaf Y B M :=
    (proEtaleModuleRestriction_constructible_iff Y A M).trans
      (CoefficientSerre.coefficient_constructible_iff Y B M).symm
  refine ⟨?_, h.isZero_iff⟩
  constructor
  · intro hc
    exact constructibleProEtale_of_iso Y A h ((hpred _).mpr hc)
  · intro hc
    exact (hpred _).mp (constructibleProEtale_of_iso Y A h.symm hc)

end WeilConjectures
