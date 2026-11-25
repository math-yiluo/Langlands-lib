/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Point.PointFiniteFreeSectionsTensor
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Mathlib.Algebra.Homology.Localization

/-! # Derived descent of the point sections-tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YY (lemma-derived-base-change),
derived.tex, Tags 015F and 06XN, and categories.tex, Tag 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent).

The ordinary and derived extensions and their counit are the published constructions.
The assertion retains the representative normalization, every K-flat resolution, and
naturality on roofs. All complexes and derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u wE wL
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

section ScalarComparison
variable {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
private theorem exact_derived_comparison
    {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
    {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (ε : DerivedCategory.Qh (C := C₁) ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := C₂))
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C₁ (.up ℤ))] :
    ∃ c : F.mapDerivedCategory ≅ LF, ∀ X : CochainComplex C₁ ℤ,
      c.inv.app ((DerivedCategory.Q (C := C₁)).obj X) ≫ F.mapDerivedCategoryFactors.hom.app X =
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) := by
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C₁ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  let c := Functor.leftDerivedUnique LF F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom ε (HomotopyCategory.quasiIso C₁ (.up ℤ))
  refine ⟨c, ?_⟩
  intro X
  have hh := Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C₁ (.up ℤ))
    (𝟙 _) ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  have hφ : F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj X) =
        F.mapDerivedCategoryFactors.hom.app X := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ (DerivedCategory.Qh (C := C₂)).map (𝟙 _) = _
    erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := C₂)).map_id]
    simp only [Category.id_comp, Category.comp_id]
  change c.inv.app ((DerivedCategory.Q (C := C₁)).obj X) ≫
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X) ≫ 𝟙 _ at hh
  simpa only [hφ, Category.comp_id] using hh

private theorem scalar_exact_comparison (Y : Scheme.{t})
    [PreservesFiniteLimits (completedOrdinaryScalarExtension l E L ι Y)]
    [PreservesFiniteColimits (completedOrdinaryScalarExtension l E L ι Y)] :
    ∃ c : (completedOrdinaryScalarExtension l E L ι Y).mapDerivedCategory ≅
      completedDerivedScalarExtension l E L ι Y,
      ∀ X : CochainComplex (integralTowerModules l E Y) ℤ,
        c.inv.app (DerivedCategory.Q.obj X) ≫
            (completedOrdinaryScalarExtension l E L ι Y).mapDerivedCategoryFactors.hom.app X =
          completedScalarCounit l E L ι Y X := by
  let T := (completedScalarChangeData l E L ι Y).choose
  have : T.Additive :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose
  have : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (completedOrdinaryScalarExtension l E L ι Y))
  have : PreservesFiniteColimits T :=
    inferInstanceAs (PreservesFiniteColimits (completedOrdinaryScalarExtension l E L ι Y))
  let LF := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
  let ε := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
  have hLF := (completedScalarChangeData l E L ι Y)
    |>.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
  have hk := exact_derived_comparison T LF ε
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hk
        | throwError "missing universal comparison proof"
      (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar hd.fvarId)
    Lean.Elab.Tactic.replaceMainGoal []

end ScalarComparison

namespace PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L} (d : PointFiniteFreeSectionsTensorData k l E L ι)

/-- Sections with their constant-value integral action, at the source coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsE := pointFiniteFreeEvaluation k l E d.coefficientE

/-- Sections with their constant-value integral action, at the target coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsL := pointFiniteFreeEvaluation k l L d.coefficientL

/-- The source ordinary composite A(C) = Gamma(C) tensor O_L, before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev A := sectionsE d ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι

/-- The target ordinary composite B(C) = Gamma(C tensor R_L), before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev B := completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙ sectionsL d

end PointDerivedSectionsTensor

open PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}
  [HasDerivedCategory.{wE} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l E))]
  [HasDerivedCategory.{wL} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l L))]

set_option genInjectivity false in
set_option genSizeOfSpec false in
attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted
end WeilConjectures
