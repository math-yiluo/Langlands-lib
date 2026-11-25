/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ProjectiveCohomologySplitModel
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
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
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Cone of a prescribed top residue cell

Source: Stacks Project, proetale.tex, Tag 09C3, final induction paragraph;
derived.tex, definition-cone (blueprint: lem-sf-prescribed-residue-cell-cone-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v c h w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry CategoryTheory.MonoidalCategory

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.sheafToPresheaf_isRightAdjoint

namespace WeilConjectures

/-- Relative smallness in the coefficient universe, supplied by the standard size transport.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance sfResidueSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{max (u + 1) v} T.ProEt := essentiallySmallSelf _

/-- Relative smallness of the slice, in the same coefficient universe.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance sfResidueSliceSmall (T : Scheme.{u}) (U : T.ProEt) :
    EssentiallySmall.{max (u + 1) v} (Over U) := essentiallySmallSelf _

/-- Coefficient-sized additive sheafification, avoiding smaller-universe instance inference.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance (priority := 4000) sfResidueAbSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max (u + 1) v} :=
  SheafOfModules.hasSheafify_coefficientUniverse

/-- The coefficient-sized locally bijective criterion.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance (priority := 4000) sfResidueAbLocallyBijective (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Additive sheafification on the actual slice, at the coefficient universe.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance (priority := 4000) sfResidueSliceAbSheafify (T : Scheme.{u}) (U : T.ProEt) :
    HasSheafify ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{max (u + 1) v} :=
  SheafOfModules.hasSheafify_coefficientUniverse

/-- The locally bijective criterion on that slice.
Source: Stacks 00W1 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance (priority := 4000) sfResidueSliceAbLocallyBijective (T : Scheme.{u}) (U : T.ProEt) :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The constant field sheaf, with coefficient size containing the small pro-etale site.
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueCoefficients (T : Scheme.{u}) (k : Type v) [Field k] :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max (u + 1) v}).obj
    (CommRingCat.of (ULift.{max (u + 1) v} k))

/-- The recorded module category over the constant field sheaf.
Source: Stacks 03DA, 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueModules (T : Scheme.{u}) (k : Type v) [Field k] :=
  ringedSiteModules.{max (u + 1) v} (sfSplitRings (sfResidueCoefficients T k))

/-- Standard localization for these module sheaves; no additional existence hypothesis.
Source: Stacks 05RU (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance sfResidueDerived (T : Scheme.{u}) (k : Type v) [Field k] :
    HasDerivedCategory (sfResidueModules T k) := HasDerivedCategory.standard _

/-- Standard localization on the actual slice site.
Source: Stacks 05RU (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance sfResidueSliceDerived (T : Scheme.{u}) (k : Type v) [Field k] (U : T.ProEt) :
    HasDerivedCategory (SheafOfModules.{max (u + 1) v}
      ((sfSplitRings (sfResidueCoefficients T k)).over U)) := HasDerivedCategory.standard _

/-- Standard localization for any coefficient ring sheaf on the actual slice.
Source: Stacks 05RU (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
instance sfResidueAnySliceDerived (T : Scheme.{u}) (U : T.ProEt)
    (R : Sheaf ((Scheme.ProEt.topology T).over U) RingCat.{max (u + 1) v}) :
    HasDerivedCategory (SheafOfModules.{max (u + 1) v} R) :=
  HasDerivedCategory.standard _

/-- The finite free sheaf of the specified rank, using the recorded free construction.
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueFree (T : Scheme.{u}) (k : Type v) [Field k] (n : ℕ) :
    sfResidueModules T k :=
  @SheafOfModules.free T.ProEt inferInstance (Scheme.ProEt.topology T)
    (sfSplitRings (sfResidueCoefficients T k))
    (sfResidueAbSheafify.{u, v} T).isRightAdjoint
    (sfResidueAbLocallyBijective.{u, v} T)
    (ULift.{max (u + 1) v} (Fin n))

/-- A free cell in degree b, conventionally written k_T^n[-b].
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueCell (T : Scheme.{u}) (k : Type v) [Field k] (b : ℤ) (n : ℕ) :=
  (CochainComplex.singleFunctor (sfResidueModules T k) b).obj (sfResidueFree T k n)

/-- Termwise restriction using the existing module restriction and its zero compatibility.
Source: Stacks 03DH (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
def sfResidueComplexRestriction (T : Scheme.{u}) (k : Type v) [Field k] (U : T.ProEt) :=
  letI := module_overFunctor_preservesZero (sfSplitRings (sfResidueCoefficients T k)) U
  (SheafOfModules.overFunctor.{max (u + 1) v}
    (sfSplitRings (sfResidueCoefficients T k)) U).mapHomologicalComplex (.up ℤ)

/-- The finite zero-differential sum of copies of an arbitrary module sheaf.
This is the literal right side of the restricted tensor formula.
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
def sfResidueTensorModel {B : Type c} [Category.{h} B] [Abelian B]
    (F : B) (a b : ℤ) (rank : ℤ → ℕ) : CochainComplex B ℤ :=
  ∐ fun q : Set.Icc a b ↦
    (CochainComplex.singleFunctor B q.val).obj (∐ fun _ : Fin (rank q.val) ↦ F)

/-- The existing prescribed split model, specialized to the constant field.
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueSplit (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) := sfSplitComplex (sfResidueCoefficients T k) a b rank

/-- The actual top-summand inclusion of the existing split model.
Source: Stacks 09C3 (blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueInclusion (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (hab : a ≤ b) (rank : ℤ → ℕ) :=
  sfSplitCell (sfResidueCoefficients T k) a b rank b ⟨hab, le_rfl⟩

/-- The identity pair, represented by the literal identity mapping cone.
Source: Stacks derived.tex, definition-cone
(blueprint: lem-sf-prescribed-residue-cell-cone-model). -/
abbrev sfResidueIdentityPair (T : Scheme.{u}) (k : Type v) [Field k] (b : ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (𝟙 (sfResidueCell T k b n))

private def splitInclusionConeIso {B : Type c} [Category.{h} B] [Abelian B]
    {A V W : CochainComplex B ℤ} (i : A ⟶ V) (j : W ⟶ V) (p : V ⟶ A) (r : V ⟶ W)
    (hip : i ≫ p = 𝟙 A) (hjr : j ≫ r = 𝟙 W)
    (hir : i ≫ r = 0) (hjp : j ≫ p = 0) (hsum : r ≫ j + p ≫ i = 𝟙 V) :
    CochainComplex.mappingCone i ≅ W ⊞ CochainComplex.mappingCone (𝟙 A) := by
  let f : CochainComplex.mappingCone i ⟶ W :=
    CochainComplex.mappingCone.desc i 0 r (by simp [hir])
  let g : CochainComplex.mappingCone i ⟶ CochainComplex.mappingCone (𝟙 A) :=
    CochainComplex.mappingCone.map i (𝟙 A) (𝟙 A) p (by simp [hip])
  let f' : W ⟶ CochainComplex.mappingCone i := j ≫ CochainComplex.mappingCone.inr i
  let g' : CochainComplex.mappingCone (𝟙 A) ⟶ CochainComplex.mappingCone i :=
    CochainComplex.mappingCone.map (𝟙 A) i (𝟙 A) i (by simp)
  have hff : f' ≫ f = 𝟙 W := by simp [f', f, hjr]
  have hfg : f' ≫ g = 0 := by
    ext n
    dsimp [f', g, CochainComplex.mappingCone.map]
    simp [← HomologicalComplex.comp_f_assoc, hjp]
  have hgf : g' ≫ f = 0 := by
    ext n
    apply CochainComplex.mappingCone.ext_from (𝟙 A) (n + 1) n rfl
    · simp [g', f, CochainComplex.mappingCone.map]
    · simp only [HomologicalComplex.comp_f, g', f, CochainComplex.mappingCone.map,
        CochainComplex.HomComplex.Cochain.id_comp,
        CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.zero_f,
        HomologicalComplex.comp_f, Category.assoc, comp_zero,
        CochainComplex.mappingCone.inr_f_desc_f]
      exact congrArg (fun t : A ⟶ W ↦ t.f n) hir
  have hgg : g' ≫ g = 𝟙 _ := by
    dsimp [g, g']
    rw [← CochainComplex.mappingCone.map_comp]
    simpa [hip] using CochainComplex.mappingCone.map_id (𝟙 A)
  have hsum' : f ≫ f' + g ≫ g' = 𝟙 _ := by
    ext n
    apply CochainComplex.mappingCone.ext_from i (n + 1) n rfl
    · simp [f, f', g, g', CochainComplex.mappingCone.map, Preadditive.comp_add]
    · have hn := congrArg (fun t : V ⟶ V ↦ t.f n) hsum
      simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
        HomologicalComplex.id_f] at hn
      simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, f, f', g, g', CochainComplex.mappingCone.map,
        CochainComplex.HomComplex.Cochain.id_comp, Preadditive.comp_add, Category.assoc,
        CochainComplex.mappingCone.inr_f_desc_f_assoc,
        CochainComplex.mappingCone.inr_f_desc_f]
      simp only [← Category.assoc, ← Preadditive.add_comp, hn,
        Category.id_comp, Category.comp_id]
  refine ⟨biprod.lift f g, biprod.desc f' g', ?_, ?_⟩
  · simpa only [biprod.lift_desc] using hsum'
  · apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [Category.assoc, hff, hfg, hgf, hgg]

private def derivedConeCancellation {B : Type c} [Category.{h} B] [Abelian B]
    [HasDerivedCategory.{w} B] (A W K : CochainComplex B ℤ)
    (e : K ≅ W ⨿ CochainComplex.mappingCone (𝟙 A)) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj W := by
  have hz : IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone (𝟙 A))) := by
    rw [IsZero.iff_id_eq_zero]
    have hh := DerivedCategory.Q_map_eq_of_homotopy B
      (CochainComplex.mappingCone.homotopyToZeroOfId A)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hh
    exact hh
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := B)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact DerivedCategory.Q.mapIso (e ≪≫ (biprod.isoCoprod _ _).symm) ≪≫
    DerivedCategory.Q.mapBiprod _ _ ≪≫ (isoBiprodZero hz).symm

private def sfLowerInclusion (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) :
    sfResidueSplit T k a (b - 1) rank ⟶ sfResidueSplit T k a b rank where
  f q := if hq : a ≤ q ∧ q ≤ b - 1 then eqToHom (by
    dsimp [sfResidueSplit, sfSplitComplex]
    rw [ite_eq_left hq, ite_eq_left (show a ≤ q ∧ q ≤ b by omega)]) else 0
  comm' _ _ _ := by simp [sfResidueSplit, sfSplitComplex]

private def sfLowerProjection (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) :
    sfResidueSplit T k a b rank ⟶ sfResidueSplit T k a (b - 1) rank where
  f q := if hq : a ≤ q ∧ q ≤ b - 1 then eqToHom (by
    dsimp [sfResidueSplit, sfSplitComplex]
    rw [ite_eq_left hq, ite_eq_left (show a ≤ q ∧ q ≤ b by omega)]) else 0
  comm' _ _ _ := by simp [sfResidueSplit, sfSplitComplex]

private def sfTopProjection (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (hab : a ≤ b) (rank : ℤ → ℕ) :
    sfResidueSplit T k a b rank ⟶ sfResidueCell T k b (rank b) :=
  HomologicalComplex.mkHomToSingle
    (eqToHom (by dsimp [sfResidueSplit, sfSplitComplex]; rw [ite_eq_left ⟨hab, le_rfl⟩]))
    (fun _ _ ↦ by simp [sfResidueSplit, sfSplitComplex])

private theorem sfConeDecomposition (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (hab : a ≤ b) (rank : ℤ → ℕ) :
    Nonempty (CochainComplex.mappingCone (sfResidueInclusion T k a b hab rank) ≅
      sfResidueSplit T k a (b - 1) rank ⨿ sfResidueIdentityPair T k b (rank b)) := by
  let i := sfResidueInclusion T k a b hab rank
  let j := sfLowerInclusion T k a b rank
  let p := sfTopProjection T k a b hab rank
  let r := sfLowerProjection T k a b rank
  have hip : i ≫ p = 𝟙 _ := by
    apply HomologicalComplex.from_single_hom_ext
    simp [i, p, sfSplitCell, sfTopProjection,
      HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomToSingle_f]
  have hjr : j ≫ r = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro q
    dsimp [j, r, sfLowerInclusion, sfLowerProjection]
    split_ifs with hq
    · simp
    · have hz : IsZero ((sfResidueSplit T k a (b - 1) rank).X q) := by
        dsimp [sfResidueSplit, sfSplitComplex]
        rw [ite_eq_right hq]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  have hir : i ≫ r = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    simp [i, r, sfSplitCell, sfLowerProjection,
      HomologicalComplex.mkHomFromSingle_f]
  have hjp : j ≫ p = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    simp [j, p, sfTopProjection, sfLowerInclusion, HomologicalComplex.mkHomToSingle_f]
  have hsum : r ≫ j + p ≫ i = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro q
    by_cases hqb : q = b
    · subst q
      simp [r, j, p, i, sfLowerProjection, sfLowerInclusion, sfTopProjection,
        sfSplitCell, HomologicalComplex.mkHomFromSingle_f,
        HomologicalComplex.mkHomToSingle_f]
    · have hz : IsZero ((sfResidueCell T k b (rank b)).X q) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hqb
      have hpi : p.f q ≫ i.f q = 0 := by rw [hz.eq_of_tgt (p.f q) 0, zero_comp]
      simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, hpi, add_zero,
        HomologicalComplex.id_f]
      dsimp [r, j, sfLowerProjection, sfLowerInclusion]
      split_ifs with hq
      · simp
      · have hz' : IsZero ((sfResidueSplit T k a b rank).X q) := by
          dsimp [sfResidueSplit, sfSplitComplex]
          rw [ite_eq_right (show ¬ (a ≤ q ∧ q ≤ b) by omega)]
          exact isZero_zero _
        exact hz'.eq_of_src _ _
  exact ⟨splitInclusionConeIso i j p r hip hjr hir hjp hsum ≪≫ biprod.isoCoprod _ _⟩

private theorem sfIdentitySupport (T : Scheme.{u}) (k : Type v) [Field k]
    (b : ℤ) (n : ℕ) (q : ℤ) (hq₀ : q ≠ b - 1) (hq₁ : q ≠ b) :
    IsZero ((sfResidueIdentityPair T k b n).X q) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hq₁⟩

private theorem sfIdentityDifferential (T : Scheme.{u}) (k : Type v) [Field k]
    (b : ℤ) (n : ℕ) (p q : ℤ) (hpq : p ≠ b - 1 ∨ q ≠ b) :
    (sfResidueIdentityPair T k b n).d p q = 0 := by
  by_cases hrel : p + 1 = q
  · by_cases hp : p = b - 1
    · have hq : q = b := by omega
      simp_all
    · by_cases hp' : p = b
      · exact (sfIdentitySupport T k b n q (by omega) (by omega)).eq_of_tgt _ _
      · exact (sfIdentitySupport T k b n p hp hp').eq_of_src _ _
  · exact (sfResidueIdentityPair T k b n).shape p q hrel

private theorem sfIdentityTerms (T : Scheme.{u}) (k : Type v) [Field k]
    (b : ℤ) (n : ℕ) :
    ∃ (e₀ : (sfResidueIdentityPair T k b n).X (b - 1) ≅ sfResidueFree T k n)
      (e₁ : (sfResidueIdentityPair T k b n).X b ≅ sfResidueFree T k n),
      e₀.inv ≫ (sfResidueIdentityPair T k b n).d (b - 1) b ≫ e₁.hom = 𝟙 _ := by
  let A := sfResidueCell T k b n
  let f := 𝟙 A
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) b (sfResidueFree T k n)
  have hz₀ : IsZero (A.X (b - 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hz₁ : IsZero (A.X (b + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  let e₀ : (CochainComplex.mappingCone f).X (b - 1) ≅ sfResidueFree T k n :=
    { hom := (CochainComplex.mappingCone.fst f).1.v (b - 1) b (by omega) ≫ e.hom
      inv := e.inv ≫ (CochainComplex.mappingCone.inl f).v b (b - 1) (by omega)
      hom_inv_id := by
        apply CochainComplex.mappingCone.ext_to f (b - 1) b (by omega)
        · simp
        · exact hz₀.eq_of_tgt _ _
      inv_hom_id := by simp }
  let e₁ : (CochainComplex.mappingCone f).X b ≅ sfResidueFree T k n :=
    { hom := (CochainComplex.mappingCone.snd f).v b b (by omega) ≫ e.hom
      inv := e.inv ≫ (CochainComplex.mappingCone.inr f).f b
      hom_inv_id := by
        apply CochainComplex.mappingCone.ext_to f b (b + 1) rfl
        · exact hz₁.eq_of_tgt _ _
        · simp
      inv_hom_id := by simp }
  refine ⟨e₀, e₁, ?_⟩
  change (e.inv ≫ (CochainComplex.mappingCone.inl f).v b (b - 1) (by omega)) ≫
    (CochainComplex.mappingCone f).d (b - 1) b ≫
      ((CochainComplex.mappingCone.snd f).v b b (by omega) ≫ e.hom) = _
  simp only [Category.assoc]
  rw [CochainComplex.mappingCone.inl_v_d_assoc f b (b - 1) (b + 1) (by omega)
    (by omega)]
  simp [f, A, sfResidueCell]

private theorem sfIdentityContraction (T : Scheme.{u}) (k : Type v) [Field k]
    (b : ℤ) (n : ℕ) :
    ∃ h : Homotopy (𝟙 (sfResidueIdentityPair T k b n)) 0,
      (∀ p q : ℤ, p ≠ b → h.hom p q = 0) ∧
      (CochainComplex.mappingCone.inr (𝟙 (sfResidueCell T k b n))).f b ≫
        h.hom b (b - 1) ≫
          (CochainComplex.mappingCone.fst (𝟙 (sfResidueCell T k b n))).1.v
            (b - 1) b (by omega) = 𝟙 _ := by
  let A := sfResidueCell T k b n
  let f := 𝟙 A
  let h := CochainComplex.mappingCone.homotopyToZeroOfId A
  have hh (p q : ℤ) (hpq : p + (-1) = q) :
      h.hom p q = (CochainComplex.mappingCone.snd f).v p p (by omega) ≫
        (CochainComplex.mappingCone.inl f).v p q hpq := by
    dsimp [h, CochainComplex.mappingCone.homotopyToZeroOfId,
      CochainComplex.mappingCone.descHomotopy, CochainComplex.HomComplex.Cochain.equivHomotopy]
    rw [dite_eq_left hpq]
    simp only [CochainComplex.mappingCone.descCochain,
      CochainComplex.HomComplex.Cochain.comp_zero, zero_add]
    exact CochainComplex.HomComplex.Cochain.comp_v
      (CochainComplex.mappingCone.snd (𝟙 A)) (CochainComplex.mappingCone.inl (𝟙 A))
      (zero_add (-1)) p p q (add_zero p) hpq
  refine ⟨h, ?_, ?_⟩
  · intro p q hp
    by_cases hpq : p + (-1) = q
    · rw [hh p q hpq]
      have hz : IsZero (A.X p) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
      rw [hz.eq_of_tgt ((CochainComplex.mappingCone.snd f).v p p (by omega)) 0, zero_comp]
    · exact h.zero p q (by change q + 1 ≠ p; omega)
  · change (CochainComplex.mappingCone.inr f).f b ≫ h.hom b (b - 1) ≫
      (CochainComplex.mappingCone.fst f).1.v (b - 1) b (by omega) = _
    rw [hh b (b - 1) (by omega)]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_fst_v,
      Category.comp_id, CochainComplex.mappingCone.inr_f_snd_v]
    change 𝟙 (A.X b) = 𝟙 (A.X b)
    rfl

private def sfSplitHomologyIso (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) (q : ℤ) :
    (sfResidueSplit T k a b rank).homology q ≅ (sfResidueSplit T k a b rank).X q := by
  let V := sfResidueSplit T k a b rank
  have : IsIso (V.iCycles q) := V.isIso_iCycles q (q + 1) (by simp) rfl
  have : IsIso (V.homologyπ q) := V.isIso_homologyπ (q - 1) q (by simp) rfl
  exact (asIso (V.homologyπ q)).symm ≪≫ asIso (V.iCycles q)

private def sfSplitDerivedHomologyIso (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
      (DerivedCategory.Q.obj (sfResidueSplit T k a b rank)) ≅
        (sfResidueSplit T k a b rank).X q :=
  (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    sfSplitHomologyIso T k a b rank q

private theorem sfSplitIsZero (T : Scheme.{u}) (k : Type v) [Field k]
    (a b : ℤ) (rank : ℤ → ℕ) (hab : b < a) : IsZero (sfResidueSplit T k a b rank) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro q
  have hz : IsZero ((sfResidueSplit T k a b rank).X q) := by
    dsimp [sfResidueSplit, sfSplitComplex]
    rw [ite_eq_right (show ¬ (a ≤ q ∧ q ≤ b) by omega)]
    exact isZero_zero _
  exact hz.eq_of_src _ _

private def zeroDifferentialIntervalIso {B : Type c} [Category.{h} B] [Abelian B]
    (P : CochainComplex B ℤ) (a b : ℤ) (hd : ∀ p q, P.d p q = 0)
    (hs : ∀ q, ¬ (a ≤ q ∧ q ≤ b) → IsZero (P.X q)) :
    P ≅ ∐ fun q : Set.Icc a b ↦ (CochainComplex.singleFunctor B q.val).obj (P.X q.val) := by
  classical
  let j (q : Set.Icc a b) : (CochainComplex.singleFunctor B q.val).obj (P.X q.val) ⟶ P :=
    HomologicalComplex.mkHomFromSingle (𝟙 _) (fun r _ ↦ by simp [hd])
  let c := Cofan.mk P j
  have hc : IsColimit c := by
    apply HomologicalComplex.isColimitOfEval
    intro n
    refine ⟨?_, ?_, ?_⟩
    · intro s
      exact if hn : a ≤ n ∧ n ≤ b then
        (HomologicalComplex.singleObjXSelf (.up ℤ) n (P.X n)).inv ≫
          s.ι.app ⟨⟨n, hn⟩⟩ else 0
    · intro s q
      change (j q.as).f n ≫ _ = _
      by_cases hn : n = q.as.val
      · subst n
        dsimp only [j, CochainComplex.singleFunctor]
        rw [dite_eq_left (show a ≤ q.as.val ∧ q.as.val ≤ b from q.as.property),
          HomologicalComplex.mkHomFromSingle_f]
        simp
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_src _ _
    · intro s f hf
      by_cases hn : a ≤ n ∧ n ≤ b
      · rw [dite_eq_left hn]
        have hh := hf ⟨⟨n, hn⟩⟩
        change (j ⟨n, hn⟩).f n ≫ f = _ at hh
        dsimp only [j] at hh
        rw [HomologicalComplex.mkHomFromSingle_f, Category.comp_id] at hh
        rw [← hh]
        simp
      · exact (hs n hn).eq_of_src _ _
  exact hc.coconePointUniqueUpToIso (coproductIsCoproduct _)

private def sfRestrictedFreeIso (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (n : ℕ) :
    (SheafOfModules.overFunctor.{max (u + 1) v}
      (sfSplitRings (sfResidueCoefficients T k)) U).obj (sfResidueFree T k n) ≅
        ∐ fun _ : Fin n ↦ SheafOfModules.unit
          ((sfSplitRings (sfResidueCoefficients T k)).over U) := by
  let R := sfSplitRings (sfResidueCoefficients T k)
  let F := SheafOfModules.overFunctor.{max (u + 1) v} R U
  have : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  have : PreservesColimitsOfShape (Discrete (ULift.{max (u + 1) v} (Fin n))) F :=
    inferInstance
  let e : F.obj (SheafOfModules.unit R) ≅ SheafOfModules.unit (R.over U) := Iso.refl _
  exact PreservesCoproduct.iso F _ ≪≫ Sigma.mapIso (fun _ ↦ e) ≪≫
    Sigma.whiskerEquiv (g := fun _ : Fin n ↦ SheafOfModules.unit (R.over U))
      Equiv.ulift (fun _ ↦ Iso.refl _)

private def sfRestrictionModelIso (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (a b : ℤ) (rank : ℤ → ℕ)
    (C : DerivedCategory (sfResidueModules T k))
    (e : C ≅ DerivedCategory.Q.obj (sfResidueSplit T k a b rank)) :
    ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, max (u + 1) v,
      max (u + 1) v, max (u + 2) (v + 1), max (u + 2) (v + 1)}
      (sfSplitRings (sfResidueCoefficients T k)) U C ≅
        DerivedCategory.Q.obj ((sfResidueComplexRestriction T k U).obj
          (sfResidueSplit T k a b rank)) := by
  let R := sfSplitRings (sfResidueCoefficients T k)
  let F := SheafOfModules.overFunctor.{max (u + 1) v} R U
  have : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  have : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  exact SheafOfModules.overFunctor_derivedRestrictionIso.{u + 1, u, max (u + 1) v,
    max (u + 2) (v + 1), max (u + 2) (v + 1)} R U C ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app _

private theorem sfRestrictedSupport (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (a b : ℤ) (rank : ℤ → ℕ) (q : ℤ)
    (hq : ¬ (a ≤ q ∧ q ≤ b)) :
    IsZero (((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)).X q) := by
  let R := sfSplitRings (sfResidueCoefficients T k)
  let F := SheafOfModules.overFunctor.{max (u + 1) v} R U
  have hz : IsZero ((sfResidueSplit T k a b rank).X q) := by
    dsimp [sfResidueSplit, sfSplitComplex]
    rw [ite_eq_right hq]
    exact isZero_zero _
  exact F.map_isZero hz

private def sfRestrictedTermIso (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (a b : ℤ) (rank : ℤ → ℕ) (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
    (((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)).X q) ≅
      ∐ fun _ : Fin (rank q) ↦
        SheafOfModules.unit ((sfSplitRings (sfResidueCoefficients T k)).over U) := by
  let F := SheafOfModules.overFunctor.{max (u + 1) v}
    (sfSplitRings (sfResidueCoefficients T k)) U
  exact F.mapIso (eqToIso (by dsimp [sfResidueSplit, sfSplitComplex]; rw [ite_eq_left hq])) ≪≫
    sfRestrictedFreeIso T k U (rank q)

private theorem sfRestrictedKFlat (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (a b : ℤ) (rank : ℤ → ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := (sfResidueCoefficients T k).over U)
      ((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)) := by
  let R := (sfResidueCoefficients T k).over U
  let P : CochainComplex (SheafOfModules.KFlatFixedTensor.Modules R) ℤ :=
    (sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have : CochainComplex.IsStrictlyLE P b := (CochainComplex.isStrictlyLE_iff P b).2
    (fun q hq ↦ sfRestrictedSupport T k U a b rank q (by omega))
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P b
  intro q
  have hf : ObjectProperty.flat (P.X q) := by
    by_cases hq : a ≤ q ∧ q ≤ b
    · have hunit : ObjectProperty.flat (𝟙_ (SheafOfModules.KFlatFixedTensor.Modules R)) :=
        ObjectProperty.flat_of_tensorIso (λ_ _)
      let f := fun _ : Fin (rank q) ↦ 𝟙_ (SheafOfModules.KFlatFixedTensor.Modules R)
      have : HasBiproduct f := HasBiproduct.of_hasCoproduct f
      have hb := ObjectProperty.prop_of_isLimit ObjectProperty.flat
        (biproduct.isLimit f) (fun _ ↦ hunit)
      have hsum := ObjectProperty.prop_of_iso ObjectProperty.flat
        (biproduct.isoCoproduct f) hb
      exact ObjectProperty.prop_of_iso _ (sfRestrictedTermIso T k U a b rank q hq).symm hsum
    · exact ObjectProperty.flat.prop_of_isZero (sfRestrictedSupport T k U a b rank q hq)
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

private theorem sfRestrictedTensorFormula (T : Scheme.{u}) (k : Type v) [Field k]
    (U : T.ProEt) (a b : ℤ) (rank : ℤ → ℕ)
    (F : SheafOfModules.{max (u + 1) v}
      ((sfSplitRings (sfResidueCoefficients T k)).over U)) :
    Nonempty ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u,
      max (u + 1) v, max (u + 2) (v + 1)} _ ((sfResidueCoefficients T k).over U)).obj
        (DerivedCategory.Q.obj
          ((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)),
          (DerivedCategory.singleFunctor _ 0).obj F) ≅
            DerivedCategory.Q.obj (sfResidueTensorModel F a b rank)) ∧
    (∀ q : ℤ, ¬ (a ≤ q ∧ q ≤ b) → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u,
        max (u + 1) v, max (u + 2) (v + 1)} _ ((sfResidueCoefficients T k).over U)).obj
        (DerivedCategory.Q.obj
          ((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)),
          (DerivedCategory.singleFunctor _ 0).obj F)))) := by
  let R := (sfResidueCoefficients T k).over U
  let P : CochainComplex (SheafOfModules.KFlatFixedTensor.Modules R) ℤ :=
    (sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a b rank)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  change SheafOfModules.KFlatFixedTensor.Modules R at F
  let G := (SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj F
  have : G.Additive := by
    change (CategoryTheory.MonoidalCategory.tensorRight
      (C := SheafOfModules.KFlatFixedTensor.Modules R) F).Additive
    exact CategoryTheory.Functor.additive_of_iso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight F)
  let L := (G.mapHomologicalComplex (.up ℤ)).obj P
  have hd : ∀ p q, L.d p q = 0 := by
    intro p q
    change G.map ((SheafOfModules.overFunctor
      (sfSplitRings (sfResidueCoefficients T k)) U).map
        ((sfResidueSplit T k a b rank).d p q)) = 0
    simp [sfResidueSplit, sfSplitComplex]
  have hs (q : ℤ) (hq : ¬ (a ≤ q ∧ q ≤ b)) : IsZero (L.X q) :=
    G.map_isZero (sfRestrictedSupport T k U a b rank q hq)
  let eTerms (q : ℤ) (hq : a ≤ q ∧ q ≤ b) : L.X q ≅ ∐ fun _ : Fin (rank q) ↦ F :=
    G.mapIso (sfRestrictedTermIso T k U a b rank q hq) ≪≫
      PreservesCoproduct.iso G _ ≪≫ Sigma.mapIso (fun _ ↦ λ_ F)
  let eModel : L ≅ sfResidueTensorModel F a b rank :=
    zeroDifferentialIntervalIso L a b hd hs ≪≫ Sigma.mapIso
      (fun q : Set.Icc a b ↦ (CochainComplex.singleFunctor _ q.val).mapIso
        (eTerms q.val q.property))
  obtain ⟨cmp, _, _⟩ :=
    SheafOfModules.ringed_kFlat_single_tensor_comparison.{u + 1, u, max (u + 1) v,
      max (u + 2) (v + 1)} R
  let eTensor := cmp P (sfRestrictedKFlat T k U a b rank) F
  change _ ≅ DerivedCategory.Q.obj L at eTensor
  refine ⟨⟨eTensor ≪≫ DerivedCategory.Q.mapIso eModel⟩, ?_⟩
  intro q hq
  have hz := (HomologicalComplex.ExactAt.of_isZero (hs q hq)).isZero_homology
  exact hz.of_iso (((DerivedCategory.homologyFunctor _ q).mapIso eTensor) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app L)

/-- Prescribed top cells have the explicit cone, contraction and all restricted tensor models.
Source: Stacks 09C3, final induction paragraph, with derived.tex definition-cone
(blueprint: lem-sf-prescribed-residue-cell-cone-model).

Proof:
1. Apply lem-sf-projective-cohomology-split-model to a representative of N. Localize its
   prescribed quasi-isomorphism to obtain phi inducing every theta_q.
2. For ANY such phi, u and Q(i) followed by phi have identical top generator images.
   The injective generator bijection in that same lemma identifies them.
3. TR3 completes the square (identity, phi inverse) to a triangle morphism. The first
   two components are isomorphisms, hence so is the third by lem-sf-triangle-morphism-iso.
4. The cone matrix is (v,x) mapped to (i(x),0). Reorder V=W plus A to identify its cone
   with W plus the identity pair D. Its only nonzero differential is the identity in
   degrees b-1,b; the identity backwards is the contracting h. Projection onto W is
   a quasi-isomorphism, so Q inverts it.
5. Exact slice restriction and its comparison with derived restriction transport
   C ≅ Q(W) to every slice. Restriction preserves the finite coproduct defining each
   free term, and takes its unit to the slice unit.
6. Finite free terms are flat, and W is bounded above, hence K-flat by the independent-
   coefficient bounded-flat criterion. The K-flat/single tensor comparison reduces
   derived tensor to termwise tensor. Additivity and finite coproduct preservation
   give the displayed zero-differential sum of copies of F. Support gives the Tor
   interval; zero differentials compute the cohomology directly.
   When a=b the lower interval is empty, so W and C vanish. Empty schemes and zero ranks
   give zero free terms and the same matrices. -/
theorem sf_prescribed_residue_cell_cone_model
    (T : Scheme.{u}) (k : Type v) [Field k]
    (_hEval : ∀ (F G : Sheaf (Scheme.ProEt.topology T) (Type (max (u + 1) v)))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 T)))))
    (a b : ℤ) (hab : a ≤ b) (rank : ℤ → ℕ)
    (N : DerivedCategory (sfResidueModules T k))
    (_hN : ∀ q : ℤ, ¬ (a ≤ q ∧ q ≤ b) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj N))
    (theta : ∀ (q : ℤ) (_hq : a ≤ q ∧ q ≤ b), sfResidueFree T k (rank q) ≅
      (DerivedCategory.homologyFunctor _ q).obj N)
    (uTop : DerivedCategory.Q.obj (sfResidueCell T k b (rank b)) ⟶ N)
    (_huTop : sfFreeCohomologyMap (sfResidueCoefficients T k) b (rank b) uTop =
      (theta b ⟨hab, le_rfl⟩).hom)
    (C : DerivedCategory (sfResidueModules T k)) (g : N ⟶ C)
    (delta : C ⟶ (DerivedCategory.Q.obj (sfResidueCell T k b (rank b)))⟦(1 : ℤ)⟧)
    (_htriangle : Triangle.mk uTop g delta ∈ distTriang _) :
    (∃ phi : DerivedCategory.Q.obj (sfResidueSplit T k a b rank) ≅ N,
      ∀ (q : ℤ) (hq : a ≤ q ∧ q ≤ b),
        sfFreeCohomologyMap (sfResidueCoefficients T k) q (rank q)
          (DerivedCategory.Q.map
            (sfSplitCell (sfResidueCoefficients T k) a b rank q hq) ≫ phi.hom) =
          (theta q hq).hom) ∧
    (∀ phi : DerivedCategory.Q.obj (sfResidueSplit T k a b rank) ≅ N,
      (∀ (q : ℤ) (hq : a ≤ q ∧ q ≤ b),
        sfFreeCohomologyMap (sfResidueCoefficients T k) q (rank q)
          (DerivedCategory.Q.map
            (sfSplitCell (sfResidueCoefficients T k) a b rank q hq) ≫ phi.hom) =
          (theta q hq).hom) →
      uTop = DerivedCategory.Q.map (sfResidueInclusion T k a b hab rank) ≫ phi.hom ∧
      ∃ e : Triangle.mk uTop g delta ≅
          DerivedCategory.Q.mapTriangle.obj
            (CochainComplex.mappingCone.triangle (sfResidueInclusion T k a b hab rank)),
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = phi.inv) ∧
    Nonempty (CochainComplex.mappingCone (sfResidueInclusion T k a b hab rank) ≅
      sfResidueSplit T k a (b - 1) rank ⨿ sfResidueIdentityPair T k b (rank b)) ∧
    (∃ (e₀ : (sfResidueIdentityPair T k b (rank b)).X (b - 1) ≅
        sfResidueFree T k (rank b))
      (e₁ : (sfResidueIdentityPair T k b (rank b)).X b ≅ sfResidueFree T k (rank b)),
      e₀.inv ≫ (sfResidueIdentityPair T k b (rank b)).d (b - 1) b ≫ e₁.hom = 𝟙 _) ∧
    (∀ q : ℤ, q ≠ b - 1 → q ≠ b →
      IsZero ((sfResidueIdentityPair T k b (rank b)).X q)) ∧
    (∀ p q : ℤ, p ≠ b - 1 ∨ q ≠ b →
      (sfResidueIdentityPair T k b (rank b)).d p q = 0) ∧
    (∃ h : Homotopy (𝟙 (sfResidueIdentityPair T k b (rank b))) 0,
      (∀ p q : ℤ, p ≠ b → h.hom p q = 0) ∧
      (CochainComplex.mappingCone.inr (𝟙 (sfResidueCell T k b (rank b)))).f b ≫
        h.hom b (b - 1) ≫
          (CochainComplex.mappingCone.fst (𝟙 (sfResidueCell T k b (rank b)))).1.v
            (b - 1) b (by omega) = 𝟙 _) ∧
    Nonempty (C ≅ DerivedCategory.Q.obj
      (CochainComplex.mappingCone (sfResidueInclusion T k a b hab rank))) ∧
    Nonempty (DerivedCategory.Q.obj
      (CochainComplex.mappingCone (sfResidueInclusion T k a b hab rank)) ≅
        DerivedCategory.Q.obj (sfResidueSplit T k a (b - 1) rank)) ∧
    (∀ U : T.ProEt,
      CochainComplex.IsKFlatIndependentCoefficients (R := (sfResidueCoefficients T k).over U)
        ((sfResidueComplexRestriction T k U).obj (sfResidueSplit T k a (b - 1) rank)) ∧
      (∀ F : SheafOfModules.{max (u + 1) v}
          ((sfSplitRings (sfResidueCoefficients T k)).over U),
        Nonempty ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u,
          max (u + 1) v, max (u + 2) (v + 1)} _
          ((sfResidueCoefficients T k).over U)).obj
            (ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, max (u + 1) v,
              max (u + 1) v, max (u + 2) (v + 1), max (u + 2) (v + 1)}
              (sfSplitRings (sfResidueCoefficients T k)) U C,
              (DerivedCategory.singleFunctor _ 0).obj F) ≅
                DerivedCategory.Q.obj (sfResidueTensorModel F a (b - 1) rank))) ∧
      (a < b → HasRingedSiteTorAmplitudeOfUniverses ((sfResidueCoefficients T k).over U)
        (ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, max (u + 1) v,
              max (u + 1) v, max (u + 2) (v + 1), max (u + 2) (v + 1)}
          (sfSplitRings (sfResidueCoefficients T k)) U C) a (b - 1))) ∧
    (∀ (q : ℤ) (_hq : a ≤ q ∧ q < b),
      Nonempty (sfResidueFree T k (rank q) ≅ (DerivedCategory.homologyFunctor _ q).obj C)) ∧
    (∀ q : ℤ, ¬ (a ≤ q ∧ q < b) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C)) ∧
    (a = b → IsZero (sfResidueSplit T k a (b - 1) rank) ∧ IsZero C) := by
  classical
  let R := sfResidueCoefficients T k
  let Z := DerivedCategory.Q.objPreimage N
  let e := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨v, hv, htheta, _⟩ := sf_projective_cohomology_split_model R _hEval N
    a b hab rank _hN theta Z e
  have := hv
  let phi : DerivedCategory.Q.obj (sfResidueSplit T k a b rank) ≅ N :=
    asIso (DerivedCategory.Q.map v) ≪≫ e
  have hphi (q : ℤ) (hq : a ≤ q ∧ q ≤ b) :
      sfFreeCohomologyMap R q (rank q)
        (DerivedCategory.Q.map (sfSplitCell R a b rank q hq) ≫ phi.hom) =
          (theta q hq).hom := by
    simpa only [phi, Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc]
      using htheta q hq
  have htop (psi : DerivedCategory.Q.obj (sfResidueSplit T k a b rank) ≅ N)
      (hpsi : ∀ (q : ℤ) (hq : a ≤ q ∧ q ≤ b),
        sfFreeCohomologyMap R q (rank q)
          (DerivedCategory.Q.map (sfSplitCell R a b rank q hq) ≫ psi.hom) =
            (theta q hq).hom) :
      uTop = DerivedCategory.Q.map (sfResidueInclusion T k a b hab rank) ≫ psi.hom := by
    apply (sf_shifted_free_generator_bijective_natural R _hEval).1 b (rank b) N |>.injective
    funext i
    exact congrArg (fun f ↦
      (((DerivedCategory.homologyFunctor _ b).obj N).freeHomEquiv f (ULift.up i)).val
        (op (Scheme.ProEt.mk (𝟙 T))))
      (_huTop.trans (hpsi b ⟨hab, le_rfl⟩).symm)
  have htri (psi : DerivedCategory.Q.obj (sfResidueSplit T k a b rank) ≅ N)
      (hp : uTop = DerivedCategory.Q.map (sfResidueInclusion T k a b hab rank) ≫ psi.hom) :
      ∃ e : Triangle.mk uTop g delta ≅
          DerivedCategory.Q.mapTriangle.obj
            (CochainComplex.mappingCone.triangle (sfResidueInclusion T k a b hab rank)),
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = psi.inv := by
    refine ⟨isoTriangleOfIso₁₂ _ _ _htriangle
      (DerivedCategory.mappingCone_triangle_distinguished _) (Iso.refl _) psi.symm ?_,
      by rfl, by rfl⟩
    change uTop ≫ psi.inv = 𝟙 _ ≫ _
    rw [hp]
    rw [Category.assoc, psi.hom_inv_id, Category.comp_id, Category.id_comp]
    rfl
  obtain ⟨eCone⟩ := sfConeDecomposition T k a b hab rank
  let eC := Triangle.π₃.mapIso (htri phi (htop phi hphi)).choose
  let eW := derivedConeCancellation (sfResidueCell T k b (rank b))
    (sfResidueSplit T k a (b - 1) rank) _ eCone
  refine ⟨⟨phi, hphi⟩, fun psi hpsi ↦ ⟨htop psi hpsi, htri psi (htop psi hpsi)⟩,
    ⟨eCone⟩, sfIdentityTerms T k b (rank b), sfIdentitySupport T k b (rank b),
    sfIdentityDifferential T k b (rank b), sfIdentityContraction T k b (rank b),
    ⟨eC⟩, ⟨eW⟩, ?_, ?_, ?_, ?_⟩
  · intro U
    let eRest := sfRestrictionModelIso T k U a (b - 1) rank C (eC ≪≫ eW)
    let D := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u,
      max (u + 1) v, max (u + 2) (v + 1)} _ ((sfResidueCoefficients T k).over U)
    have eTest (F : SheafOfModules.{max (u + 1) v}
        ((sfSplitRings (sfResidueCoefficients T k)).over U)) :=
      D.mapIso (eRest.prod (Iso.refl ((DerivedCategory.singleFunctor _ 0).obj F)))
    refine ⟨sfRestrictedKFlat T k U a (b - 1) rank, ?_, ?_⟩
    · intro F
      obtain ⟨et⟩ := (sfRestrictedTensorFormula T k U a (b - 1) rank F).1
      exact ⟨eTest F ≪≫ et⟩
    · intro hab'
      refine ⟨by omega, ?_⟩
      intro F q hq
      have hz := (sfRestrictedTensorFormula T k U a (b - 1) rank F).2 q (by omega)
      exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso (eTest F))
  · intro q hq
    let eX : (sfResidueSplit T k a (b - 1) rank).X q ≅ sfResidueFree T k (rank q) :=
      eqToIso (by dsimp [sfResidueSplit, sfSplitComplex]; rw [ite_eq_left (by omega)])
    exact ⟨eX.symm ≪≫ (sfSplitDerivedHomologyIso T k a (b - 1) rank q).symm ≪≫
      ((DerivedCategory.homologyFunctor _ q).mapIso (eC ≪≫ eW)).symm⟩
  · intro q hq
    have hz : IsZero ((sfResidueSplit T k a (b - 1) rank).X q) := by
      dsimp [sfResidueSplit, sfSplitComplex]
      rw [ite_eq_right (show ¬ (a ≤ q ∧ q ≤ b - 1) by omega)]
      exact isZero_zero _
    exact hz.of_iso (((DerivedCategory.homologyFunctor _ q).mapIso (eC ≪≫ eW)) ≪≫
      sfSplitDerivedHomologyIso T k a (b - 1) rank q)
  · intro hab'
    have hz := sfSplitIsZero T k a (b - 1) rank (by omega)
    exact ⟨hz, (DerivedCategory.Q.map_isZero hz).of_iso (eC ≪≫ eW)⟩

end WeilConjectures
