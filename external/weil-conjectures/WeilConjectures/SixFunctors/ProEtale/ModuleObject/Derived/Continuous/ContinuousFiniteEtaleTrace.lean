/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleTraceFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSheetSumCompatibility
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits

/-! # Existence and epimorphy of the normalized continuous finite etale trace

Source: blueprint, stratified lattice proof, "Pushing down by the trace".
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

private theorem module_isZero_empty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] {Y : Scheme.{u}} [IsEmpty Y]
    (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsZero P := by
  apply (IsZero.iff_id_eq_zero P).2
  ext : 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  have : IsEmpty T.unop.left := ⟨fun x ↦ isEmptyElim (α := Y) (T.unop.hom.base x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty P.X T.unop).hom_ext _ _

private theorem epi_sum_of_product
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Fintype J]
    {S A : C} (B : J → C) [HasProduct B] (e : ∀ j, A ≅ B j)
    (q : S ⟶ ∏ᶜ B) [IsIso q] (j₀ : J) :
    Epi (∑ j, q ≫ Pi.π B j ≫ (e j).inv) := by
  classical
  let i : A ⟶ ∏ᶜ B := Pi.lift (fun j ↦ if j = j₀ then (e j).hom else 0)
  let r := i ≫ inv q
  have hj (j : J) :
      r ≫ (q ≫ Pi.π B j ≫ (e j).inv) = if j = j₀ then 𝟙 A else 0 := by
    dsimp only [r]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc]
    change (Pi.lift (fun j ↦ if j = j₀ then (e j).hom else 0) ≫ Pi.π B j) ≫
      (e j).inv = _
    rw [Pi.lift_comp_π]
    split_ifs <;> simp only [Iso.hom_inv_id, zero_comp]
  have hr : r ≫ (∑ j, q ≫ Pi.π B j ≫ (e j).inv) = 𝟙 A := by
    rw [Preadditive.comp_sum]
    simp_rw [hj]
    simp
  let : IsSplitEpi (∑ j, q ≫ Pi.π B j ≫ (e j).inv) := ⟨⟨r, hr⟩⟩
  infer_instance

private theorem epi_mod_sum_of_sheets
    {C D B : Type*} [Category C] [Category D] [Category B]
    [MonoidalCategory B] [Preadditive B] [MonoidalPreadditive B]
    (R : B) [MonObj R] {J : Type*} [Fintype J] (F : C ⥤ D) (L : D ⥤ C) (H : C ⥤ Mod B R)
    (G : J → D ⥤ Mod B R) (a b : ∀ j, H ≅ F ⋙ G j) (hba : b = a) (P : C)
    (ε : F.obj (L.obj (F.obj P)) ⟶ F.obj P)
    [HasProduct (fun j ↦ (G j).obj (F.obj P))]
    (hq : let b := a
      IsIso (Pi.lift (fun j ↦
        (b j).hom.app (L.obj (F.obj P)) ≫ (G j).map ε))) (j₀ : J) :
    Epi (∑ j, (b j).hom.app (L.obj (F.obj P)) ≫ (G j).map ε ≫ (b j).inv.app P) := by
  subst b
  have : IsIso (Pi.lift (fun j ↦
      (a j).hom.app (L.obj (F.obj P)) ≫ (G j).map ε)) := hq
  have hepi := epi_sum_of_product (fun j ↦ (G j).obj (F.obj P))
    (fun j ↦ (a j).app P) (Pi.lift (fun j ↦
      (a j).hom.app (L.obj (F.obj P)) ≫ (G j).map ε)) j₀
  simpa only [Pi.lift_comp_π_assoc, Iso.app_inv, Category.assoc] using hepi

private theorem sheetSum_epi
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X) [Surjective p]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (c : FiniteEtaleModuleChart p) : Epi (finiteEtaleSheetSum Λ p P c) := by
  classical
  by_cases hn : Nonempty (Fin c.degree)
  · obtain ⟨j₀⟩ := hn
    have hepi := epi_mod_sum_of_sheets (condensedRingObj Λ c.base)
      (upperStar Λ p) (lowerStar Λ p) (upperStar Λ c.map)
      (fun j ↦ upperStar Λ (c.sheet j))
      (fun j ↦ (eqToIso (congrArg (upperStar Λ) (c.over j))).symm ≪≫
        upperStarComp Λ (c.sheet j) p)
      (fun j ↦ finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j))
      (by funext j; exact finiteEtaleTraceSheetComparison_eq Λ p c.map (c.sheet j) (c.over j)) P
      ((upperStarLowerStarAdjunction Λ p).counit.app ((upperStar Λ p).obj P))
      (splitProEtaleModuleProductMap_isIso Λ p c.map c.degree c.sheet c.over c.splits
        ((upperStar Λ p).obj P)) j₀
    simpa only [finiteEtaleSheetSum, finiteEtaleTraceSheetSum] using hepi
  · have : IsEmpty c.base := by
      constructor
      intro y
      have : Surjective (pullback.snd p c.map) := inferInstance
      obtain ⟨z, _⟩ := (pullback.snd p c.map).surjective y
      let e : pullback p c.map ⟶ (∅ : Scheme.{u}) :=
        c.splits.some.desc (Cofan.mk (∅ : Scheme.{u})
          (fun j : Fin c.degree ↦ False.elim (hn ⟨j⟩)))
      exact isEmptyElim (α := (∅ : Scheme.{u})) (e.base z)
    exact (module_isZero_empty Λ ((upperStar Λ c.map).obj P)).epi _

private theorem finiteEtaleTrace_of_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] [Surjective p]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ τ : (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P,
      Epi τ ∧ FiniteEtaleTraceFormula Λ p P τ := by
  obtain ⟨τ, hτ, hEpi⟩ := finiteEtaleSplitHom_descent Λ p
    ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) P
    (finiteEtaleSheetSum Λ p P) (finiteEtaleSheetSum_compatible Λ p P)
  exact ⟨τ, hEpi (fun c ↦ sheetSum_epi Λ p P c), hτ⟩

/-- A finite etale surjection has an epic normalized trace for every continuous
rational module, without any local-freeness or integral-lattice hypothesis.
Source: blueprint, stratified lattice proof, "Pushing down by the trace";
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-continuous-finite-etale-trace)

Proof. On every weakly etale finite splitting chart of p take the sum of the
canonical sheet projections, each the pullback of the actual counit at p^*P
conjugated by the composition comparisons. These local sums agree on overlaps
(finiteEtaleSheetSum_compatible), so they descend to a global map tau with the
exact sheet-sum formula FiniteEtaleTraceFormula (finiteEtaleSplitHom_descent).
Each local sum is epic: on a chart with at least one sheet, the canonical
product comparison of splitProEtaleModuleProductMap_isIso is an isomorphism, and
insertion into one chosen sheet followed by its inverse is a right inverse of
the sum. A chart with no sheets has empty fibre product; surjectivity of p makes
its base empty, and every internal module over the empty scheme is zero. The
epimorphy clause of the descent theorem then makes tau epic. No choice of an
integral lattice, trivialization of P, or division by the degree is used. -/
theorem continuousFiniteEtaleTrace_exists
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] [Surjective p]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ∃ τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P,
      Epi τ ∧ FiniteEtaleTraceFormula (Profinite.continuousMapRingObj E) p P τ := by
  -- Descend the canonical internal sheet sums; the product comparison proves epimorphy.
  exact finiteEtaleTrace_of_compatible (Profinite.continuousMapRingObj E) p P

end AlgebraicGeometry.ProEtale.CondensedRing
