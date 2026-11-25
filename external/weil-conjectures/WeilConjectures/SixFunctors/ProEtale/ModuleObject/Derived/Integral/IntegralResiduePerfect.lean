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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact

/-! # Dualizability of the residue coefficient as an integral complex

Source: Bhatt--Scholze, Lemma 6.5.9(3), and the two-term free resolution of
O_E/ℓ (blueprint: lem-weil-pbc-integral-residue-perfect).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResiduePerfect
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The residue coefficient module, restricted to integral coefficients and placed
in degree zero, is dualizable.
Source: Bhatt--Scholze, Lemma 6.5.9(3), applied to the two-term free resolution
(blueprint: lem-weil-pbc-integral-residue-perfect).

Proof in words. Pull the proved short exact integral module reduction sequence from
the profinite point to T. Inverse image is exact and strong monoidal, so its two
integral regular modules identify with the tensor unit on T. The first two terms are
therefore dualizable. A short exact sequence with dualizable first and second terms
has dualizable third term in the derived category: the third term is represented by
the mapping cone of the map between these two terms. Finally transport along the
canonical comparison between inverse image of restricted scalars and restriction of
inverse image. This identifies the third term with the displayed residue coefficient.
The argument also applies to the empty scheme. -/
theorem integralResidue_isDualizable (T : Scheme.{u}) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
      ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
        (Mod.regular (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) := by
  let F := upperStarFromPoint T
  have : F.IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).isLeftAdjoint
  have : PreservesFiniteLimits F := by
    dsimp [F, upperStarFromPoint, pointUpperStar]
    infer_instance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let R := integralCoeff.{u} ℓ E
  let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
  let eR : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
        Category.id_comp])
  let eA : (F.mapMod A).obj (Mod.regular A) ≅ Mod.regular (F.obj A) :=
    Mod.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
        Category.id_comp])
  have : (F.mapMod R).Additive :=
    ⟨Mod.hom_ext _ _ F.map_add⟩
  have hs := (integralModuleReductionSequence_shortExact.{u} ℓ E).map_of_exact (F.mapMod R)
  have hR : IsDualizable ((F.mapMod R).obj (Mod.regular R)) :=
    isDualizable_unit.of_iso eR.symm
  have hA := DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hs hR hR
  let e := (F.mapModComapIso (integralReductionMap ℓ E)).app (Mod.regular A) ≪≫
    (Mod.comap (F.map (integralReductionMap ℓ E))).mapIso eA
  exact hA.of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e)

end AlgebraicGeometry.ProEtale.CondensedRing
