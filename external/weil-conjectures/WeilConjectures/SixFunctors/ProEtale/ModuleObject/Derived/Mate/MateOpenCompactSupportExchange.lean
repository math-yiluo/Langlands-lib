/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenProperRestrictionIso
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-! # The normalized compact-support comparison for an open square

Source: blueprint proposition-composition-open-restriction-compactifications-f, proof (2), and
 proposition-composition-base-change-rf-shriek--1, proof (2)--(3).
-/

@[expose] public noncomputable section
set_option linter.privateModule false

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : TwoSquare H L L' H') (M : B) :
    (mateEquiv a b θ).app M =
      b.homEquiv _ _ (θ.app (R.obj M) ≫ H'.map (a.counit.app M)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit]

private theorem supported_open_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {V Y : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hz : IsZero ((upperStar Λ v.closedComplement).mapDerivedCategory.obj B)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).counit.app B) := by
  let c := v.closedComplement
  have hc : IsCompl (Set.range c.base) (Set.range v.base) := by
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v
  have hopen : IsIso ((upperStar Λ v).mapDerivedCategory.map (adj.counit.app B)) :=
    isIso_of_hom_comp_eq_id _ (adj.right_triangle_components B)
  apply (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    Λ c v hc).isIso_of_pairFunctor (adj.counit.app B)
  · exact (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ v) _).2 hopen
  · have hs := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ v c hc.symm.disjoint ((upperStar Λ v).mapDerivedCategory.obj B)
    have ht := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ c).app B)
    exact hs.isIso ht _

end AlgebraicGeometry.ProEtale.CondensedRing
