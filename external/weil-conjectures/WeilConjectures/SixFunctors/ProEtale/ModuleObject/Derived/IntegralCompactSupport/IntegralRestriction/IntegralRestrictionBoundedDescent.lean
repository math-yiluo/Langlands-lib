/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Finite-open descent for integral restriction

Source: blueprint main-20261015, sk-thm-int-restriction-glue.proof.md,
expanded by theorem-f-shriek-ell-adic-coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

private theorem zero_of_open_restrictions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (I : Type w) (U : I → X.Opens) (hcover : iSup U = ⊤)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i : I, IsZero ((CondensedRing.upperStar Λ (U i).ι).obj M)) :
    IsZero M := by
  have hsheaf : IsZero M.X := by
    have hiso : IsIso (0 : M.X ⟶ 0) := by
      have hc : Presieve.ofArrows (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) ∈
          Scheme.proetalePrecoverage X := by
        apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
        apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
        refine ⟨?_, fun i ↦ inferInstanceAs (IsOpenImmersion (U i).ι)⟩
        intro x
        have hx : x ∈ iSup U := by rw [hcover]; trivial
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨i, by simpa using hi⟩
      apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} _
        (fun i ↦ (U i).ι) hc
      intro i
      have hz : IsZero ((ProEtale.upperStar Ab.{u + 1} (U i).ι).obj M.X) := by
        let e := (Mod.extendScalarsIsoComapInv
          (condensedPullbackHom Λ (U i).ι)).app
            (((ProEtale.upperStar Ab.{u + 1} (U i).ι).mapMod _).obj M)
        exact ((Mod.forget _).map_isZero (hM i)).of_iso
          ((Mod.forget _).mapIso e).symm
      let e := ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (U i).ι
        inferInstance
      exact isIso_of_source_target_iso_zero _ (hz.of_iso (e.app M.X).symm).isoZero
        ((((ProEtale.upperStar Ab.{u + 1} (U i).ι).map_isZero (isZero_zero _))).of_iso
          (e.app 0).symm).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : M.X ⟶ 0))
  rw [IsZero.iff_id_eq_zero]
  apply (Mod.forget _).map_injective
  simpa using hsheaf.eq_of_src (𝟙 M.X) 0

/-- Boundedness descends along a finite open cover.
Source: theorem-f-shriek-ell-adic-coefficients, proof steps 1--2; blueprint
sk-thm-int-restriction-glue.proof.md, paragraph (1).
(blueprint: lem-int-restriction-bounded-descent).

Proof: Open inverse image is exact, so its derived functor is termwise restriction
and commutes with every cohomology functor. For each member choose lower and upper
cohomological bounds. If the finite index type is inhabited, take the minimum of
its lower bounds and the maximum of its upper bounds. Outside this interval each
cohomology module restricts to zero on every open. For a pro-etale object W over X,
the base changes W times_X U_i cover W. Every section of the cohomology module
restricts to zero on this covering and is therefore zero by the sheaf condition.
Thus the global cohomology module is zero in those degrees. The standard derived
t-structure characterizes boundedness by precisely these vanishings. If the index
type is empty, the covering equality forces X empty, and the empty pro-etale
covering makes every module sheaf zero; all cohomology vanishes, so choose bounds
zero and zero. -/
theorem bounded_finiteOpenDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (I : Type w) [Finite I] (U : I → X.Opens)
    (hcover : iSup U = ⊤) (M : Ambient Λ X)
    (hM : ∀ i : I, DerivedCategory.TStructure.t.bounded ((pull Λ (U i).ι).obj M)) :
    DerivedCategory.TStructure.t.bounded M := by
  classical
  choose a ha using fun i ↦ (hM i).1
  choose b hb using fun i ↦ (hM i).2
  obtain ⟨r, hr⟩ := (Set.finite_range a).bddBelow
  obtain ⟨s, hs⟩ := (Set.finite_range b).bddAbove
  have hz (q : ℤ) (hq : q < r ∨ s < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj M) := by
    apply zero_of_open_restrictions Λ X I U hcover
    intro i
    have hi : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pull Λ (U i).ι).obj M)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ (a i)).mp (ha i) q
          (hq.trans_le (hr (Set.mem_range_self i)))
      · exact (DerivedCategory.isLE_iff _ (b i)).mp (hb i) q
          ((hs (Set.mem_range_self i)).trans_lt hq)
    let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ (U i).ι).app M
    let eh := ((CondensedRing.upperStar Λ (U i).ι).mapDerivedCategoryHomologyFunctorIso q).app M
    exact hi.of_iso (((DerivedCategory.homologyFunctor _ q).mapIso e).trans eh.symm).symm
  exact ⟨⟨r, (DerivedCategory.isGE_iff M r).mpr (fun q hq ↦ hz q (Or.inl hq))⟩,
    ⟨s, (DerivedCategory.isLE_iff M s).mpr (fun q hq ↦ hz q (Or.inr hq))⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
