/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicSectionSliceFreeness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # Local finite freeness in the section presentation
Source: Stacks Project, Tags 00YV, 03DM and 03DO.
(blueprint: lem-sf-adic-section-local-freeness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.AdicFiniteRealization

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The section equivalence detects finite free trivializations on scheme covers.
Source: Stacks Project, Tags 00YV, 03DM and 03DO
(blueprint: lem-sf-adic-section-local-freeness).
Proof: localize at a weakly etale chart W. The pro-etale site of its source is
equivalent to the slice site over W, and restriction of the section equivalence
commutes with this localization. The regular internal module encodes as the unit
module; finite coproduct preservation identifies its rank n free module with
SheafOfModules.free on ULift (Fin n). Full faithfulness gives the converse.
A scheme precover gives a family covering the terminal object. Conversely restrict
a local generators covering sieve to the terminal object and refine it by a
pro-etale precover. Pull the free presentations to that refinement and shrink the
index universe using smallness of the precoverage. This gives a scheme cover of
the required size. Empty covers and rank zero are allowed throughout. -/
theorem sectionModule_locallyFree_iff (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) A) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ j : C.I₀,
      Mod.IsFree ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).obj A)
        (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).mapMod A).obj P)) ↔
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) A).functor.obj P).IsFiniteLocallyFree := by
  classical
  let R := (adicLisseForget X).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u+1,u+1,u} (ProEt.topology X) A)
  let M := (InternalAbelianSheafModule.sectionModuleEquivalence.{u+1,u+1,u}
    (ProEt.topology X) A).functor.obj P
  constructor
  · rintro ⟨C, hC⟩
    let (s : C.I₀) : WeaklyEtale (C.f s) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
    let U (s : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f s)
    have hU : (Scheme.ProEt.topology X).CoversTop U := by
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _
        (Scheme.ProEt.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X)]
      let a (s : C.I₀) : U s ⟶ Scheme.ProEt.mk (𝟙 X) :=
        MorphismProperty.Over.homMk (C.f s) (by
          change C.f s ≫ 𝟙 X = C.f s
          exact Category.comp_id _)
      apply Scheme.ProEt.mem_topology_iff.mpr
      refine ⟨Presieve.ofArrows U a, ?_, ?_⟩
      · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
        exact C.mem₀
      · intro W f hf
        obtain ⟨s⟩ := hf
        exact ⟨s, ⟨𝟙 _⟩⟩
    have hfree (s : C.I₀) : ∃ n : ℕ, Nonempty (M.over (U s) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) :=
      (section_slice_free X A P (U s)).mpr (hC s)
    choose n hn using hfree
    have hU' : (Scheme.ProEt.topology X).CoversTop
        (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) := by
      intro V
      apply (Scheme.ProEt.topology X).superset_covering _ (hU V)
      rintro W f ⟨s, ⟨a⟩⟩
      exact ⟨ULift.up s, ⟨a⟩⟩
    exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free (M := M)
      (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) hU'
      (fun s ↦ ULift.{u + 1} (Fin (n s.down))) (fun s ↦ hn s.down)
  · intro hM
    let : M.IsFiniteLocallyFree := hM
    obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
    let : q.IsLocallyFreeData := hq
    have hfree (i : q.I) : ∃ n : ℕ, Nonempty (M.over (q.X i) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let : (q.generators i).IsFiniteType := hf.isFiniteType i
      obtain ⟨n, ⟨en⟩⟩ := Finite.exists_equiv_fin (q.generators i).I
      exact ⟨n, ⟨(asIso (q.generators i).π).symm ≪≫
        SheafOfModules.freeFunctor.mapIso (en.trans Equiv.ulift.symm).toIso⟩⟩
    let V : X.ProEt := Scheme.ProEt.mk (𝟙 X)
    obtain ⟨S, hS, hle⟩ := Scheme.ProEt.mem_topology_iff.mp (q.coversTop V)
    obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hS
    have hw (i : C.I₀) : (C.f i).left = (C.X i).hom := by
      have h := MorphismProperty.Over.w (C.f i)
      change (C.f i).left ≫ 𝟙 X = (C.X i).hom at h
      exact (Category.comp_id _).symm.trans h
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
      { I₀ := C.I₀
        X := fun i ↦ (C.X i).left
        f := fun i ↦ (C.X i).hom
        mem₀ := by
          have hm := Scheme.ProEt.mem_precoverage_iff.mp C.mem₀
          rw [Presieve.map_ofArrows] at hm
          change (Presieve.ofArrows (fun i ↦ (C.X i).left)
            (fun i ↦ (C.f i).left)) ∈ Scheme.proetalePrecoverage X at hm
          simpa only [hw] using hm }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let D' := D.restrictIndexOfSmall.{u}
    refine ⟨D', fun s ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D s
    obtain ⟨i, ⟨a⟩⟩ := hle _ _ (.mk j)
    obtain ⟨n, ⟨en⟩⟩ := hfree i
    have en' : Nonempty (M.over (C.X j) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let F := SheafOfModules.overMap R a
      let e : F.obj (SheafOfModules.unit (R.over (q.X i))) ≅
          SheafOfModules.unit (R.over (C.X j)) := SheafOfModules.overMapUnitIso a
      exact ⟨((SheafOfModules.overFunctorMap R a).app M).symm ≪≫ F.mapIso en ≪≫
        (SheafOfModules.mapFreeIso F _ e.symm).symm⟩
    exact (section_slice_free X A P (C.X j)).mp ⟨n, en'⟩

end WeilConjectures.AdicFiniteRealization
