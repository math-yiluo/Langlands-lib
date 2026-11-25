/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSplitHomDescent
import Mathlib.Tactic.CongrExclamation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent

/-! # Compatibility of canonical sums of sheet projections

Source: blueprint, stratified lattice trace proof; Stacks Project, Tag 03SH.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- The sum of the actual counit projections, conjugated by composition comparisons.
Source: blueprint, stratified lattice trace proof, local computation.
(blueprint: lem-sfb-finite-etale-sheet-sum-compatible) -/
abbrev finiteEtaleSheetSum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (c : FiniteEtaleModuleChart p) :
    (upperStar Λ c.map).obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ⟶
      (upperStar Λ c.map).obj P :=
  finiteEtaleTraceSheetSum Λ p P c.map c.degree c.sheet c.over

private theorem splitting_pullback {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (a : Z ⟶ Y) (k : Z ⟶ X) (hk : a ≫ g = k) (n : ℕ) (t : Fin n → (Y ⟶ U))
    (w : ∀ j, t j ≫ p = g)
    (hc : IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))) :
    Nonempty (IsColimit (Cofan.mk (pullback p k)
      (fun j ↦ pullback.lift (a ≫ t j) (𝟙 Z)
        (by simp only [Category.assoc, w, Category.id_comp, hk])))) := by
  subst k
  let B : pullback p (a ≫ g) ⟶ pullback p g :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a)
      (by simp only [Category.assoc, pullback.condition])
  let S (j : Fin n) : PullbackCone a (𝟙 Y) :=
    PullbackCone.mk (𝟙 Z) a (by simp)
  have hS (j : Fin n) : IsLimit (S j) :=
    PullbackCone.IsLimit.mk _ (fun q ↦ q.fst) (by simp)
      (by intro q; simpa [S] using q.condition) (by intro q m hm _; exact hm)
  let T : PullbackCone a (pullback.snd p g) :=
    PullbackCone.mk (pullback.snd p (a ≫ g)) B (by simp [B])
  have hT : IsLimit T := by
    refine PullbackCone.IsLimit.mk _ (fun q ↦
      pullback.lift (q.snd ≫ pullback.fst p g) q.fst ?_) ?_ ?_ ?_
    · simp only [Category.assoc, pullback.condition]
      exact congrArg (fun k ↦ k ≫ g) q.condition.symm
    · intro q
      simp
    · intro q
      apply pullback.hom_ext
      · simp [B]
      · simpa [T, B] using q.condition
    · intro q m hm₁ hm₂
      apply pullback.hom_ext
      · have h := congrArg (fun k ↦ k ≫ pullback.fst p g) hm₂
        simpa [T, B] using h
      · simpa [T] using hm₁
  let hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc
  let d : Cofan (fun _ : Fin n ↦ Z) := Cofan.mk (pullback p (a ≫ g))
    (fun j ↦ pullback.lift (a ≫ t j) (𝟙 Z) (by simp [Category.assoc, w]))
  exact hu.nonempty_isColimit_of_pullbackCone_left (fun _ ↦ 𝟙 Y) (pullback.snd p g) a
      S hS T hT d (Iso.refl _) (by intro j; simp) (by simp [d, S, T]) (by
        intro j
        change (pullback.lift (a ≫ t j) (𝟙 Z) _ ≫ 𝟙 _) ≫ B =
          a ≫ pullback.lift (t j) (𝟙 Y) _
        simp only [Category.comp_id]
        apply pullback.hom_ext
        · simp [B, Category.assoc]
        · simp only [Category.assoc, B, pullback.lift_snd]
          rw [← Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id])

private theorem refined_sheets_locally_permute {X U : Scheme.{u}} (p : U ⟶ X)
    (c₁ c₂ : FiniteEtaleModuleChart p) (Z : Scheme.{u})
    (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) (w : a ≫ c₁.map = b ≫ c₂.map) (z : Z) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ e : Fin c₁.degree ≃ Fin c₂.degree,
      ∀ j, O.ι ≫ a ≫ c₁.sheet j = O.ι ≫ b ≫ c₂.sheet (e j) := by
  classical
  let g := a ≫ c₁.map
  let s₁ (j : Fin c₁.degree) : Z ⟶ pullback p g :=
    pullback.lift (a ≫ c₁.sheet j) (𝟙 Z)
      (by simp [g, Category.assoc, c₁.over])
  let s₂ (j : Fin c₂.degree) : Z ⟶ pullback p g :=
    pullback.lift (b ≫ c₂.sheet j) (𝟙 Z)
      (by simp [g, Category.assoc, c₂.over, w])
  have hc₁ : IsColimit (Cofan.mk (pullback p g) s₁) :=
    (splitting_pullback p c₁.map a g rfl c₁.degree c₁.sheet c₁.over c₁.splits.some).some
  have hc₂ : IsColimit (Cofan.mk (pullback p g) s₂) :=
    (splitting_pullback p c₂.map b g w.symm c₂.degree c₂.sheet c₂.over c₂.splits.some).some
  let hc₁' := (Cofan.isColimitEquivOfEquiv
    (Equiv.ulift : ULift.{u} (Fin c₁.degree) ≃ _) _).toFun hc₁
  let hc₂' := (Cofan.isColimitEquivOfEquiv
    (Equiv.ulift : ULift.{u} (Fin c₂.degree) ≃ _) _).toFun hc₂
  obtain ⟨O, hz, e, he⟩ := finiteSectionCoproduct_local_permutation Z (pullback p g)
    (pullback.snd p g) (ULift.{u} (Fin c₁.degree)) (ULift.{u} (Fin c₂.degree))
    (fun j ↦ s₁ j.down) (fun j ↦ s₂ j.down) hc₁' hc₂'
      (fun j ↦ pullback.lift_snd _ _ _) (fun j ↦ pullback.lift_snd _ _ _) z
  refine ⟨O, hz, Equiv.ulift.symm.trans (e.trans Equiv.ulift), fun j ↦ ?_⟩
  simpa [s₁, s₂, Category.assoc] using
    congrArg (fun k ↦ k ≫ pullback.fst p g) (he ⟨j⟩)

private theorem module_hom_ext_open
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f g : M ⟶ N) (O : X → X.Opens) (hO : ∀ x, x ∈ O x)
    (h : ∀ x, (upperStar Λ (O x).ι).map f = (upperStar Λ (O x).ι).map g) : f = g := by
  apply (Mod.forget _).map_injective
  apply ProEtale.hom_ext_of_openImmersionRestriction Ab.{u + 1} (fun x ↦ (O x).ι)
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, ⟨⟨x, hO x⟩, rfl⟩⟩
  · intro x
    let E := profinitePointModuleForgetPullbackIso Λ (O x).ι
    have h' : (ProEtale.upperStar Ab.{u + 1} (O x).ι).map ((Mod.forget _).map f) =
        (ProEtale.upperStar Ab.{u + 1} (O x).ι).map ((Mod.forget _).map g) := by
      apply (cancel_epi (E.hom.app M)).mp
      calc
        _ = (Mod.forget _).map ((upperStar Λ (O x).ι).map f) ≫ E.hom.app N :=
          (E.hom.naturality f).symm
        _ = (Mod.forget _).map ((upperStar Λ (O x).ι).map g) ≫ E.hom.app N := by rw [h x]
        _ = _ := E.hom.naturality g
    let R := ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} (O x).ι
    apply (cancel_epi (R.hom.app M.X)).mp
    rw [← R.hom.naturality, ← R.hom.naturality, h']

private theorem eq_iso_symm_congr {A B : Type*} [Category B]
    (F : A → B) {a b : A} (w : a = b) :
    (eqToIso (congrArg F w)).symm = eqToIso (congrArg F w.symm) := by
  cases w
  rfl

private theorem proof_heq {A B : Prop} (a : A) (b : B) : HEq a b := by
  have h : A = B := propext ⟨fun _ ↦ b, fun _ ↦ a⟩
  cases h
  rfl

private theorem iso_family_composite {I J : Type*} {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : I → C ⥤ D) (R : J → C ⥤ E) (f : I → J) (H : D ⥤ E)
    (A : ∀ i, R (f i) ≅ F i ⋙ H) {K : C ⥤ E} {i j : I} {x : J}
    (e : x = f i) (w : i = j) (B : F i ⋙ H ≅ K) (D₀ : R x ≅ K)
    (h : A i ≪≫ B = (eqToIso (congrArg R e)).symm ≪≫ D₀) :
    A j ≪≫ Functor.isoWhiskerRight (eqToIso (congrArg F w)).symm H ≪≫ B =
      (eqToIso (congrArg R (e.trans (congrArg f w)))).symm ≪≫ D₀ := by
  cases w
  simpa only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Iso.refl_trans] using h

private theorem comparison_assoc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (t : Y ⟶ U) (a : Z ⟶ Y) :
    upperStarComp Λ a (t ≫ p) ≪≫
        Functor.isoWhiskerRight (upperStarComp Λ t p) (upperStar Λ a) ≪≫
        (upperStar Λ p).associator (upperStar Λ t) (upperStar Λ a) =
      (eqToIso (congrArg (upperStar Λ) (Category.assoc a t p))).symm ≪≫
        upperStarComp Λ (a ≫ t) p ≪≫
        Functor.isoWhiskerLeft (upperStar Λ p) (upperStarComp Λ a t) := by
  rw [eq_iso_symm_congr (upperStar Λ) (Category.assoc a t p)]
  exact upperStarComp_assoc Λ a t p

private theorem comparison_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (a : Z ⟶ Y) :
    upperStarComp Λ a g ≪≫
        Functor.isoWhiskerRight
          ((eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p)
          (upperStar Λ a) ≪≫
        (upperStar Λ p).associator (upperStar Λ t) (upperStar Λ a) =
      ((eqToIso (congrArg (upperStar Λ)
        ((Category.assoc a t p).trans (congrArg (fun k ↦ a ≫ k) w)))).symm ≪≫
        upperStarComp Λ (a ≫ t) p) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ p) (upperStarComp Λ a t) := by
  have h := iso_family_composite (fun k : Y ⟶ X ↦ upperStar Λ k)
    (fun k : Z ⟶ X ↦ upperStar Λ k) (fun k ↦ a ≫ k) (upperStar Λ a)
    (fun k ↦ upperStarComp Λ a k) (Category.assoc a t p) w
    (Functor.isoWhiskerRight (upperStarComp Λ t p) (upperStar Λ a) ≪≫
      (upperStar Λ p).associator (upperStar Λ t) (upperStar Λ a))
    (upperStarComp Λ (a ≫ t) p ≪≫
      Functor.isoWhiskerLeft (upperStar Λ p) (upperStarComp Λ a t))
    (comparison_assoc Λ p t a)
  simpa only [Functor.isoWhiskerRight_trans, Iso.trans_assoc] using h

private theorem sheet_comparison_pullback_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (a : Z ⟶ Y) :
    upperStarComp Λ a g ≪≫
        Functor.isoWhiskerRight (finiteEtaleTraceSheetComparison Λ p g t w)
          (upperStar Λ a) ≪≫
        (upperStar Λ p).associator (upperStar Λ t) (upperStar Λ a) =
      finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
        (by simp only [Category.assoc, w]) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ p) (upperStarComp Λ a t) := by
  let B := (upperStar Λ p).associator (upperStar Λ t) (upperStar Λ a)
  let D := Functor.isoWhiskerLeft (upperStar Λ p) (upperStarComp Λ a t)
  calc
    _ = upperStarComp Λ a g ≪≫
        Functor.isoWhiskerRight
          ((eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p)
          (upperStar Λ a) ≪≫ B :=
      congrArg (fun C ↦ upperStarComp Λ a g ≪≫
        Functor.isoWhiskerRight C (upperStar Λ a) ≪≫ B)
        (finiteEtaleTraceSheetComparison_eq Λ p g t w)
    _ = ((eqToIso (congrArg (upperStar Λ)
        ((Category.assoc a t p).trans (congrArg (fun k ↦ a ≫ k) w)))).symm ≪≫
        upperStarComp Λ (a ≫ t) p) ≪≫ D := comparison_transport Λ p g t w a
    _ = _ := congrArg (fun C ↦ C ≪≫ D)
      (finiteEtaleTraceSheetComparison_eq Λ p (a ≫ g) (a ≫ t)
        ((Category.assoc a t p).trans (congrArg (fun k ↦ a ≫ k) w))).symm

private theorem sheet_comparison_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (a : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ a g).hom.app M ≫
        (upperStar Λ a).map ((finiteEtaleTraceSheetComparison Λ p g t w).hom.app M) =
      (finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
        (by simp only [Category.assoc, w])).hom.app M ≫
        (upperStarComp Λ a t).hom.app ((upperStar Λ p).obj M) := by
  have h := congrArg (fun e ↦ e.hom.app M) (sheet_comparison_pullback_iso Λ p g t w a)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] using h

@[irreducible]
private def sheet_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    (upperStar Λ g).obj Q ⟶ (upperStar Λ g).obj P :=
  (finiteEtaleTraceSheetComparison Λ p g t w).hom.app Q ≫
    (upperStar Λ t).map ε ≫ (finiteEtaleTraceSheetComparison Λ p g t w).inv.app P

private theorem sheet_projection_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (a : Z ⟶ Y) :
    (upperStarComp Λ a g).hom.app Q ≫
        (upperStar Λ a).map (sheet_projection Λ p Q P ε g t w) ≫
        (upperStarComp Λ a g).inv.app P =
      sheet_projection Λ p Q P ε (a ≫ g) (a ≫ t)
        (by simp only [Category.assoc, w]) := by
  let C := finiteEtaleTraceSheetComparison Λ p g t w
  let D := finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
    (by simp only [Category.assoc, w])
  have hP : (upperStarComp Λ a t).hom.app ((upperStar Λ p).obj P) ≫
        (upperStar Λ a).map (C.inv.app P) ≫ (upperStarComp Λ a g).inv.app P =
      D.inv.app P := by
    apply (cancel_epi (D.hom.app P)).mp
    rw [← Category.assoc, ← sheet_comparison_pullback Λ p g t w a P]
    simp only [C, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  unfold sheet_projection
  simp only [Functor.map_comp, ← Category.assoc]
  rw [sheet_comparison_pullback Λ p g t w a Q]
  simp only [Category.assoc]
  have hε := (upperStarComp Λ a t).hom.naturality ε
  simp only [Functor.comp_map] at hε
  rw [reassoc_of% hε.symm]
  simpa only [C, D, Category.assoc] using congrArg
    (fun k ↦ (D.hom.app Q ≫ (upperStar Λ (a ≫ t)).map ε) ≫ k) hP

private theorem sum_projection_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (a : Z ⟶ Y) :
    (upperStarComp Λ a g).hom.app Q ≫
        (upperStar Λ a).map (∑ j, sheet_projection Λ p Q P ε g (t j) (w j)) ≫
        (upperStarComp Λ a g).inv.app P =
      ∑ j, sheet_projection Λ p Q P ε (a ≫ g) (a ≫ t j)
        (by simp only [Category.assoc, w]) := by
  simp only [Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun j _ ↦ sheet_projection_pullback Λ p Q P ε g (t j) (w j) a

private theorem sum_projection_pullback_to
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (a : Z ⟶ Y) (k : Z ⟶ X) (hk : a ≫ g = k) :
    ((eqToIso (congrArg (upperStar Λ) hk.symm)) ≪≫ upperStarComp Λ a g).hom.app Q ≫
        (upperStar Λ a).map (∑ j, sheet_projection Λ p Q P ε g (t j) (w j)) ≫
      ((eqToIso (congrArg (upperStar Λ) hk.symm)) ≪≫ upperStarComp Λ a g).inv.app P =
      ∑ j, sheet_projection Λ p Q P ε k (a ≫ t j)
        (by simp only [Category.assoc, w, hk]) := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]
  exact sum_projection_pullback Λ p Q P ε g n t w a

@[irreducible]
private def trace_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStar Λ p).obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ⟶
      (upperStar Λ p).obj P :=
  (upperStarLowerStarAdjunction Λ p).counit.app ((upperStar Λ p).obj P)

private theorem sheet_sum_eq_projection_sum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g) :
    finiteEtaleTraceSheetSum Λ p P g n t w =
      ∑ j, sheet_projection Λ p ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) P
        (trace_counit Λ p P) g (t j) (w j) := by
  unfold finiteEtaleTraceSheetSum trace_counit sheet_projection
  rfl

private theorem sum_projection_eq_of_permutation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Z ⟶ X) (n₁ n₂ : ℕ) (t₁ : Fin n₁ → (Z ⟶ U))
    (t₂ : Fin n₂ → (Z ⟶ U)) (w₁ : ∀ j, t₁ j ≫ p = g) (w₂ : ∀ j, t₂ j ≫ p = g)
    (e : Fin n₁ ≃ Fin n₂) (he : ∀ j, t₁ j = t₂ (e j)) :
    (∑ j, sheet_projection Λ p Q P ε g (t₁ j) (w₁ j)) =
      ∑ j, sheet_projection Λ p Q P ε g (t₂ j) (w₂ j) := by
  apply Fintype.sum_equiv e
  intro j
  have ht : (⟨t₁ j, w₁ j⟩ : {t : Z ⟶ U // t ≫ p = g}) = ⟨t₂ (e j), w₂ (e j)⟩ :=
    Subtype.ext (he j)
  exact congrArg (fun s : {t : Z ⟶ U // t ≫ p = g} ↦
    sheet_projection Λ p Q P ε g s.val s.property) ht

private theorem projection_sum_eq_of_local_permutation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (g : Z ⟶ X) (n₁ n₂ : ℕ) (t₁ : Fin n₁ → (Z ⟶ U))
    (t₂ : Fin n₂ → (Z ⟶ U)) (w₁ : ∀ j, t₁ j ≫ p = g) (w₂ : ∀ j, t₂ j ≫ p = g)
    (h : ∀ z : Z, ∃ O : Z.Opens, z ∈ O ∧ ∃ e : Fin n₁ ≃ Fin n₂,
      ∀ j, O.ι ≫ t₁ j = O.ι ≫ t₂ (e j)) :
    (∑ j, sheet_projection Λ p Q P ε g (t₁ j) (w₁ j)) =
      ∑ j, sheet_projection Λ p Q P ε g (t₂ j) (w₂ j) := by
  classical
  choose O hz e he using h
  apply module_hom_ext_open Λ _ _ O hz
  intro z
  apply (cancel_epi ((upperStarComp Λ (O z).ι g).hom.app Q)).mp
  apply (cancel_mono ((upperStarComp Λ (O z).ι g).inv.app P)).mp
  have h₁ := sum_projection_pullback Λ p Q P ε g n₁ t₁ w₁ (O z).ι
  have h₂ := sum_projection_pullback Λ p Q P ε g n₂ t₂ w₂ (O z).ι
  simp only [Category.assoc]
  rw [h₁, h₂]
  exact sum_projection_eq_of_permutation Λ p Q P ε
    ((O z).ι ≫ g) _ _ _ _ _ _ (e z) (he z)

@[irreducible]
private def chart_projection_sum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (c : FiniteEtaleModuleChart p) :
    (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P :=
  ∑ j, sheet_projection Λ p Q P ε c.map (c.sheet j) (c.over j)

private theorem chart_projection_sum_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (c : FiniteEtaleModuleChart p) (a : Z ⟶ c.base) :
    (upperStarComp Λ a c.map).hom.app Q ≫
        (upperStar Λ a).map (chart_projection_sum Λ p Q P ε c) ≫
      (upperStarComp Λ a c.map).inv.app P =
      ∑ j, sheet_projection Λ p Q P ε (a ≫ c.map) (a ≫ c.sheet j)
        (by simp only [Category.assoc, c.over]) := by
  unfold chart_projection_sum
  exact sum_projection_pullback Λ p Q P ε c.map c.degree c.sheet c.over a

private theorem chart_projection_sum_pullback_to
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P)
    (c : FiniteEtaleModuleChart p) (a : Z ⟶ c.base) (k : Z ⟶ X)
    (hk : a ≫ c.map = k) :
    ((eqToIso (congrArg (upperStar Λ) hk.symm)) ≪≫
        upperStarComp Λ a c.map).hom.app Q ≫
        (upperStar Λ a).map (chart_projection_sum Λ p Q P ε c) ≫
      ((eqToIso (congrArg (upperStar Λ) hk.symm)) ≪≫
        upperStarComp Λ a c.map).inv.app P =
      ∑ j, sheet_projection Λ p Q P ε k (a ≫ c.sheet j)
        (by simp only [Category.assoc, c.over, hk]) := by
  unfold chart_projection_sum
  exact sum_projection_pullback_to Λ p Q P ε c.map c.degree c.sheet c.over a k hk

private theorem chart_projection_sum_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (c : FiniteEtaleModuleChart p) :
    chart_projection_sum Λ p ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) P
      (trace_counit Λ p P) c = finiteEtaleSheetSum Λ p P c := by
  unfold chart_projection_sum
  exact (sheet_sum_eq_projection_sum Λ p P c.map c.degree c.sheet c.over).symm

attribute [local semireducible] FiniteEtaleModuleChart.Compatible

private theorem projection_sums_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ p).obj Q ⟶ (upperStar Λ p).obj P) :
    FiniteEtaleModuleChart.Compatible Λ Q P (chart_projection_sum Λ p Q P ε) := by
  intro c₁ c₂ Z a b _ _ w
  have h₁ := chart_projection_sum_pullback Λ p Q P ε c₁ a
  have h₂ := chart_projection_sum_pullback_to Λ p Q P ε c₂ b _ w.symm
  refine Eq.trans h₁ ?_
  refine Eq.trans (projection_sum_eq_of_local_permutation Λ p Q P ε
    (a ≫ c₁.map) c₁.degree c₂.degree
    (fun j ↦ a ≫ c₁.sheet j) (fun j ↦ b ≫ c₂.sheet j)
    (fun j ↦ by simp only [Category.assoc, c₁.over])
    (fun j ↦ by simp only [Category.assoc, c₂.over, w])
    (fun z ↦ refined_sheets_locally_permute p c₁ c₂ Z a b w z)) ?_
  refine Eq.trans h₂.symm ?_
  -- Compare arguments syntactically: the default congruence tactic treats the
  -- imported proof arguments as definitionally equal and leaves a costly conversion.
  run_tac Lean.Elab.Tactic.withMainContext do
    let step (g : Lean.MVarId) : Lean.MetaM (List Lean.MVarId) := g.withContext do
      if ← g.isAssigned then return []
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).cleanupAnnotations == t.cleanupAnnotations then
          g.assign (.fvar d.fvarId)
          return []
      if t.isForall then
        let (_, g) ← g.intro1P
        return [g]
      let g ← g.eqOfHEq
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let some (_, lhs, _, rhs) := t.heq? | throwError "expected heterogeneous equality: {t}"
      let lhs := lhs.cleanupAnnotations
      let rhs := rhs.cleanupAnnotations
      if lhs == rhs then
        g.hrefl
        return []
      if (← Lean.Meta.isProof lhs) && (← Lean.Meta.isProof rhs) then
        g.assign (← Lean.Meta.mkAppM ``proof_heq #[lhs, rhs])
        return []
      if lhs.isLambda && rhs.isLambda then
        let g ← g.heqOfEq
        return ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``funext)
      let f := lhs.getAppFn
      let f' := rhs.getAppFn
      let xs := lhs.getAppArgs
      let ys := rhs.getAppArgs
      unless f == f' && xs.size == ys.size && !xs.isEmpty do
        throwError "cannot compare {lhs} and {rhs} by syntactic congruence"
      let info ← Lean.Meta.getFunInfoNArgs f xs.size
      let fixed := xs.zipWith (fun x y ↦ x.cleanupAnnotations == y.cleanupAnnotations) ys
      let c ← Lean.Meta.mkRichHCongr (forceHEq := true) (← Lean.Meta.inferType f) info
        (fixedFun := true) (fixedParams := fixed)
      g.apply (c.proof.beta #[f])
    let mut todo := #[← Lean.Elab.Tactic.getMainGoal]
    for _ in [:10000] do
      if todo.isEmpty then break
      let g := todo.back!
      todo := todo.pop
      todo := todo ++ (← step g).toArray
    unless todo.isEmpty do throwError "syntactic congruence did not finish"
    Lean.Elab.Tactic.replaceMainGoal []

private theorem compatible_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} {p : U ⟶ X}
    (Q P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d e : ∀ c : FiniteEtaleModuleChart p,
      (upperStar Λ c.map).obj Q ⟶ (upperStar Λ c.map).obj P)
    (h : ∀ c, d c = e c) (hd : FiniteEtaleModuleChart.Compatible Λ Q P d) :
    FiniteEtaleModuleChart.Compatible Λ Q P e := by
  have he : d = e := funext h
  cases he
  exact hd

/-- Sheet sums agree on overlaps, independently of the enumeration of the sheets.
Source: blueprint, stratified lattice trace proof, local computation;
Stacks Project, Tag 03SH.
(blueprint: lem-sfb-finite-etale-sheet-sum-compatible)

Proof in words. Refine the two splitting charts to a common weakly etale scheme Z.
Each splitting gives a finite family of disjoint open-and-closed sections of
U times_X Z. Intersect each sheet of one splitting with every sheet of the other.
These intersections give a covering of Z by open-and-closed pieces on each of
which the two enumerations differ by a bijection. This follows from the finite
section coproduct local permutation lemma and includes the empty family.
Inverse-image composition coherence and naturality show that every conjugated
counit projection commutes with further pullback. The same calculation holds
for any morphism between the two p-pullbacks. On each piece the two sums are
therefore reindexings of the same finite sum. Reindex the sum by that bijection
and use separatedness of linear sheaf morphisms to descend the equality to Z.
No finiteness condition on p is needed beyond the two given finite splittings. -/
theorem finiteEtaleSheetSum_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    FiniteEtaleModuleChart.Compatible Λ
      ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) P
      (finiteEtaleSheetSum Λ p P) := by
  apply compatible_congr Λ _ P _ (finiteEtaleSheetSum Λ p P)
    (chart_projection_sum_eq Λ p P)
  exact projection_sums_compatible Λ p _ P (trace_counit Λ p P)

end AlgebraicGeometry.ProEtale.CondensedRing
