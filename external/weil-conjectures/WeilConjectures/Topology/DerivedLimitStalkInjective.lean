/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleDerivedSections
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology
import WeilConjectures.Topology.CohomologyPresheafDerivedSectionsEvaluation
import WeilConjectures.Topology.RingedSpaceRGammaDerivedLimit

/-!
# Stalk injectivity for a derived inverse limit

Source: Stacks Project, Cohomology of Sheaves, Tag 0D61,
lemma-cohomology-derived-limit-injective
(blueprint: lem-pc-ringed-space-derived-limit-stalk-injective).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

private theorem tower_limit_projection_injective
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n₀ : ℕ)
    (h : ∀ n (hn : n₀ ≤ n), Function.Injective (F.map (homOfLE hn).op)) :
    Function.Injective (limit.π F (op n₀)) := by
  intro s t heq
  apply Concrete.limit_ext F s t
  intro j
  obtain ⟨n⟩ := j
  by_cases hn : n₀ ≤ n
  · apply h n hn
    simpa only [← ConcreteCategory.comp_apply, limit.w] using heq
  · have hn' : n ≤ n₀ := Nat.le_of_not_ge hn
    have hh := congrArg (fun z ↦ F.map (homOfLE hn').op z) heq
    simpa only [← ConcreteCategory.comp_apply, limit.w] using hh

-- Transport between derived sections, presheaf evaluation and module stalks needs extra reduction.
/-- Eventual injectivity of open cohomology and vanishing of its first derived inverse
limit imply injectivity of the specified projection on cohomology stalks.
Source: Stacks Project, Cohomology of Sheaves, Tag 0D61,
lemma-cohomology-derived-limit-injective
(blueprint: lem-pc-ringed-space-derived-limit-stalk-injective).

Proof:
1. By lem-pc-ringed-space-sheafification-cohomology (Tag 0BKJ), represent a stalk class
in the kernel by a class over an open neighborhood. Its image has zero germ, so shrink
until its image at level n₀ vanishes, then refine to an element of the fundamental system.
2. Apply lem-pc-ringed-space-rgamma-derived-limit (Tag 0D60). Its Milnor short exact
sequence has left term zero by hlim. The inverse limit maps injectively to level n₀:
compatibility and hinj kill all later components, and compatibility kills earlier ones.
The representative therefore vanishes.
3. Its germ is zero, giving the claimed injectivity. The projection used throughout
is p followed by the n₀-th product projection; no canonical derived limit is chosen. -/
theorem derivedLimit_stalk_injective (X : RingedSpace.{u})
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (p : L ⟶ ∏ᶜ (fun n : ℕ => K.obj (op n)))
    (δ : (∏ᶜ (fun n : ℕ => K.obj (op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (x : X) (m : ℤ) (n₀ : ℕ) (B : Set (Opens X))
    (hB_mem : ∀ U ∈ B, x ∈ U)
    (hB_basis : ∀ V : Opens X, x ∈ V → ∃ U ∈ B, U ≤ V)
    (hlim : ∀ U ∈ B, IsZero
      ((@Functor.rightDerived _ _ _ _ _
        (@InjectiveResolution.instHasInjectiveResolutions _ _ _ roosTowerEnoughInjectives) _
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) roosLimitAdditive 1).obj
        (K ⋙ openModuleDerivedSections X U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1))))
    (hinj : ∀ U ∈ B, ∀ (n : ℕ) (h : n₀ ≤ n), Function.Injective
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((openModuleDerivedSections X U).map (K.map (homOfLE h).op)))) :
    Function.Injective ((moduleStalkFunctor X x).map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).map
        (p ≫ Pi.π (fun n : ℕ => K.obj (op n)) n₀))).hom := by
  have hlocal : ∀ U ∈ B, Function.Injective
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((openModuleDerivedSections X U).map (p ≫ Pi.π _ n₀))) := by
    intro U hU
    obtain ⟨a, b, hz, hseq, hb⟩ := (rgamma_derivedLimit X U K L p δ hK).2 m
    have ha : a = 0 := (hlim U hU).eq_of_src a 0
    have : Mono b := hseq.exact.mono_g ha
    have hb_inj := (AddCommGrpCat.mono_iff_injective b).mp inferInstance
    have hπ := tower_limit_projection_injective
      (K ⋙ openModuleDerivedSections X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} m) n₀ (hinj U hU)
    rw [← hb n₀]
    exact hπ.comp hb_inj
  obtain ⟨P, hP, e, θ, hθ, hrep, hzero, hnat⟩ := sheafification_cohomology X m
  let f := p ≫ Pi.π (fun n : ℕ ↦ K.obj (op n)) n₀
  have hP_inj : ∀ U ∈ B, Function.Injective ((P.map f).app (op U)) := by
    intro U hU
    obtain ⟨eU⟩ := cohomology_presheaf_derivedSections_evaluation X m P hP U
    intro s t hst
    apply (ConcreteCategory.bijective_of_isIso (eU.hom.app L)).1
    apply hlocal U hU
    have hs := congrArg (fun z ↦ eU.hom.app (K.obj (op n₀)) z) hst
    change eU.hom.app (K.obj (op n₀))
        ((P ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op U)).map f s) =
      eU.hom.app (K.obj (op n₀))
        ((P ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op U)).map f t) at hs
    rw [eU.hom.naturality_apply, eU.hom.naturality_apply] at hs
    exact hs
  apply (injective_iff_map_eq_zero _).2
  intro t ht
  obtain ⟨U, hxU, s, hs⟩ := hrep L x t
  have hst : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hxU)
      ((θ.app (K.obj (op n₀))).app (op U) ((P.map f).app (op U) s)) = 0 := by
    rw [hnat, hs]
    exact ht
  obtain ⟨V, hxV, i, hi⟩ := hzero (K.obj (op n₀)) U x hxU _ hst
  obtain ⟨W, hW, hWV⟩ := hB_basis V hxV
  let j : W ⟶ V := homOfLE hWV
  have hV : (P.map f).app (op V) ((P.obj L).map i.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, (P.map f).naturality]
    exact hi
  have hWzero : (P.map f).app (op W)
      ((P.obj L).map j.op ((P.obj L).map i.op s)) = 0 := by
    rw [← ConcreteCategory.comp_apply, (P.map f).naturality,
      ConcreteCategory.comp_apply, hV, map_zero]
  have hsW : (P.obj L).map j.op ((P.obj L).map i.op s) = 0 :=
    (hP_inj W hW) (by simpa using hWzero)
  have hres : ∀ {A C : Opens X} (k : C ⟶ A) (hxC : x ∈ C)
      (z : (P.obj L).obj (op A)),
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ C x hxC)
          ((θ.app L).app (op C) ((P.obj L).map k.op z)) =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ A x (k.le hxC))
          ((θ.app L).app (op A) z) := by
    intro A C k hxC z
    rw [(θ.app L).naturality_apply]
    exact TopCat.Presheaf.germ_res_apply _ k x hxC _
  rw [← hs, ← hres i hxV s,
    ← hres j (hB_mem W hW) ((P.obj L).map i.op s), hsW, map_zero, map_zero]

end AlgebraicGeometry.RingedSpace
