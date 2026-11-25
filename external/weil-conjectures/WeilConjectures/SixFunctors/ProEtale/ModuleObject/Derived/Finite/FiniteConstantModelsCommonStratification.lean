/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Common reduced strata for finite families of constant-model constructible sheaves -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [-instance] essentiallySmallSelfInstance

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarFromPoint
  Mod.extendScalarsIsoComapInv

private theorem orderedStrata_schemes
    (X : Scheme.{u}) (r : ℕ) (Q : Fin r → Set X)
    (_hQl : ∀ a, IsLocallyClosed (Q a))
    (hQd : Pairwise (fun a b ↦ Disjoint (Q a) (Q b)))
    (hQtail : ∀ k : ℕ,
      IsClosed (Set.univ \ ⋃ a : Fin r, ⋃ (_ : a.val < k), Q a)) :
    ∃ (D : Fin r → Scheme.{u}) (f : ∀ a, D a ⟶ X)
      (Z : Fin (r + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
      (v : ∀ a : Fin r, D a ⟶ Z a.castSucc),
      (∀ a, IsReduced (D a)) ∧ (∀ a, IsImmersion (f a)) ∧
      (∀ a, Set.range (f a) = Q a) ∧
      (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k)) ∧
      (∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = f a) ∧
      ∀ k, Set.range (i k) = (⋃ a : Fin r, ⋃ (_ : a.val < k.val), Q a)ᶜ := by
  classical
  let U (k : Fin (r + 1)) : X.Opens :=
    ⟨⋃ a : Fin r, ⋃ (_ : a.val < k.val), Q a, by
      have ht : IsClosed ((⋃ a : Fin r, ⋃ (_ : a.val < k.val), Q a)ᶜ) := by
        simpa only [TopologicalSpace.Closeds.coe_top, ← Set.compl_eq_univ_sdiff] using
          hQtail k.val
      simpa only [compl_compl] using ht.isOpen_compl⟩
  let Z (k : Fin (r + 1)) : TopologicalSpace.Closeds X :=
    ⟨(U k : Set X)ᶜ, (U k).isOpen.isClosed_compl⟩
  let I (k : Fin (r + 1)) := Scheme.IdealSheafData.vanishingIdeal (Z k)
  let W (a : Fin r) : (I a.castSucc).subscheme.Opens :=
    (I a.castSucc).subschemeι ⁻¹ᵁ U a.succ
  let f (a : Fin r) := (W a).ι ≫ (I a.castSucc).subschemeι
  have hrange (a : Fin r) : Set.range (f a) = Q a := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : (f a) y ∈ U a.succ := y.property
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hb, hyb⟩ := Set.mem_iUnion.mp hb
      have hnot : (f a) y ∉ U a.castSucc := by
        have h : (f a) y ∈ Set.range (I a.castSucc).subschemeι := ⟨_, rfl⟩
        rw [Scheme.IdealSheafData.range_subschemeι] at h
        exact h
      have he : b = a := by
        apply Fin.ext
        by_contra he
        have hlt : b.val < a.val := by
          simp only [Fin.val_succ] at hb
          omega
        exact hnot (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hlt, hyb⟩⟩)
      simpa only [he] using hyb
    · intro hx
      have hnot : x ∉ U a.castSucc := by
        rintro h
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        have hne : a ≠ b := by
          intro he
          subst b
          exact (lt_irrefl a.val) (by simpa only [Fin.val_castSucc] using hb)
        exact Set.disjoint_left.mp (hQd hne) hx hxb
      have hxI : x ∈ Set.range (I a.castSucc).subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hnot
      obtain ⟨z, hz⟩ := hxI
      refine ⟨⟨z, ?_⟩, hz⟩
      change (I a.castSucc).subschemeι z ∈ U a.succ
      rw [hz]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩
  have hred (k : Fin (r + 1)) : IsReduced (I k).subscheme :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X (Z k)).2.2.2.1
  refine ⟨fun a ↦ (W a).toScheme, f, fun k ↦ (I k).subscheme,
    fun k ↦ (I k).subschemeι, fun a ↦ (W a).ι, ?_, fun _ ↦ inferInstance,
    hrange, fun k ↦ ⟨inferInstance, hred k⟩,
    fun _ ↦ ⟨inferInstance, rfl⟩, fun k ↦ (I k).range_subschemeι⟩
  intro a
  have := hred a.castSucc
  exact inferInstanceAs (IsReduced (W a).toScheme)

private theorem commonReduced_geometry
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (A : Fin n → Scheme.Stratification X) :
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ a, IsReduced (R.domain a)) ∧
      (∃ (Z : Fin (R.n + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
        (v : ∀ a : Fin R.n, R.domain a ⟶ Z a.castSucc),
        (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k)) ∧
        (∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = R.immersion a) ∧
        ∀ k, Set.range (i k) =
          (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)ᶜ) ∧
      (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (A j).n,
        R.stratum a ⊆ (A j).stratum b) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) := by
  classical
  let B := (j : Fin n) → Fin (A j).n
  let P : B → Set X := fun b ↦ ⋂ j, (A j).stratum (b j)
  have hl (b : B) : IsLocallyClosed (P b) := by
    choose O Z hO hZ he using fun j ↦ (A j).isLocallyClosed_stratum (b j)
    exact ⟨⋂ j, O j, ⋂ j, Z j, isOpen_iInter_of_finite hO, isClosed_iInter hZ,
      by simp only [P, he, Set.iInter_inter_distrib]⟩
  have hc : (⋃ b, P b) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx (j : Fin n) : ∃ b, x ∈ (A j).stratum b :=
      Set.mem_iUnion.mp ((A j).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    choose b hb using hx
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iInter.mpr hb⟩
  obtain ⟨r, Q, _, hQl, hQc, hQd, hQr, hQtail⟩ :=
    ProEtale.exists_ordered_irreducible_refinement (⊤ : TopologicalSpace.Closeds X) P hl hc
  obtain ⟨D, f, Z, i, v, hred, hf, hrange, hi, hv, hr⟩ :=
    orderedStrata_schemes X r Q hQl hQd hQtail
  let R : X.FiniteLocallyClosedStratification := {
    n := r
    stratum := Q
    isLocallyClosed_stratum := hQl
    iUnion_stratum_eq_univ := hQc
    pairwise_disjoint_stratum := hQd
    domain := D
    immersion := f
    isImmersion := hf
    range_immersion := hrange }
  refine ⟨R, hred, ⟨Z, i, v, hi, hv, hr⟩, ?_, ?_⟩
  · intro j a
    obtain ⟨b, hb⟩ := hQr a
    exact ⟨b j, fun x hx ↦ Set.mem_iInter.mp (hb hx) j⟩
  · intro k
    have ht : IsClosed ((⋃ a : Fin r, ⋃ (_ : a.val < k.val), Q a)ᶜ) := by
      simpa only [TopologicalSpace.Closeds.coe_top, ← Set.compl_eq_univ_sdiff] using
        hQtail k.val
    simpa only [compl_compl] using ht.isOpen_compl

private theorem commonReduced_restrictions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ)
    (M : Fin n → supportModules Λ X) (A : Fin n → Scheme.Stratification X)
    (R : X.FiniteLocallyClosedStratification)
    (hred : ∀ a, IsReduced (R.domain a))
    (href : ∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (A j).n,
      R.stratum a ⊆ (A j).stratum b)
    (hA : ∀ j a, HasFiniteConstantLocalModel Λ ((A j).domain a)
      ((upperStar Λ ((A j).immersion a)).obj (M j))) :
    ∀ j a, HasFiniteConstantLocalModel Λ (R.domain a)
      ((upperStar Λ (R.immersion a)).obj (M j)) := by
  intro j a
  obtain ⟨b, hb⟩ := href j a
  have := hred a
  exact finiteModel_on_reduced_substratum Λ (A j) b (R.immersion a)
    ((R.range_immersion a).le.trans hb) (M j) (hA j b)

private theorem commonReduced_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ)
    (M : Fin n → supportModules Λ X)
    (A : Fin n → Scheme.Stratification X)
    (hA : ∀ j a, HasFiniteConstantLocalModel Λ ((A j).domain a)
      ((upperStar Λ ((A j).immersion a)).obj (M j))) :
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ a, IsReduced (R.domain a)) ∧
      (∃ (Z : Fin (R.n + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
        (v : ∀ a : Fin R.n, R.domain a ⟶ Z a.castSucc),
        (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k)) ∧
        (∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = R.immersion a) ∧
        ∀ k, Set.range (i k) =
          (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)ᶜ) ∧
      (∀ j a, HasFiniteConstantLocalModel Λ (R.domain a)
        ((upperStar Λ (R.immersion a)).obj (M j))) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) := by
  classical
  obtain ⟨R, hred, htails, href, hopen⟩ := commonReduced_geometry X n A
  exact ⟨R, hred, htails, commonReduced_restrictions Λ X n M A R hred href hA, hopen⟩

private theorem finiteStratification_of_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (hX : CompactSpace X ∧ QuasiSeparatedSpace X)
    (M : supportModules Λ X) (hM : IsConstantModelConstructible Λ X M) :
    IsFiniteConstantStratified Λ X M := by
  classical
  simpa only [IsConstantModelConstructible, ite_eq_left hX] using hM

private theorem finiteStratifications_family
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (n : ℕ)
    (M : Fin n → supportModules Λ X)
    (hM : ∀ j, IsFiniteConstantStratified Λ X (M j)) :
    ∃ A : Fin n → Scheme.Stratification X,
      ∀ j a, HasFiniteConstantLocalModel Λ ((A j).domain a)
        ((upperStar Λ ((A j).immersion a)).obj (M j)) := by
  exact Classical.axiomOfChoice hM

/-- A finite family of constructible module sheaves has a common ordered reduced
stratification on which every restriction has a finite constant local model.
Source: blueprint lemma-sections-support-closed-subscheme--3, proof steps 1--5; Stacks Tags 09Y5,
01J3 and 01J4. (blueprint: lem-finite-constant-models-common-reduced-stratification).

Proof: choose an adapted finite stratification for each sheaf. Intersections indexed
by tuples of old stratum indices form a finite locally closed cover. Apply Noetherian
ordered refinement to this cover, obtaining a partition whose prefixes are open.
Realize each piece as an open subscheme of the reduced closed tail before it.
Its map into X factors through the corresponding old immersion: first factor through
the old open coborder, then use reducedness to factor through the closed part.
Exact inverse image pulls back the finite scalar presentation, and the composition
comparison identifies the resulting module with the restriction from X. The empty
family and the empty scheme are included by the same finite-cover argument. -/
theorem finiteConstantModels_commonReducedStratification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ)
    (M : Fin n → supportModules Λ X)
    (hM : ∀ j, IsConstantModelConstructible Λ X (M j)) :
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ a, IsReduced (R.domain a)) ∧
      (∃ (Z : Fin (R.n + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
        (v : ∀ a : Fin R.n, R.domain a ⟶ Z a.castSucc),
        (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k)) ∧
        (∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = R.immersion a) ∧
        ∀ k, Set.range (i k) =
          (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)ᶜ) ∧
      (∀ j a, HasFiniteConstantLocalModel Λ (R.domain a)
        ((upperStar Λ (R.immersion a)).obj (M j))) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  obtain ⟨A, hA⟩ := finiteStratifications_family Λ X n M
    (fun j ↦ finiteStratification_of_constructible Λ X hX (M j) (hM j))
  exact commonReduced_models Λ X n M A hA

end AlgebraicGeometry.ProEtale.CondensedRing
