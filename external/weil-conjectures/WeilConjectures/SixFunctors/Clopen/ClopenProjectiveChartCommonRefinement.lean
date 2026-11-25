/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Clopen.ClopenCompletedRestrictionComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Common refinements of completed projective charts

Source: Stacks Project, proetale.tex, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-clopen-projective-chart-common-refinement).

All restrictions below are ordinary uncompleted derived ringed pullbacks. Coefficient
index zero is exponent one. Finite products of the unit module are finite direct sums.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.ordinaryIntegralDerivedPull WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem chart_cover_closed {X : Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i) (U j))) (i : Fin n) :
    IsClosed (U i : Set X) := by
  classical
  apply (isClopen_of_disjoint_cover_open (b := ⋃ j : {j // j ≠ i}, (U j.1 : Set X))
    ?_ (U i).isOpen (isOpen_iUnion fun j ↦ (U j.1).isOpen) ?_).isClosed
  · intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ j, U j from hcover.symm ▸ hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxj
    exact (TopologicalSpace.Opens.coe_disjoint.mpr
      (hdisjoint j.property.symm)).notMem_of_mem_left hxi hj

private theorem chart_pushforward_unit_isIso
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D} {G : C ⥤ D}
    [G.IsContinuous J L]
    {S : Sheaf J RingCat.{u + 1}} {R : Sheaf L RingCat.{u + 1}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} J L).obj R) [IsIso φ] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  let H := SheafOfModules.toSheaf S ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}
  have : IsIso (H.map (SheafOfModules.unitToPushforwardObjUnit φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (φ.hom.app V)
    exact (ConcreteCategory.isIso_iff_bijective (φ.hom.app V)).mp inferInstance
  exact isIso_of_reflects_iso (SheafOfModules.unitToPushforwardObjUnit φ) H

private theorem chart_map_retract
    {C D : Type*} [Category* C] [Category* D]
    [HasFiniteProducts C] [HasFiniteProducts D]
    (F : C ⥤ D) [PreservesFiniteLimits F] {R : C} {S : D}
    (e : F.obj R ≅ S) (X : C)
    (hX : ∃ (n : ℕ) (ι : X ⟶ ∏ᶜ fun _ : Fin n ↦ R)
      (ρ : (∏ᶜ fun _ : Fin n ↦ R) ⟶ X), ι ≫ ρ = 𝟙 X) :
    ∃ (n : ℕ) (ι : F.obj X ⟶ ∏ᶜ fun _ : Fin n ↦ S)
      (ρ : (∏ᶜ fun _ : Fin n ↦ S) ⟶ F.obj X), ι ≫ ρ = 𝟙 _ := by
  obtain ⟨n, ι, ρ, hιρ⟩ := hX
  let c := PreservesProduct.iso F (fun _ : Fin n ↦ R) ≪≫ Pi.mapIso (fun _ ↦ e)
  refine ⟨n, F.map ι ≫ c.hom, c.inv ≫ F.map ρ, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hιρ, F.map_id]

/-- Finite projective charts for two complete ordinary restrictions admit a common
clopen refinement, with models for the composite ordinary pullbacks.

Source: Stacks Project, Tag 09C3, common refinement of the local models; Tags 03D8,
06YY and 08TC for ordinary restriction and completion
(blueprint: lem-fix-clopen-projective-chart-common-refinement).

Proof: each finite disjoint open cover is clopen, because the complement of one
member is the finite union of the others. Intersect the two covers and enumerate
the product of their finite index sets by Fin c. The intersections are clopen in
an affine scheme, hence qcqs; their pairwise disjointness and covering follow from
those of the original covers. On each intersection use the normalized clopen
coefficient identification to restrict the corresponding complex. This exact
module functor carries zero terms to zero, identifies the unit sheaf with the
unit sheaf, and preserves finite products (equivalently finite sums). Apply it
to the specified inclusion and retraction; functoriality preserves their composite
identity. The bounded projective complex is K-flat. Its ordinary derived
restriction is therefore this termwise restriction. A clopen restriction preserves
the entire quotient tower and its augmented Roos triangle, hence preserves
completeness; the ordinary-to-completed comparison is consequently invertible
on each given complete complex. Transport the given completed chart isomorphism
through this comparison. Finally the ordinary derived pullback compositor
identifies iterated restriction with pullback along the displayed composite to W.
Empty members, zero complexes, and empty schemes satisfy the same construction. -/
theorem clopen_projective_chart_common_refinement
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : Scheme.{u}) (f : V ⟶ W) [IsAffine V]
    (M N : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (_hcomplete : ∀ K : DerivedCategory (scalarReductionSource.{u, u} l E W),
      K = M ∨ K = N → IntegralOnSlice.IsComplete l E V none
        ((ordinaryIntegralDerivedPull l E f).obj K))
    (_hmodels : ∀ K : DerivedCategory (scalarReductionSource.{u, u} l E W),
      K = M ∨ K = N →
    ∃ (n : ℕ) (U : Fin n → V.Opens),
      (⨆ i, U i) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        ∃ (P : CochainComplex (integralTowerModules.{u, u} l E (U i).toScheme) ℤ)
          (a b : ℤ),
          a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ r : ℤ, ∃ (N : ℕ)
            (ι : P.X r ⟶ ∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
            (ρ : (∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
              ⟶ P.X r),
            ι ≫ ρ = 𝟙 _) ∧
          Nonempty
            ((integralDerivedPullback l E (U i).ι).obj ((ordinaryIntegralDerivedPull l E f).obj K) ≅
              DerivedCategory.Q.obj P)) :
          ∃ (c : ℕ) (U : Fin c → V.Opens),
            (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
            (∀ i, CompactSpace (U i).toScheme) ∧
            (∀ i, QuasiSeparatedSpace (U i).toScheme) ∧
            ∀ (i : Fin c) (K : DerivedCategory (scalarReductionSource.{u, u} l E W)),
              K = M ∨ K = N →
              ∃ (P : CochainComplex (scalarReductionSource.{u, u} l E (U i).toScheme) ℤ)
                (a b : ℤ), a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
                (∀ q : ℤ, ∃ (r : ℕ)
                  (ι : P.X q ⟶ ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
                  (ρ : (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
                    ⟶ P.X q), ι ≫ ρ = 𝟙 _) ∧
                Nonempty ((ordinaryIntegralDerivedPull l E
                  ((U i).ι ≫ f)).obj K ≅ DerivedCategory.Q.obj P) := by
  classical
  obtain ⟨m, U, hUcover, hUdisjoint, hUmodels⟩ := _hmodels M (Or.inl rfl)
  obtain ⟨n, T, hTcover, hTdisjoint, hTmodels⟩ := _hmodels N (Or.inr rfl)
  let e : Fin (m * n) ≃ Fin m × Fin n := finProdFinEquiv.symm
  let A : Fin (m * n) → V.Opens := fun i ↦ U (e i).1 ⊓ T (e i).2
  have hAclosed (i : Fin (m * n)) : IsClosed (A i : Set V) :=
    (chart_cover_closed U hUcover hUdisjoint (e i).1).inter
      (chart_cover_closed T hTcover hTdisjoint (e i).2)
  refine ⟨m * n, A, ?_, ?_, ?_, ?_, ?_⟩
  · apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, U i from hUcover.symm ▸ hx)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ j, T j from hTcover.symm ▸ hx)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨e.symm (i, j), ?_⟩
    simpa only [A, e.apply_symm_apply, TopologicalSpace.Opens.mem_inf] using And.intro hi hj
  · intro i j hij
    by_cases h : (e i).1 = (e j).1
    · have h' : (e i).2 ≠ (e j).2 := fun h' ↦ hij (e.injective (Prod.ext h h'))
      exact (hTdisjoint h').mono inf_le_right inf_le_right
    · exact (hUdisjoint h).mono inf_le_left inf_le_left
  · intro i
    exact isCompact_iff_compactSpace.mp (hAclosed i).isCompact
  · intro i
    exact (A i).isOpenEmbedding.quasiSeparatedSpace
  · intro i K hK
    have local_model (B : V.Opens) (hB : IsClosed (B : Set V)) (hAB : A i ≤ B)
        (P : CochainComplex (integralTowerModules.{u, u} l E B.toScheme) ℤ)
        (a b : ℤ) (hab : a ≤ b) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
        (hsplit : ∀ q : ℤ, ∃ (r : ℕ)
          (ι : P.X q ⟶ ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E B.toScheme))
          (ρ : (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E B.toScheme)) ⟶ P.X q),
          ι ≫ ρ = 𝟙 _)
        (hP : Nonempty ((integralDerivedPullback l E B.ι).obj
          ((ordinaryIntegralDerivedPull l E f).obj K) ≅ DerivedCategory.Q.obj P)) :
        ∃ (Q : CochainComplex (scalarReductionSource.{u, u} l E (A i).toScheme) ℤ)
          (a b : ℤ), a ≤ b ∧ Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
          (∀ q : ℤ, ∃ (r : ℕ)
            (ι : Q.X q ⟶ ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E (A i).toScheme))
            (ρ : (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E (A i).toScheme)) ⟶ Q.X q),
            ι ≫ ρ = 𝟙 _) ∧
          Nonempty ((ordinaryIntegralDerivedPull l E ((A i).ι ≫ f)).obj K ≅
            DerivedCategory.Q.obj Q) := by
      let j := V.homOfLE hAB
      let F : scalarReductionSource.{u, u} l E B.toScheme ⥤
          scalarReductionSource.{u, u} l E (A i).toScheme :=
        OpenCompletedRestriction.ordinary l E j
      have : F.Additive := OpenCompletedRestriction.ordinaryAdditive l E j
      have : PreservesFiniteLimits F := OpenCompletedRestriction.ordinaryLimits l E j
      have : PreservesFiniteColimits F := OpenCompletedRestriction.ordinaryColimits l E j
      let c := (sheafCompose (Scheme.ProEt.topology (A i).toScheme)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
          (OpenCompletedRestriction.coefficients l E j).completed
      have := chart_pushforward_unit_isIso c.hom
      let eunit : F.obj (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E B.toScheme)) ≅
          SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (A i).toScheme) :=
        (asIso (SheafOfModules.unitToPushforwardObjUnit c.hom)).symm
      have : P.IsStrictlyGE a := ha
      have : P.IsStrictlyLE b := hb
      let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
      refine ⟨Q, a, b, hab, inferInstance, inferInstance, ?_, ?_⟩
      · intro q
        exact chart_map_retract F eunit (P.X q) (hsplit q)
      · obtain ⟨eF⟩ := clopen_completed_restriction_comparison l E W V f B (A i)
          hB (hAclosed i) hAB K (_hcomplete K hK)
        obtain ⟨eP⟩ := hP
        exact ⟨eF ≪≫ F.mapDerivedCategory.mapIso eP ≪≫ F.mapDerivedCategoryFactors.app P⟩
    rcases hK with rfl | rfl
    · obtain ⟨P, a, b, hab, ha, hb, hsplit, hP⟩ := hUmodels (e i).1
      exact local_model _ (chart_cover_closed U hUcover hUdisjoint _) inf_le_left
        P a b hab ha hb hsplit hP
    · obtain ⟨P, a, b, hab, ha, hb, hsplit, hP⟩ := hTmodels (e i).2
      exact local_model _ (chart_cover_closed T hTcover hTdisjoint _) inf_le_right
        P a b hab ha hb hsplit hP

end WeilConjectures
