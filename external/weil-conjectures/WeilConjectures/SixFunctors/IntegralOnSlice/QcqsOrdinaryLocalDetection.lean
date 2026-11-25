/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionModels
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryCompletedPullCoherence
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryCompletedOpenClosedDetection
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryCompletedCoverDetection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Local detection for ordinary derived restriction

Source: Stacks Tags 09AH, 09BM, 04TQ and 05RT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

attribute [local irreducible] ordinaryPull ordinaryDerivedPull

private theorem ordinaryExactImmersion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (r : X ⟶ Y) [IsImmersion r] :
    PreservesFiniteLimits (ordinaryPull l E r) ∧
      PreservesFiniteColimits (ordinaryPull l E r) := by
  have h := qcqsOrdinaryRestrictionModels l E (𝟙 X) r
  simp only [Category.id_comp] at h
  exact ⟨h.1, h.2.1⟩

private theorem ordinaryExactChart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (r : X ⟶ Y) [WeaklyEtale r] :
    PreservesFiniteLimits (ordinaryPull l E r) ∧
      PreservesFiniteColimits (ordinaryPull l E r) := by
  have h := qcqsOrdinaryRestrictionModels l E r (𝟙 Y)
  simp only [Category.comp_id] at h
  exact ⟨h.1, h.2.1⟩

private def ordinaryExactComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (r : X ⟶ Y)
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)] :
    ordinaryDerivedPull l E r ≅ (ordinaryPull l E r).mapDerivedCategory := by
  let F := (ordinaryPull l E r).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ))
    (ordinaryPull l E r).mapDerivedCategory (ordinaryPull l E r).mapDerivedCategoryFactorsh
  unfold ordinaryDerivedPull
  exact Functor.leftDerivedUnique (ordinaryPull l E r).mapDerivedCategory
    (F.totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ)))
    (F.totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ)))
    (ordinaryPull l E r).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (Mod l E Y none) (.up ℤ))

private theorem ordinaryExactComp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{t}} (s : X ⟶ Y) (r : Y ⟶ Z)
    [PreservesFiniteLimits (ordinaryPull l E s)]
    [PreservesFiniteColimits (ordinaryPull l E s)]
    [PreservesFiniteLimits (ordinaryPull l E r)]
    [PreservesFiniteColimits (ordinaryPull l E r)]
    [PreservesFiniteLimits (ordinaryPull l E (s ≫ r))]
    [PreservesFiniteColimits (ordinaryPull l E (s ≫ r))] :
    Nonempty (ordinaryDerivedPull l E (s ≫ r) ≅
      ordinaryDerivedPull l E r ⋙ ordinaryDerivedPull l E s) := by
  obtain ⟨c⟩ := (ordinaryCompletedPullCoherence l E).2 s r
  let := comp_preservesFiniteLimits (ordinaryPull l E r) (ordinaryPull l E s)
  let := comp_preservesFiniteColimits (ordinaryPull l E r) (ordinaryPull l E s)
  exact ⟨ordinaryExactComparison l E (s ≫ r) ≪≫
    Functor.mapDerivedCategoryNatIso c ≪≫
    (Functor.mapDerivedCategoryCompIso (ordinaryPull l E r) (ordinaryPull l E s)).symm ≪≫
    Functor.isoWhiskerRight (ordinaryExactComparison l E r).symm _ ≪≫
    Functor.isoWhiskerLeft _ (ordinaryExactComparison l E s).symm⟩

private theorem ordinaryExactJoint
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} {B : I → Type*} [∀ i, Category (B i)] [∀ i, Abelian (B i)]
    [∀ i, HasDerivedCategory (B i)]
    (F : ∀ i, A ⥤ B i) [∀ i, (F i).Additive]
    [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
    (hF : JointlyReflectIsomorphisms F)
    {H K : DerivedCategory A} (f : H ⟶ K)
    (h : ∀ i, IsIso ((F i).mapDerivedCategory.map f)) : IsIso f := by
  let := h
  exact (Functor.jointlyReflectIsomorphisms_mapDerivedCategory hF).isIso f

/-- Ordinary derived restriction is conservative on an isomorphic scheme,
jointly conservative for an open--closed pair, and conservative on a covering family.
These are tests for arbitrary derived morphisms.

Source: Stacks Tags 09AH, 09BM, 04TQ and 05RT
(blueprint: lem-fix-qcqs-ordinary-local-detection).
Proof: ordinary module pullbacks respect identity and composition by uniqueness
of their ringed adjunctions. The stated ordinary restriction model theorem gives
exactness for immersions, weakly etale charts, and their composites. Exactness
identifies the chosen left derived pullbacks with mapDerivedCategory; these
comparisons and exact derived composition give the required composite arrows.
An isomorphism of schemes gives mutually inverse restrictions.
For an open--closed pair use joint reflection for ordinary module restrictions.
For a cover use joint reflection for ordinary module restrictions to its charts.
In each case the existing theorem for a jointly reflecting family of exact functors
passes reflection to the unbounded derived categories: exact restriction commutes
with every cohomology sheaf, and isomorphisms are detected on all cohomology.
Transport through the composition comparisons proves the criteria as stated. -/
theorem qcqsOrdinaryLocalDetection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    {H K : D l E T none} (f : H ⟶ K) :
    (∀ (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S]
      (r : S ⟶ T) [IsIso r],
      IsIso ((ordinaryDerivedPull l E r).map f) ↔ IsIso f) ∧
    (∀ (S U Z : Scheme.{t})
      [CompactSpace S] [QuasiSeparatedSpace S]
      [CompactSpace U] [QuasiSeparatedSpace U]
      [CompactSpace Z] [QuasiSeparatedSpace Z]
      (r : S ⟶ T) [IsImmersion r] (j : U ⟶ S) (i : Z ⟶ S)
      [IsOpenImmersion j] [QuasiCompact j] [IsClosedImmersion i],
      Set.range j.base ∪ Set.range i.base = Set.univ →
      Disjoint (Set.range j.base) (Set.range i.base) →
      (IsIso ((ordinaryDerivedPull l E r).map f) ↔
        IsIso ((ordinaryDerivedPull l E (j ≫ r)).map f) ∧
          IsIso ((ordinaryDerivedPull l E (i ≫ r)).map f))) ∧
    (∀ (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S]
      (r : S ⟶ T) [IsImmersion r] [Nonempty S]
      (I : Type w) (W : I → S.ProEt),
      (∀ a : I, CompactSpace (W a).left) →
      (∀ a : I, QuasiSeparatedSpace (W a).left) →
      Presieve.ofArrows W
        (fun a ↦ (MorphismProperty.Over.homMk (W a).hom (Category.comp_id _) :
          W a ⟶ ProEt.mk (𝟙 S))) ∈ ProEt.precoverage S (ProEt.mk (𝟙 S)) →
      (IsIso ((ordinaryDerivedPull l E r).map f) ↔
        ∀ a : I, IsIso ((ordinaryDerivedPull l E ((W a).hom ≫ r)).map f))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S _ _ r _
    obtain ⟨hrl, hrc⟩ := ordinaryExactImmersion l E r
    obtain ⟨hil, hic⟩ := ordinaryExactImmersion l E (inv r)
    obtain ⟨hdl, hdc⟩ := ordinaryExactImmersion l E (𝟙 T)
    obtain ⟨c⟩ := (ordinaryCompletedPullCoherence l E).1 T
    let idIso : ordinaryDerivedPull l E (𝟙 T) ≅ 𝟭 (D l E T none) :=
      ordinaryExactComparison l E (𝟙 T) ≪≫ Functor.mapDerivedCategoryNatIso c ≪≫
        Functor.mapDerivedCategoryIdIso _
    have hcomp : inv r ≫ r = 𝟙 T := IsIso.inv_hom_id r
    have hlim : PreservesFiniteLimits (ordinaryPull l E (inv r ≫ r)) := by
      rw [hcomp]
      exact hdl
    have hcol : PreservesFiniteColimits (ordinaryPull l E (inv r ≫ r)) := by
      rw [hcomp]
      exact hdc
    obtain ⟨cr⟩ := ordinaryExactComp l E (inv r) r
    let e : ordinaryDerivedPull l E r ⋙ ordinaryDerivedPull l E (inv r) ≅
        𝟭 (D l E T none) :=
      cr.symm ≪≫
        eqToIso (congrArg (ordinaryDerivedPull l E) hcomp) ≪≫ idIso
    constructor
    · intro h
      let := h
      exact (NatIso.isIso_map_iff e f).mp (by
        change IsIso ((ordinaryDerivedPull l E (inv r)).map
          ((ordinaryDerivedPull l E r).map f))
        infer_instance)
    · intro h
      let := h
      infer_instance
  · intro S U Z _ _ _ _ _ _ r _ j i _ _ _ hcover hdisj
    obtain ⟨hrl, hrc⟩ := ordinaryExactImmersion l E r
    obtain ⟨hjl, hjc⟩ := ordinaryExactImmersion l E j
    obtain ⟨hil, hic⟩ := ordinaryExactImmersion l E i
    obtain ⟨hjrl, hjrc⟩ := ordinaryExactImmersion l E (j ≫ r)
    obtain ⟨hirl, hirc⟩ := ordinaryExactImmersion l E (i ≫ r)
    let g := (ordinaryDerivedPull l E r).map f
    obtain ⟨cjr⟩ := ordinaryExactComp l E j r
    obtain ⟨cir⟩ := ordinaryExactComp l E i r
    have hj : IsIso ((ordinaryDerivedPull l E (j ≫ r)).map f) ↔
        IsIso ((ordinaryPull l E j).mapDerivedCategory.map g) :=
      (NatIso.isIso_map_iff cjr f).trans
        (NatIso.isIso_map_iff (ordinaryExactComparison l E j) g)
    have hi : IsIso ((ordinaryDerivedPull l E (i ≫ r)).map f) ↔
        IsIso ((ordinaryPull l E i).mapDerivedCategory.map g) :=
      (NatIso.isIso_map_iff cir f).trans
        (NatIso.isIso_map_iff (ordinaryExactComparison l E i) g)
    rw [hj, hi]
    constructor
    · intro h
      let := h
      constructor <;> infer_instance
    · rintro ⟨hjg, hig⟩
      let := hjg
      let := hig
      have hc := jointlyReflectIsomorphisms_pairFunctor
        (ordinaryPull l E j) (ordinaryPull l E i)
        (fun {_ _} f hj hi ↦
          ordinaryCompletedOpenClosedDetection l E S U Z j i hcover hdisj f hj hi)
      exact (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory
        _ _ hc).isIso_of_pairFunctor g hjg hig
  · intro S _ _ r _ _ I W hcompact hqs hcover
    obtain ⟨hrl, hrc⟩ := ordinaryExactImmersion l E r
    have hwl (a : I) : PreservesFiniteLimits (ordinaryPull l E (W a).hom) :=
      by
        let : CompactSpace (W a).left := hcompact a
        let : QuasiSeparatedSpace (W a).left := hqs a
        exact (ordinaryExactChart l E (X := (W a).left) (Y := S) (W a).hom).1
    have hwc (a : I) : PreservesFiniteColimits (ordinaryPull l E (W a).hom) :=
      by
        let : CompactSpace (W a).left := hcompact a
        let : QuasiSeparatedSpace (W a).left := hqs a
        exact (ordinaryExactChart l E (X := (W a).left) (Y := S) (W a).hom).2
    have hwrl (a : I) :
        PreservesFiniteLimits (ordinaryPull l E ((W a).hom ≫ r)) :=
      by
        let : CompactSpace (W a).left := hcompact a
        let : QuasiSeparatedSpace (W a).left := hqs a
        exact (qcqsOrdinaryRestrictionModels l E (S := (W a).left) (V := S) (W a).hom r).1
    have hwrc (a : I) :
        PreservesFiniteColimits (ordinaryPull l E ((W a).hom ≫ r)) :=
      by
        let : CompactSpace (W a).left := hcompact a
        let : QuasiSeparatedSpace (W a).left := hqs a
        exact (qcqsOrdinaryRestrictionModels l E (S := (W a).left) (V := S) (W a).hom r).2.1
    let g := (ordinaryDerivedPull l E r).map f
    have hw (a : I) : IsIso ((ordinaryDerivedPull l E ((W a).hom ≫ r)).map f) ↔
        IsIso ((ordinaryPull l E (W a).hom).mapDerivedCategory.map g) := by
      let : CompactSpace (W a).left := hcompact a
      let : QuasiSeparatedSpace (W a).left := hqs a
      let := hwl a
      let := hwc a
      let := hwrl a
      let := hwrc a
      obtain ⟨cwr⟩ := ordinaryExactComp l E (W a).hom r
      exact (NatIso.isIso_map_iff cwr f).trans
        (NatIso.isIso_map_iff (ordinaryExactComparison l E (W a).hom) g)
    constructor
    · intro h a
      let := h
      exact (hw a).mpr (by infer_instance)
    · intro h
      exact ordinaryExactJoint (fun a ↦ ordinaryPull l E (W a).hom)
        (ordinaryCompletedCoverDetection l E S I W hcompact hqs hcover) g
        (fun a ↦ (hw a).mp (h a))

end WeilConjectures.IntegralOnSlice
