/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
import all WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.SixFunctors.SchemeRefinementTree
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.SixFunctors.Constructible.ConstructibleResidueTree
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralReductionHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import WeilConjectures.SixFunctors.GeneratorReduction.AffineConstructibleRestrictionComplete

/-! # Residue-lisse refinement over an affine open

Source: Bhatt--Scholze, Lemmas 6.5.5--6.5.8; Stacks Tags 09Y4 and 09C3.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

private theorem forget_tree {W T : Scheme.{u}} {t : T ⟶ W}
    {allowed : ∀ (Y : Scheme.{u}), (Y ⟶ W) → ∀ (A B : Scheme.{u}),
      (A ⟶ Y) → (B ⟶ Y) → Prop}
    {P : ∀ (Y : Scheme.{u}), (Y ⟶ W) → Prop}
    (tree : SchemeRefinementTree W allowed T t) (htree : tree.AllLeaves P) :
    ∃ q : QcqsOpenClosedTree T,
      ∀ (S : Scheme.{u}) (p : q.Path S), p.IsLeaf → P S (p.toRoot ≫ t) := by
  induction tree with
  | tip t hc hq hi =>
    let := hc
    let := hq
    refine ⟨.leaf _, ?_⟩
    intro S p hp
    cases p with
    | root => simpa only [SchemeRefinementTree.AllLeaves,
        QcqsOpenClosedTree.Path.toRoot, Category.id_comp] using htree
  | @node T A B t j i hc hq hi hj hi' hjqc hiqc hcov hdis ha a b iha ihb =>
    let := hc
    let := hq
    let := hj
    let := hi'
    let := hjqc
    let := hiqc
    obtain ⟨qa, hqa⟩ := iha htree.1
    obtain ⟨qb, hqb⟩ := ihb htree.2
    have hcomp : Set.range j.base = (Set.range i.base)ᶜ := by
      ext x
      constructor
      · intro hx hx'
        exact Set.disjoint_left.mp hdis hx hx'
      · intro hx
        have hx' : x ∈ Set.range j.base ∪ Set.range i.base := by rw [hcov]; trivial
        exact hx'.resolve_right hx
    refine ⟨.split j i hcomp qa qb, ?_⟩
    intro S p hp
    cases p with
    | root => exact hp.elim
    | openBranch _ _ _ _ _ p =>
      simpa only [QcqsOpenClosedTree.Path.toRoot, Category.assoc] using hqa S p hp
    | closedBranch _ _ _ _ _ p =>
      simpa only [QcqsOpenClosedTree.Path.toRoot, Category.assoc] using hqb S p hp

private theorem partition_tree
    {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (m : ℕ) (n : Fin m → ℕ)
    (S : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (s : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ W)
    (hs : ∀ a j, IsImmersion (s a j))
    (hc : ∀ a j, Topology.IsConstructible (Set.range (s a j).base))
    (hcover : ∀ a : Fin m, (⋃ j, Set.range (s a j).base) = Set.univ) :
    ∃ tree : QcqsOpenClosedTree W,
      ∀ (T : Scheme.{u}) (p : tree.Path T), p.IsLeaf → Nonempty T →
        ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j,
          f ≫ s a j = p.toRoot := by
  classical
  choose O Q Z o c q z ho hclosed hq hz hco hoqc hqqc hqr hzr using
    fun (a : Fin m) (j : Fin (n a)) ↦
      exists_constructible_cut (W := W) (S := S a j) (s a j) (hc a j)
  let allowed := fun (T : Scheme.{u}) (_ : T ⟶ W) (L R : Scheme.{u})
      (_ : L ⟶ T) (_ : R ⟶ T) ↦ True
  let resolved := fun (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W) ↦
    Disjoint (Set.range t.base) (Set.range (s k.1 k.2).base) ∨
      ∃ f : T ⟶ S k.1 k.2, f ≫ s k.1 k.2 = t
  have resolved_comp (k : (a : Fin m) × Fin (n a))
      {T R : Scheme.{u}} (t : T ⟶ W) (r : R ⟶ T)
      (ht : resolved k T t) : resolved k R (r ≫ t) := by
    rcases ht with ht | ⟨f, hf⟩
    · left
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      exact Set.disjoint_left.mp ht ⟨r y, rfl⟩ hx
    · exact Or.inr ⟨r ≫ f, by rw [Category.assoc, hf]⟩
  have step (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W)
      (hcompact : CompactSpace T) (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t) :
      ∃ tree : SchemeRefinementTree W allowed T t,
        tree.AllLeaves (fun R r ↦
          (∃ p : R ⟶ T, p ≫ t = r) ∧ resolved k R r) := by
    let :=  hcompact
    let :=  hqs
    let :=  himm
    let a := k.1
    let j := k.2
    have :=  ho a j
    have :=  hclosed a j
    have :=  hq a j
    have :=  hz a j
    have :=  hoqc a j
    have :=  hqqc a j
    let A := pullback t (o a j)
    let D := pullback t (z a j)
    let p : A ⟶ T := pullback.fst t (o a j)
    let d : D ⟶ T := pullback.fst t (z a j)
    let f : A ⟶ O a j := pullback.snd t (o a j)
    let B := pullback f (q a j)
    let C := pullback f (c a j)
    let b : B ⟶ A := pullback.fst f (q a j)
    let c' : C ⟶ A := pullback.fst f (c a j)
    have : CompactSpace A := inferInstance
    have : CompactSpace D := inferInstance
    have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
    have : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated d
    have : CompactSpace B := inferInstance
    have : CompactSpace C := inferInstance
    have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated b
    have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c'
    have hfc : f ≫ o a j = p ≫ t := (pullback.condition (f := t) (g := o a j)).symm
    have hqr' : Set.range (q a j).base = (Set.range (c a j).base)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩ ⟨v, hv⟩
        have hy : o a j (q a j y) ∈ Set.range (q a j ≫ o a j).base := ⟨y, rfl⟩
        rw [hqr a j] at hy
        apply hy.2
        refine ⟨v, ?_⟩
        rw [← hco a j]
        exact congrArg (o a j) hv
      · intro hx
        have hxW : o a j x ∈ Set.range (q a j ≫ o a j).base := by
          rw [hqr a j]
          refine ⟨⟨x, rfl⟩, ?_⟩
          rintro ⟨v, hv⟩
          apply hx
          refine ⟨v, (o a j).isEmbedding.injective ?_⟩
          simpa only [← hco a j, Scheme.Hom.comp_apply] using hv
        obtain ⟨y, hy⟩ := hxW
        exact ⟨y, (o a j).isEmbedding.injective hy⟩
    have houter : Set.range p.base ∪ Set.range d.base = Set.univ ∧
        Disjoint (Set.range p.base) (Set.range d.base) := by
      change Set.range (pullback.fst t (o a j)).base ∪
          Set.range (pullback.fst t (z a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst t (o a j)).base)
          (Set.range (pullback.fst t (z a j)).base)
      simp only [Scheme.Pullback.range_fst, hzr, Set.preimage_compl]
      exact ⟨Set.union_compl_self _, disjoint_compl_right⟩
    have hinner : Set.range b.base ∪ Set.range c'.base = Set.univ ∧
        Disjoint (Set.range b.base) (Set.range c'.base) := by
      change Set.range (pullback.fst f (q a j)).base ∪
          Set.range (pullback.fst f (c a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst f (q a j)).base)
          (Set.range (pullback.fst f (c a j)).base)
      simp only [Scheme.Pullback.range_fst, hqr', Set.preimage_compl]
      exact ⟨Set.compl_union_self _, disjoint_compl_left⟩
    refine ⟨.node t p d inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance houter.1 houter.2
      trivial
      (.node (p ≫ t) b c' inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hinner.1 hinner.2
        trivial
        (.tip _ inferInstance inferInstance inferInstance)
        (.tip _ inferInstance inferInstance inferInstance))
      (.tip _ inferInstance inferInstance inferInstance), ?_⟩
    change ((_ ∧ resolved k B (b ≫ p ≫ t)) ∧
      (_ ∧ resolved k C (c' ≫ p ≫ t))) ∧ (_ ∧ resolved k D (d ≫ t))
    refine ⟨⟨⟨⟨b ≫ p, (Category.assoc ..)⟩, ?_⟩,
      ⟨⟨c' ≫ p, (Category.assoc ..)⟩, ?_⟩⟩, ⟨⟨d, rfl⟩, ?_⟩⟩
    · left
      have hb : b ≫ p ≫ t = pullback.snd f (q a j) ≫ q a j ≫ o a j := by
        change pullback.fst f (q a j) ≫ p ≫ t = _
        rw [← hfc, ← Category.assoc, pullback.condition, Category.assoc]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      have hy : (b ≫ p ≫ t) y ∈ Set.range (q a j ≫ o a j).base := by
        rw [hb]
        exact ⟨pullback.snd f (q a j) y, rfl⟩
      rw [hqr a j] at hy
      exact hy.2 hx
    · right
      refine ⟨pullback.snd f (c a j), ?_⟩
      change pullback.snd f (c a j) ≫ s a j = c' ≫ p ≫ t
      rw [← hco a j, ← Category.assoc, ← pullback.condition, Category.assoc, hfc]
    · left
      have hd : Set.range (d ≫ t).base =
          Set.range t.base ∩ (Set.range (o a j).base)ᶜ := by
        change Set.range (pullback.fst t (z a j) ≫ t).base = _
        rw [Scheme.Pullback.range_fst_comp, hzr a j]
      apply Set.disjoint_left.mpr
      intro x hx hxS
      have hxO := (hd ▸ hx).2
      obtain ⟨v, rfl⟩ := hxS
      apply hxO
      refine ⟨c a j v, ?_⟩
      exact congrArg (fun g : S a j ⟶ W ↦ g v) (hco a j)
  have build (K : Finset ((a : Fin m) × Fin (n a))) :
      ∃ tree : SchemeRefinementTree W allowed W (𝟙 W),
        tree.AllLeaves (fun T t ↦ ∀ k ∈ K, resolved k T t) := by
    induction K using Finset.induction_on with
    | empty =>
      exact ⟨.tip _ inferInstance inferInstance inferInstance, by simp [
        SchemeRefinementTree.AllLeaves]⟩
    | @insert k K hk ih =>
      obtain ⟨tree, htree⟩ := ih
      choose replacement hreplacement using step k
      refine ⟨tree.bind replacement, SchemeRefinementTree.allLeaves_bind replacement ?_ tree
        htree⟩
      intro T t hcompact hqs himm hprocessed
      apply SchemeRefinementTree.allLeaves_mono _ (replacement T t hcompact hqs himm)
        (hreplacement T t hcompact hqs himm)
      rintro R r ⟨⟨p, hp⟩, hnew⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hnew
      · rw [← hp]
        exact resolved_comp i t p (hprocessed i hi)
  obtain ⟨tree, htree⟩ := build Finset.univ
  have hleaf : tree.AllLeaves (fun T t ↦ Nonempty T →
      ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j, f ≫ s a j = t) := by
    apply SchemeRefinementTree.allLeaves_mono _ tree htree
    intro T t ht hT a
    obtain ⟨x⟩ := hT
    have hx : t x ∈ ⋃ j : Fin (n a), Set.range (s a j).base := by
      rw [hcover a]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases ht ⟨a, j⟩ (Finset.mem_univ _) with havoid | hfactor
    · exact False.elim (Set.disjoint_left.mp havoid ⟨x, rfl⟩ hj)
    · exact ⟨j, hfactor⟩
  obtain ⟨qtree, hqtree⟩ := forget_tree tree hleaf
  refine ⟨qtree, ?_⟩
  intro T p hp hn a
  simpa only [Category.comp_id] using hqtree T p hp hn a

/-- Simultaneous residue-lisse stratification of two integral constructible inputs.
There is no assertion of a projective model, a finite chart family, or a tensor product.

Source: Bhatt--Scholze, Lemmas 6.5.5--6.5.8; Stacks Tags 09Y4 and 09C3.
(blueprint: lem-sf-affine-residue-lisse-tree).

Proof: restriction to the affine open is the exact over-site restriction and preserves
products, hence the augmented quotient/Roos triangle and derived completeness. Its
finite reductions are exact constant-coefficient restrictions, with the original common
cohomology interval. Choose the constructible stratification of each residue cohomology
sheaf in each of the two finite intervals. Refine this finite family of partitions by
successive quasi-compact open/complementary closed cuts, using Tag 09Y4. Build the recursive
binary pullback tree and forget its ambient structural maps to obtain the actual tree,
retaining the factorization of each leaf through every original partition. Each nonempty leaf
factors through one stratum of every chosen partition. Ordinary restriction through
these constructible cuts preserves the completed coefficient ring and completeness.
The same holds on every qcqs weakly etale object of a leaf. Exact residue pullback
commutes with cohomology, preserves the cohomology interval, and pulls the finite
constant models on the chosen stratum to finite constant models on the object.
Outside the interval use the zero model. The empty leaf imposes no condition.
No invertibility assumption on ell is involved in any of these site-local steps. -/
theorem affineResidueLisseTree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K L : IntegralOnSlice.D.{u, u} l E X none)
    (hK : sfIntegralConstructible l E X K)
    (hL : sfIntegralConstructible l E X L)
    (U : X.Opens) [IsAffine U.toScheme] :
    ∃ tree : QcqsOpenClosedTree U.toScheme,
      ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
        ∀ (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
          (r : V ⟶ S) [WeaklyEtale r]
          (M : IntegralOnSlice.D.{u, u} l E X none), M = K ∨ M = L →
          IntegralOnSlice.IsComplete l E V none
            ((ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj M) ∧
          ∃ a b : ℤ, a ≤ b ∧
            (∀ q : ℤ, q < a ∨ b < q → IsZero
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E V 0).obj
                  ((ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj M)))) ∧
            (∀ q : ℤ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
              (Padic.coefficientExtensionRing l E 1)
              (fun N ↦ Module.Finite (ULift.{u + 1}
                (Padic.coefficientExtensionRing l E 1)) N)
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E V 0).obj
                  ((ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj M)))) := by
  classical
  let A := Padic.coefficientExtensionRing l E 1
  have : Finite A := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  obtain ⟨hKc, aM, bM, habM, hM⟩ := hK
  obtain ⟨hLc, aN, bN, habN, hN⟩ := hL
  let a := min aM aN
  let b := max bM bN
  have hab : a ≤ b := (min_le_left _ _).trans (habM.trans (le_max_left _ _))
  let C (c : Bool) := if c then K else L
  let H (c : Bool) (q : ℤ) := (DerivedCategory.homologyFunctor _ q).obj
    ((scalarReductionDerivedExtension l E X 0).obj (C c))
  have hconstruct (c : Bool) (q : ℤ) : IsConstructibleProEtaleModuleSheaf X A (H c q) := by
    cases c
    · exact (hN 0).1.2 q
    · exact (hM 0).1.2 q
  have hzero (c : Bool) (q : ℤ) (hq : q < a ∨ b < q) : IsZero (H c q) := by
    by_contra hn
    cases c
    · have hq' := (hN 0).2 hn
      dsimp only [a, b] at hq
      rcases hq with hq | hq <;> have := min_le_right aM aN <;>
        have := le_max_right bM bN <;> obtain ⟨_, _⟩ := hq' <;> omega
    · have hq' := (hM 0).2 hn
      dsimp only [a, b] at hq
      rcases hq with hq | hq <;> have := min_le_left aM aN <;>
        have := le_max_left bM bN <;> obtain ⟨_, _⟩ := hq' <;> omega
  let J := Bool × ↥(Finset.Icc a b)
  have hstrat (j : J) : ∃ Z : Stratification X, 0 < Z.n ∧
      ∀ k : Fin Z.n,
        IsLocallyConstantProEtaleModuleSheaf (Z.domain k) A
          (proEtaleConstantModulePullback (Z.immersion k) A (H j.1 j.2)) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Z.domain k),
          Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing (Z.domain k) A)
            (proEtaleConstantModulePullback (Z.immersion k) A (H j.1 j.2))) :=
    hconstruct j.1 j.2
  let Z (j : J) := (hstrat j).choose
  have hmodels (j : J) (k : Fin (Z j).n) :
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses ((Z j).domain k) A
        (fun L ↦ Module.Finite (ULift.{u + 1} A) L)
        (proEtaleConstantModulePullback ((Z j).immersion k) A (H j.1 j.2)) :=
    finiteModels_of_lisse_stalks _ A _ ((hstrat j).choose_spec.2 k).1
      ((hstrat j).choose_spec.2 k).2
  let Z' (j : J) := (Z j).pullback U.ι
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  obtain ⟨tree, htree⟩ := partition_tree (Fintype.card J)
    (fun j ↦ (Z' (e j)).n) (fun j ↦ (Z' (e j)).domain)
    (fun j ↦ (Z' (e j)).immersion)
    (fun j k ↦ (Z' (e j)).isImmersion k)
    (fun j k ↦ by
      rw [(Z' (e j)).range_immersion k]
      exact (Z' (e j)).isConstructible_stratum k)
    (fun j ↦ by
      simpa only [(Z' (e j)).range_immersion] using (Z' (e j)).iUnion_stratum_eq_univ)
  have factors (S : Scheme.{u}) (p : tree.Path S) (hp : p.IsLeaf)
      (hn : Nonempty S) (j : J) :
      ∃ k : Fin (Z' j).n, ∃ f : S ⟶ (Z' j).domain k,
        f ≫ (Z' j).immersion k = p.toRoot := by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact htree S p hp hn j'
  refine ⟨tree, ?_⟩
  intro S p hp hn V _ _ r _ M hM
  have complete : IntegralOnSlice.IsComplete l E V none
      ((ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj M) := by
    apply affineConstructibleRestrictionComplete l E X M _ U tree p V r
    rcases hM with rfl | rfl
    · exact hKc
    · exact hLc
  refine ⟨complete, a, b, hab, ?_, ?_⟩
  · intro t ht
    obtain ⟨β⟩ := ordinaryIntegralReductionHomology l E (r ≫ p.toRoot ≫ U.ι) M 0 t
    have hz : IsZero ((DerivedCategory.homologyFunctor _ t).obj
        ((scalarReductionDerivedExtension l E X 0).obj M)) := by
      rcases hM with rfl | rfl
      · exact hzero true t ht
      · exact hzero false t ht
    have hpull :=
      (proEtaleConstantModulePullbackFunctor (r ≫ p.toRoot ≫ U.ι) A).map_isZero hz
    exact hpull.of_iso β
  · intro t
    obtain ⟨β⟩ := ordinaryIntegralReductionHomology l E (r ≫ p.toRoot ≫ U.ι) M 0 t
    apply finiteModels_iso V A β.symm
    by_cases ht : t ∈ Finset.Icc a b
    · let c : Bool := if M = K then true else false
      have hMc : M = C c := by
        rcases hM with h | h
        · simp [c, h, C]
        · by_cases hLK : L = K
          · simp [c, h, hLK, C]
          · simp [c, h, hLK, C]
      let j : J := (c, ⟨t, ht⟩)
      obtain ⟨k, f, hf⟩ := factors S p hp hn j
      let g : S ⟶ (Z j).domain k := f ≫ pullback.fst ((Z j).immersion k) U.ι
      have hg : g ≫ (Z j).immersion k = p.toRoot ≫ U.ι := by
        dsimp only [g]
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (fun h ↦ h ≫ U.ι) hf
      have hfin := finiteModels_pull (r ≫ g) A _ (hmodels j k)
      obtain ⟨α, _⟩ := proEtaleConstantRingModulePullbackComposition
        (r ≫ g) ((Z j).immersion k) A
      have heq : (r ≫ g) ≫ (Z j).immersion k = r ≫ p.toRoot ≫ U.ι := by
        rw [Category.assoc, hg]
      let γ : proEtaleConstantModulePullback (r ≫ p.toRoot ≫ U.ι) A (H c t) ≅
          proEtaleConstantModulePullback (r ≫ g) A
            (proEtaleConstantModulePullback ((Z j).immersion k) A (H c t)) :=
        eqToIso (congrArg (fun h ↦ proEtaleConstantModulePullback h A (H c t)) heq.symm)
          ≪≫ α.app (H c t)
      rw [hMc]
      exact finiteModels_iso V A γ.symm hfin
    · have hout : t < a ∨ b < t := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at ht
        exact ht
      have hz : IsZero ((DerivedCategory.homologyFunctor _ t).obj
          ((scalarReductionDerivedExtension l E X 0).obj M)) := by
        rcases hM with rfl | rfl
        · exact hzero true t hout
        · exact hzero false t hout
      exact finiteModels_zero V A _
        ((proEtaleConstantModulePullbackFunctor (r ≫ p.toRoot ≫ U.ι) A).map_isZero hz)

end WeilConjectures.GeneratorReduction
