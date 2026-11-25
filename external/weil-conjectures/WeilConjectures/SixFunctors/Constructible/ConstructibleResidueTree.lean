/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralReductionHomology
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitRestriction
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition

/-!
# Residue-lisse refinement on qcqs pro-etale objects

Source: Stacks Project, proetale.tex, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-constructible-residue-tree).

All restrictions below are ordinary uncompleted derived ringed pullbacks. Coefficient
index zero is exponent one. Finite products of the unit module are finite direct sums.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open IntegralOnSlice Opposite

attribute [local instance 5000] HasDerivedCategory.standard

private instance residueSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
attribute [local irreducible] HasDerivedCategory.standard
  ordinaryPull
  scalarReductionExistence scalarReductionDerivedExistence

private theorem ordinaryRingMap_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryIntegralDirectRingMap l E f = ordinaryCompletedRingMap.{u, u} l E f := by
  apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
  · exact (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec
  · exact (ordinaryCompletedRingMap_existsUnique l E f).exists.choose_spec

private noncomputable def ordinaryPullIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryIntegralModulePull l E f ≅ ordinaryPull.{u, u} l E f := by
  have h : ordinaryIntegralModulePush l E f = ordinaryPush.{u, u} l E f := by
    unfold ordinaryIntegralModulePush ordinaryPush
    rw [ordinaryRingMap_eq l E f]
  exact (ordinaryIntegralModuleAdjunction l E f).leftAdjointUniq
    ((ordinaryAdjunction.{u, u} l E f).ofNatIsoRight (eqToIso h.symm))

private noncomputable def ordinaryDerivedIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryIntegralDerivedPull l E f ≅ ordinaryDerivedPull.{u, u} l E f := by
  let := ordinaryIntegralModulePull_additive l E f
  let := ordinaryPull_additive.{u, u} l E f
  let a := ordinaryPullIso l E f
  let b : (ordinaryIntegralModulePull l E f).mapHomotopyCategory (.up ℤ) ≅
      (ordinaryPull.{u, u} l E f).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory a.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory a.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, a.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, a.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  let W := HomotopyCategory.quasiIso (integralTowerModules.{u, u} l E Y) (.up ℤ)
  let W' := HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ)
  have hW : W = W' := rfl
  let : (DerivedCategory.Qh (C := IntegralOnSlice.Mod.{u, u} l E Y none)).IsLocalization W := by
    rw [hW]
    exact inferInstanceAs
      ((DerivedCategory.Qh (C := IntegralOnSlice.Mod.{u, u} l E Y none)).IsLocalization
        (HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ)))
  let ε := ordinaryIntegralPullCounit l E f
  let δ := ((ordinaryPull.{u, u} l E f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ))
  let : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor ε W := by
    unfold ordinaryIntegralDerivedPull
    dsimp only [ε, ordinaryIntegralPullCounit, W]
    infer_instance
  let : (ordinaryDerivedPull.{u, u} l E f).IsLeftDerivedFunctor δ W := by
    unfold ordinaryDerivedPull
    let F := (ordinaryPull.{u, u} l E f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
    exact inferInstanceAs
      (Functor.IsLeftDerivedFunctor
        (F.totalLeftDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ)))
          (F.totalLeftDerivedCounit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ)))
          (HomotopyCategory.quasiIso (IntegralOnSlice.Mod.{u, u} l E Y none) (.up ℤ)))
  exact Functor.leftDerivedNatIso _ _ ε δ W
    (Functor.isoWhiskerRight b DerivedCategory.Qh)

private theorem sliceComplete_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {K L : IntegralOnSlice.D.{u, u} l E X none} (e : K ≅ L)
    (hL : IntegralOnSlice.IsComplete.{u, u} l E X none L) :
    IntegralOnSlice.IsComplete.{u, u} l E X none K := by
  have hu := (canonicalCompletionUnitCriterion.{u, u} l E X L).mpr hL
  let := hu
  apply (canonicalCompletionUnitCriterion.{u, u} l E X K).mp
  have h := (completionUnit.{u, u} l E X none).naturality e.hom
  have : IsIso ((completionUnit.{u, u} l E X none).app K ≫
      (completion.{u, u} l E X none).map e.hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((completion.{u, u} l E X none).map e.hom)

private theorem residue_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y V W : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace W] [QuasiSeparatedSpace W]
    (r : Y ⟶ V) (i : V ⟶ W) [WeaklyEtale r] [IsImmersion i]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (hK : IsSfDerivedComplete l E W K) :
    IntegralOnSlice.IsComplete.{u, u} l E Y none
      ((ordinaryIntegralDerivedPull l E (r ≫ i)).obj K) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let F : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ F.p := by change l ≠ p; omega
  have hc : IntegralOnSlice.IsComplete.{u, u} l E W none K :=
    ⟨F, hl, (sfDerivedComplete_iff_legacy l E W F hl K).mp hK⟩
  have hu := (canonicalCompletionUnitCriterion.{u, u} l E W K).mpr hc
  let := hu
  have hout : IntegralOnSlice.IsComplete.{u, u} l E Y none
      ((ordinaryDerivedPull.{u, u} l E (r ≫ i)).obj K) :=
    (canonicalCompletionUnitCriterion.{u, u} l E Y _).mp
      ((ordinaryCompositeCompletionUnit_isIso.{u, u} l E r i K).mp (by infer_instance))
  exact sliceComplete_iso l E Y ((ordinaryDerivedIso l E (r ≫ i)).app K) hout

private theorem finiteModels_of_lisse_stalks
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hl : IsLocallyConstantProEtaleModuleSheaf X A F)
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A) F)) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) F := by
  classical
  let B := ULift.{u + 1, u} A
  let J := ProEt.topology X
  let R := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
  let F' := (proEtaleModuleRestriction X A).obj F
  obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over B F' (by
    obtain ⟨ι, W, g, hW, hM⟩ := (finiteLocal_iff X A F).mpr ⟨hl, hs⟩
    exact ⟨ι, W, g, hW, fun i ↦ let ⟨M, _, e⟩ := hM i; ⟨M, Module.finite_of_finite B, e⟩⟩)
  refine ⟨I, U, f, hf, fun i ↦ ?_⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := he i
  let := hL
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit X A)
  have h := proEtaleConstantRingUnit_over_locallyBijective X A (U i)
  have : Presheaf.IsLocallyInjective (J.over (U i)) a := h.1
  have : Presheaf.IsLocallySurjective (J.over (U i)) a := h.2
  have hc := ConstantScalarComparison.constantComparisonHom_isIso
    (J.over (U i)) B (R.over (U i)) a L
  refine ⟨L, Module.Finite.of_finite, ⟨?_⟩⟩
  exact (ConstantScalarComparison.restrictionFullyFaithful
    (J.over (U i)) B (R.over (U i)) a).preimageIso
      (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
          (J.over (U i)) B (R.over (U i)) a L))

private theorem finiteModels_iso
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules X (proEtaleConstantRing X A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) F) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) G := by
  obtain ⟨I, U, f, hf, he⟩ := hF
  refine ⟨I, U, f, hf, fun i ↦ ?_⟩
  obtain ⟨L, hL, ⟨a⟩⟩ := he i
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ a⟩⟩

private theorem finiteModels_pull
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses Y A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) F) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L)
      (proEtaleConstantModulePullback f A F) := by
  classical
  obtain ⟨I, U, a, ha, he⟩ := hF
  let L (i : I) := (he i).choose
  have hL (i : I) : Module.Finite (ULift.{u + 1} A) (L i) := (he i).choose_spec.1
  have hfinite (i : I) : Finite (L i) := by
    let := hL i
    exact Module.finite_of_finite (ULift.{u + 1} A)
  obtain ⟨b, hb, ht, _⟩ := proEtaleConstantModulePullback_locallyConstant f A F I U a ha L
    hfinite (fun i ↦ (he i).choose_spec.2)
  exact ⟨I, _, b, hb, fun i ↦ ⟨L i, hL i, ht i⟩⟩

private theorem finiteModels_zero
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X A
      (fun L ↦ Module.Finite (ULift.{u + 1} A) L) F := by
  exact finiteModels_of_lisse_stalks X A F (locallyConstant_of_isZero X A F hF)
    (fun Ω _ _ x ↦ finite_stalk_of_isZero X A F hF x)

/-- A finite open--closed tree simultaneously makes the residue cohomology of two
integral constructible complexes finite lisse. The assertion is stable on qcqs
weakly etale objects of each leaf, with ordinary uncompleted pullback throughout.

Source: Stacks Project, Tags 09Y4 and 09C3; Bhatt--Scholze, Lemma 6.5.8
and Remark 6.5.10 (blueprint: lem-fix-constructible-residue-tree).

Proof: each integral constructible complex has one finite interval containing its
residue support. For each degree in these two finite intervals choose the finite
constructibility stratification of its cohomology sheaf. Append these finitely many
partitions to the given ones and apply the finite open--closed refinement theorem.
Its scheme-theoretic factorizations retain the original partitions and all the
new residue strata. Along every branch apply qcqs completion locality at each qc
open child and its complementary closed child. The closed child's complement is
qc by the open child's quasi-compactness. Induction gives completeness on every
vertex and compatibility of ordinary pullback with each finite reduction. Apply
the same locality theorem once more on any qcqs weakly etale object of a leaf.
Exact constant coefficient pullback commutes with residue cohomology, preserving
its vanishing outside the original interval. The factorization through each
cohomology stratum, pullback composition and locally constant pullback preserve
the finite residue module models. Finite geometric stalks of the constructible
sheaves ensure that these local constant models are finite, hence finitely
generated over the finite residue ring. For degrees outside the interval use
the zero module model. Empty leaves impose no conditions, and for an empty list
of original partitions the appended residue partitions give the same argument. -/
theorem constructible_residue_tree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (_hM : sfIntegralConstructible l E W M)
    (_hN : sfIntegralConstructible l E W N)
    (m : ℕ) (n : Fin m → ℕ)
    (S : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (s : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ W)
    (_hs : ∀ (a : Fin m) (j : Fin (n a)), IsImmersion (s a j))
    (_hc : ∀ (a : Fin m) (j : Fin (n a)),
      Topology.IsConstructible (Set.range (s a j).base))
    (_hcover : ∀ a : Fin m,
      (⋃ j : Fin (n a), Set.range (s a j).base) = Set.univ)
    (_hdisjoint : ∀ a : Fin m, Pairwise (fun j k : Fin (n a) ↦
      Disjoint (Set.range (s a j).base) (Set.range (s a k).base)))
    (_hlisse : ∀ (a : Fin m) (j : Fin (n a))
      (K : DerivedCategory (scalarReductionSource.{u, u} l E W)),
      K = M ∨ K = N → ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheafOfUniverses (S a j)
        (Padic.coefficientExtensionRing l E 1)
        (proEtaleConstantModulePullback (s a j) (Padic.coefficientExtensionRing l E 1)
          ((DerivedCategory.homologyFunctor _ q).obj
            ((scalarReductionDerivedExtension l E W 0).obj K)))) :
    ∃ (d : ℕ) (T : Fin d → Scheme.{u}) (toW : ∀ v : Fin d, T v ⟶ W)
      (root : Fin d) (parent left right : Fin d → Fin d)
      (leftEdge : ∀ v : Fin d, T (left v) ⟶ T v)
      (rightEdge : ∀ v : Fin d, T (right v) ⟶ T v)
      (leaf : Fin d → Prop),
      (∃ e : T root ≅ W, e.hom = toW root) ∧ parent root = root ∧
      (∀ v, v ≠ root → (parent v).val < v.val) ∧
      (∀ v, CompactSpace (T v)) ∧ (∀ v, QuasiSeparatedSpace (T v)) ∧
      (∀ v, IsImmersion (toW v)) ∧
      (∀ v, v ≠ root → left (parent v) = v ∨ right (parent v) = v) ∧
      (∀ v, leaf v ↔ ∀ w, w ≠ root → parent w ≠ v) ∧
      (∀ v, ¬ leaf v →
        left v ≠ right v ∧ v.val < (left v).val ∧ v.val < (right v).val ∧
        parent (left v) = v ∧ parent (right v) = v ∧
        leftEdge v ≫ toW v = toW (left v) ∧
        rightEdge v ≫ toW v = toW (right v) ∧
        IsOpenImmersion (leftEdge v) ∧ QuasiCompact (leftEdge v) ∧
        IsClosedImmersion (rightEdge v) ∧
        Set.range (leftEdge v).base ∪ Set.range (rightEdge v).base = Set.univ ∧
        Disjoint (Set.range (leftEdge v).base) (Set.range (rightEdge v).base)) ∧
      (∀ v, leaf v → Nonempty (T v) →
        (∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T v ⟶ S a j, f ≫ s a j = toW v) ∧
        (∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
          (r : Y ⟶ T v) [WeaklyEtale r],
          ∀ K : DerivedCategory (scalarReductionSource.{u, u} l E W),
          K = M ∨ K = N →
          IntegralOnSlice.IsComplete l E Y none
            ((ordinaryIntegralDerivedPull l E (r ≫ toW v)).obj K) ∧
          ∃ a b : ℤ, a ≤ b ∧
            (∀ q : ℤ, q < a ∨ b < q → IsZero
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E Y 0).obj
                  ((ordinaryIntegralDerivedPull l E (r ≫ toW v)).obj K)))) ∧
            (∀ q : ℤ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses Y
              (Padic.coefficientExtensionRing l E 1)
              (fun L ↦ Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) L)
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E Y 0).obj
                  ((ordinaryIntegralDerivedPull l E (r ≫ toW v)).obj K)))))) := by
  classical
  let A := Padic.coefficientExtensionRing l E 1
  have : Finite A := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  obtain ⟨hMc, aM, bM, habM, hM⟩ := _hM
  obtain ⟨hNc, aN, bN, habN, hN⟩ := _hN
  let a := min aM aN
  let b := max bM bN
  have hab : a ≤ b := (min_le_left _ _).trans (habM.trans (le_max_left _ _))
  let K (c : Bool) := if c then M else N
  let H (c : Bool) (q : ℤ) := (DerivedCategory.homologyFunctor _ q).obj
    ((scalarReductionDerivedExtension l E W 0).obj (K c))
  have hconstruct (c : Bool) (q : ℤ) : IsConstructibleProEtaleModuleSheaf W A (H c q) := by
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
  have hstrat (j : J) : ∃ Z : Stratification W, 0 < Z.n ∧
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
  let P := Fin m ⊕ J
  let n' : P → ℕ := Sum.elim n (fun j ↦ (Z j).n)
  let S' : (p : P) → Fin (n' p) → Scheme.{u} := fun p ↦
    match p with
    | .inl c => S c
    | .inr j => (Z j).domain
  let s' : (p : P) → (k : Fin (n' p)) → S' p k ⟶ W := fun p ↦
    match p with
    | .inl c => s c
    | .inr j => (Z j).immersion
  have hs' (p : P) (k : Fin (n' p)) : IsImmersion (s' p k) := by
    cases p with
    | inl c => exact _hs c k
    | inr j => exact (Z j).isImmersion k
  have hc' (p : P) (k : Fin (n' p)) :
      Topology.IsConstructible (Set.range (s' p k).base) := by
    cases p with
    | inl c => exact _hc c k
    | inr j =>
      change Topology.IsConstructible (Set.range ((Z j).immersion k).base)
      rw [(Z j).range_immersion k]
      exact (Z j).isConstructible_stratum k
  have hcover' (p : P) : (⋃ k, Set.range (s' p k).base) = Set.univ := by
    cases p with
    | inl c => exact _hcover c
    | inr j =>
      change (⋃ k : Fin (Z j).n, Set.range ((Z j).immersion k).base) = Set.univ
      simpa only [(Z j).range_immersion] using (Z j).iUnion_stratum_eq_univ
  have hdisjoint' (p : P) : Pairwise (fun k t : Fin (n' p) ↦
      Disjoint (Set.range (s' p k).base) (Set.range (s' p t).base)) := by
    cases p with
    | inl c => exact _hdisjoint c
    | inr j =>
      change Pairwise (fun k t : Fin (Z j).n ↦
        Disjoint (Set.range ((Z j).immersion k).base)
          (Set.range ((Z j).immersion t).base))
      simpa only [(Z j).range_immersion] using (Z j).pairwise_disjoint_stratum
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  obtain ⟨O, Q, C, o, c, q, z, _, _, _, _, _, _, _, _, _,
      d, T, toW, root, parent, left, right, leftEdge, rightEdge, leaf,
      hroot, hparent, horder, hleft, hright, hcompact, hqs, himmersion,
      hchildren, hleaf, hsplit, _, _, _, hfactor⟩ :=
    exists_finite_open_closed_refinement (Fintype.card P) (fun p ↦ n' (e p))
      (fun p ↦ S' (e p)) (fun p ↦ s' (e p))
      (fun p ↦ hs' (e p)) (fun p ↦ hc' (e p))
      (fun p ↦ hcover' (e p)) (fun p ↦ hdisjoint' (e p))
  have factors (v : Fin d) (hv : leaf v) (hn : Nonempty (T v)) (p : P) :
      ∃ k : Fin (n' p), ∃ f : T v ⟶ S' p k, f ≫ s' p k = toW v := by
    obtain ⟨p', rfl⟩ := e.surjective p
    exact hfactor v hv hn p'
  refine ⟨d, T, toW, root, parent, left, right, leftEdge, rightEdge, leaf,
    hroot, hparent, horder, hcompact, hqs, himmersion, hchildren, hleaf, ?_, ?_⟩
  · intro v hv
    obtain ⟨hne, hlt, hrt, hpl, hpr, hopen, hclosed, hqc, _, hunion, hdis⟩ := hsplit v hv
    exact ⟨hne, hlt, hrt, hpl, hpr, hleft v hv, hright v hv,
      hopen, hqc, hclosed, hunion, hdis⟩
  · intro v hv hn
    refine ⟨fun c ↦ factors v hv hn (.inl c), ?_⟩
    intro Y _ _ r _ L hL
    let : CompactSpace (T v) := hcompact v
    let : QuasiSeparatedSpace (T v) := hqs v
    let : IsImmersion (toW v) := himmersion v
    have complete : IsComplete l E Y none
        ((ordinaryIntegralDerivedPull l E (r ≫ toW v)).obj L) := by
      apply residue_complete l E r (toW v) L
      rcases hL with rfl | rfl
      · exact hMc
      · exact hNc
    refine ⟨complete, a, b, hab, ?_, ?_⟩
    · intro t ht
      obtain ⟨β⟩ := ordinaryIntegralReductionHomology l E (r ≫ toW v) L 0 t
      have hz : IsZero ((DerivedCategory.homologyFunctor _ t).obj
          ((scalarReductionDerivedExtension l E W 0).obj L)) := by
        rcases hL with rfl | rfl
        · exact hzero true t ht
        · exact hzero false t ht
      exact ((proEtaleConstantModulePullbackFunctor (r ≫ toW v) A).map_isZero hz).of_iso β
    · intro t
      obtain ⟨β⟩ := ordinaryIntegralReductionHomology l E (r ≫ toW v) L 0 t
      apply finiteModels_iso Y A β.symm
      by_cases ht : t ∈ Finset.Icc a b
      · let c : Bool := if L = M then true else false
        have hLc : L = K c := by
          rcases hL with h | h
          · simp [c, h, K]
          · by_cases hNM : N = M
            · simp [c, h, hNM, K]
            · simp [c, h, hNM, K]
        let j : J := (c, ⟨t, ht⟩)
        obtain ⟨k, f, hf⟩ := factors v hv hn (.inr j)
        have hfin := finiteModels_pull (r ≫ f) A _ (hmodels j k)
        obtain ⟨α, _⟩ := proEtaleConstantRingModulePullbackComposition
          (r ≫ f) ((Z j).immersion k) A
        have heq : (r ≫ f) ≫ (Z j).immersion k = r ≫ toW v := by
          rw [Category.assoc, hf]
        let γ : proEtaleConstantModulePullback (r ≫ toW v) A (H c t) ≅
            proEtaleConstantModulePullback (r ≫ f) A
              (proEtaleConstantModulePullback ((Z j).immersion k) A (H c t)) :=
          eqToIso (congrArg (fun g ↦ proEtaleConstantModulePullback g A (H c t)) heq.symm)
            ≪≫ α.app (H c t)
        rw [hLc]
        exact finiteModels_iso Y A γ.symm hfin
      · have hout : t < a ∨ b < t := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at ht
          exact ht
        have hz : IsZero ((DerivedCategory.homologyFunctor _ t).obj
            ((scalarReductionDerivedExtension l E W 0).obj L)) := by
          rcases hL with rfl | rfl
          · exact hzero true t hout
          · exact hzero false t hout
        exact finiteModels_zero Y A _
          ((proEtaleConstantModulePullbackFunctor (r ≫ toW v) A).map_isZero hz)

end WeilConjectures
