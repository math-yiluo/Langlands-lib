/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeakContractibleEquivalences
import WeilConjectures.SixFunctors.Constructible.ConstructibleResidueTree
import WeilConjectures.SixFunctors.Supporting.AffineCommonProjectiveCharts

/-!
# Common projective sheaf charts for two integral constructible complexes

Source: Stacks Project, proetale.tex, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-constructible-projective-chart-refinement).

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

/-- Two integral constructible complexes have simultaneous bounded projective sheaf
models after a finite open--closed refinement and weakly contractible affine covers.

Source: Stacks Project, Tag 09C3; Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8
(blueprint: lem-fix-constructible-projective-chart-refinement).

Proof:
1. Apply `constructible_residue_tree`. It retains all given stratum factorizations
   and makes the two ordinary restrictions complete, with bounded finite lisse
   residue, on every qcqs weakly etale object of each nonempty leaf. Identity
   restriction gives the required completeness and residue assertions on the leaf.
2. Clause (2) of the single-affine hypercover theorem supplies a covering object
   with w-contractible ring. The weak-contractibility equivalences applied in its
   own small pro-etale site give the epimorphism-evaluation property on this affine.
3. Apply `affine_common_projective_charts` to the two ordinary restrictions on this
   cover. The existing bounded-field Tor lemma gives the all-resolutions Tor
   bound; bounded finite local residue models give intrinsic constructibility. The
   existing projective-model theorem and the common clopen transport lemma supply
   one finite disjoint cover with both composite ordinary projective models.
4. Identify the covering arrow with the canonical arrow to the terminal object.
   The pro-etale precoverage gives surjectivity on points. Lift a leaf point to the
   affine cover, then to one member of the finite open cover. This proves that the
   chart composites cover the leaf. Reassociate their composites to identify the
   displayed model isomorphisms. Empty leaves have no chart condition. -/
theorem constructible_projective_chart_refinement
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
        (∀ K : DerivedCategory (scalarReductionSource.{u, u} l E W),
          K = M ∨ K = N →
          IntegralOnSlice.IsComplete l E (T v) none
            ((ordinaryIntegralDerivedPull l E (toW v)).obj K) ∧
          ∃ a b : ℤ, a ≤ b ∧
            (∀ q : ℤ, q < a ∨ b < q → IsZero
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E (T v) 0).obj
                  ((ordinaryIntegralDerivedPull l E (toW v)).obj K)))) ∧
            (∀ q : ℤ, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses (T v)
              (Padic.coefficientExtensionRing l E 1)
              (fun L ↦ Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) L)
              ((DerivedCategory.homologyFunctor _ q).obj
                ((scalarReductionDerivedExtension l E (T v) 0).obj
                  ((ordinaryIntegralDerivedPull l E (toW v)).obj K))))) ∧
        ∃ V : (T v).ProEt, IsAffine V.left ∧
          (∀ (F G : Sheaf (ProEt.topology V.left) (Type (u + 1)))
            (f : F ⟶ G), Epi f →
            Function.Surjective (f.hom.app (Opposite.op (ProEt.mk (𝟙 V.left))))) ∧
          Presieve.singleton (MorphismProperty.Over.homMk V.hom (Category.comp_id _) :
            V ⟶ ProEt.mk (𝟙 (T v))) ∈
            (ProEt.precoverage (T v)) (ProEt.mk (𝟙 (T v))) ∧
          ∃ (c : ℕ) (U : Fin c → V.left.Opens),
            (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
            (∀ i, CompactSpace (U i).toScheme) ∧
            (∀ i, QuasiSeparatedSpace (U i).toScheme) ∧
            (∀ x : T v, ∃ i : Fin c,
              x ∈ Set.range (((U i).ι ≫ V.hom).base)) ∧
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
                  ((U i).ι ≫ V.hom ≫ toW v)).obj K ≅ DerivedCategory.Q.obj P))  := by
  classical
  obtain ⟨d, T, toW, root, parent, left, right, leftEdge, rightEdge, leaf,
    hroot, hparent, hlt, hcompact, hqs, himm, hchild, hleaf, hsplit, hlocal⟩ :=
    constructible_residue_tree l E W _hl M N _hM _hN m n S s
      _hs _hc _hcover _hdisjoint _hlisse
  refine ⟨d, T, toW, root, parent, left, right, leftEdge, rightEdge, leaf,
    hroot, hparent, hlt, hcompact, hqs, himm, hchild, hleaf, hsplit, ?_⟩
  intro v hv hne
  let := hcompact v
  let := hqs v
  obtain ⟨hfactor, hresidue⟩ := hlocal v hv hne
  refine ⟨hfactor, ?_, ?_⟩
  · intro K hK
    simpa only [Category.id_comp] using hresidue (T v) (𝟙 (T v)) K hK
  · have : CompactSpace (ProEt.mk (𝟙 (T v))).left := hcompact v
    have : QuasiSeparatedSpace (ProEt.mk (𝟙 (T v))).left := hqs v
    obtain ⟨D, f, hf, g, hD, hg⟩ :=
      (AlgebraicGeometry.exists_proetale_hypercover_single_affine
        (T v) (ProEt.mk (𝟙 (T v))) inferInstance inferInstance).2.1
          (ProEt.mk (𝟙 (T v))) inferInstance
    have := hf
    have := hD
    let V : (T v).ProEt := ProEt.mk f
    have : IsAffine V.left := inferInstanceAs (IsAffine (Spec D))
    have : WeaklyEtale (𝟙 V.left) := inferInstanceAs (WeaklyEtale (𝟙 (Spec D)))
    have hw : ∀ (F G : Sheaf (ProEt.topology V.left) (Type (u + 1)))
        (a : F ⟶ G), Epi a →
          Function.Surjective (a.hom.app (Opposite.op (ProEt.mk (𝟙 V.left)))) := by
      intro F G a ha
      exact (proetale_weakContractible_equivalences V.left
        (ProEt.mk (𝟙 V.left))).2.1.mp
          ((proetale_weakContractible_equivalences V.left
            (ProEt.mk (𝟙 V.left))).1.mp
              ((proetale_weakContractible_equivalences V.left
                (ProEt.mk (𝟙 V.left))).2.2 D (𝟙 V.left))) F G a
    have hg' : g = (MorphismProperty.Over.homMk V.hom (Category.comp_id _) :
        V ⟶ ProEt.mk (𝟙 (T v))) := by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w g)
    rw [hg'] at hg
    refine ⟨V, inferInstance, hw, hg, ?_⟩
    obtain ⟨c, U, hcov, hdis, hqc, hquasi, hmodel⟩ :=
      affine_common_projective_charts l E W V.left (V.hom ≫ toW v) hw M N
        (hresidue V.left V.hom)
    refine ⟨c, U, hcov, hdis, hqc, hquasi, ?_, ?_⟩
    · have hbig : Presieve.singleton V.hom ∈ Scheme.proetalePrecoverage (T v) := by
        rw [ProEt.mem_precoverage_iff, Presieve.map_singleton] at hg
        exact hg
      have hsurj := (Scheme.singleton_mem_precoverage_iff (P := @WeaklyEtale) V.hom).1
        hbig.2
      intro x
      obtain ⟨y, rfl⟩ := hsurj.1 x
      have hy : y ∈ (⨆ i, U i : V.left.Opens) := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact ⟨i, ⟨⟨y, hi⟩, rfl⟩⟩
    · intro i K hK
      simpa only [Category.assoc] using hmodel i K hK

end WeilConjectures
