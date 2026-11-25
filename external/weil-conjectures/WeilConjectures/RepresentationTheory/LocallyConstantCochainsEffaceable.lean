/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsExact
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsInvariantsZero
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding

/-!
# Effaceable locally constant cochain cohomology over the integers

Source: Stacks Project, Etale Cohomology, Tag 0DVG, profinite comparison.
(blueprint: lem-sc-locally-constant-cochains-effaceable).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

private theorem exists_homology_deltaFunctor
    {A : Type v} [Category.{w} A] [Abelian A]
    (C : A ⥤ CochainComplex AddCommGrpCat.{s} ℕ) [C.Additive]
    (hs : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      ((S.map C).map (HomologicalComplex.eval
        AddCommGrpCat.{s} (ComplexShape.up ℕ) n)).ShortExact) :
    ∃ T : CohomologicalDeltaFunctor A AddCommGrpCat.{s},
      T.F = (fun q ↦ C ⋙ HomologicalComplex.homologyFunctor
        AddCommGrpCat.{s} (ComplexShape.up ℕ) q) := by
  have hse (S : ShortComplex A) (hS : S.ShortExact) : (S.map C).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (hs S hS)
  let T : CohomologicalDeltaFunctor A AddCommGrpCat.{s} :=
    { F := fun q ↦ C ⋙ HomologicalComplex.homologyFunctor _ _ q
      additive := fun _ ↦ inferInstance
      delta := fun S hS n ↦ (hse S hS).δ n (n + 1) rfl
      mono_zero := by
        intro S hS
        have : Mono ((C.map S.f).f 0) := (hs S hS 0).mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          (C.map S.f) 0 (by
            intro i hi
            change i + 1 = 0 at hi
            omega)
      exact_middle := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₂ n⟩
      exact_right := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₃ n (n + 1) rfl⟩
      exact_left := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₁ n (n + 1) rfl⟩
      naturality := by
        intro S R hS hR φ n
        exact HomologicalComplex.HomologySequence.δ_naturality
          (C.mapShortComplex.map φ) (hse S hS) (hse R hR) n (n + 1) rfl }
  exact ⟨T, rfl⟩

/-- The locally constant inhomogeneous complex gives an effaceable delta-functor
with degree zero equal to invariants. The terms, coefficient maps and differential
specify the complex functor up to its natural coordinate isomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed inhomogeneous differential
and final profinite comparison.
(blueprint: lem-sc-locally-constant-cochains-effaceable).

Proof: In degree n take the additive group of locally constant functions G^n to E(M).
The first face uses the action, the interior faces multiply adjacent arguments, and the
last face drops the last argument. The open-stabilizer condition makes each orbit map
locally constant. Thus all faces preserve local constancy; they are additive, and the
face identities cancel the terms of the square of the alternating differential.
Postcomposition by equivariant coefficient maps defines the complex functor. For a short
exact sequence, kernels are pointwise and surjectivity follows by choosing a lift on each
of the finitely many clopen fibers of a cochain on compact G^n. These degreewise short
exact sequences give natural connecting maps and the exact homology sequence, hence T.
In degree zero, G^0 is a point and the differential is g acting on m minus m; there are
no incoming boundaries. This identifies T in degree zero naturally with invariants.
Embed M into D(M), the locally constant functions G to M with right translation, by the
orbit map. Evaluation at 1 proves monicity. Compactness of the finite clopen partition
of a function gives an open subgroup fixing it, so D(M) is a discrete representation.
For a positive-degree D(M)-valued cochain c, insert x in its first coordinate and evaluate
its value at 1 to define h(c)(g_1,...,g_{n-1})(x)=c(x,g_1,...,g_{n-1})(1).
A finite cover in the compact x coordinate shows that h(c) is locally constant into the
whole discrete function module. Expansion gives dh+hd=1 in positive degrees, with all
merged and final faces cancelling. Every positive cocycle is therefore a boundary.
The induced map on positive cohomology into D(M) is zero; transport this monomorphism
back across E to obtain effacement in A. This uses arbitrary integer modules. -/
theorem exists_locallyConstantCochains_effaceable
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    : ∃ C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ,
      ∃ e : ∀ (M : A) (n : ℕ),
          (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V,
        (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
          e N n (((C.map f).f n) x) g =
            (E.functor.map f).hom.hom (e M n x g)) ∧
        (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
            (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) ∧
        ∃ T : CohomologicalDeltaFunctor A AddCommGrpCat.{max u s},
          T.F = (fun q ↦ C ⋙ HomologicalComplex.homologyFunctor
            AddCommGrpCat.{max u s} (ComplexShape.up ℕ) q) ∧
          Nonempty (T.F 0 ≅
            (E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
              forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)) ∧
          (∀ (n : ℕ), 0 < n → ∀ (M : A),
            ∃ (N : A) (f : M ⟶ N), Mono f ∧ (T.F n).map f = 0) := by
  obtain ⟨C, e, hm, hd, ha, hs⟩ := exists_locallyConstantCochains_exact G A E
  have : C.Additive := ha
  obtain ⟨T, hT⟩ := exists_homology_deltaFunctor C hs
  refine ⟨C, e, hm, hd, T, hT, ?_, ?_⟩
  · rw [hT]
    exact locallyConstantCochains_invariants_zero G A E C e hm hd
  · intro n hn M
    obtain ⟨N, f, hf, hN⟩ :=
      locallyConstantCochains_acyclic_embedding G A E C e hm hd M
    refine ⟨N, f, hf, ?_⟩
    rw [hT]
    exact ((hN n hn).isZero_homology).eq_of_tgt _ _

end Rep
