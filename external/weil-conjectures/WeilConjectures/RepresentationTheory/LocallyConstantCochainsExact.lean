/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsStructure
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsDegreewiseExact


/-!
# LocallyConstantCochainsExact

Source: Stacks Project, Etale Cohomology, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-exact).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- The locally constant integer cochain complex is additive and degreewise exact.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed inhomogeneous
cochain differential; steps 1 and 2 of lem-sc-locally-constant-cochains-effaceable.

Proof: Give LC(G^n,E(M)) its pointwise additive group structure. Precomposition by
projections and adjacent multiplication preserves local constancy. For the action face,
a locally constant cochain has finitely many values since G^n is compact. Intersect the
open stabilizers of these values: on each fiber and a sufficiently small coset the action
face is constant. Thus the displayed sum is a locally constant additive differential.
The face identities pair each summand in d squared with its negative, so d squared is
zero, including n=0. Equivariant coefficient maps commute with the action and the other
faces, hence give chain maps; identity, composition and addition hold pointwise.
Use these actual terms and differentials to construct C and take identity coordinate
maps, transporting along E. Equivalences preserve short exact sequences. Kernels and
cokernels of discrete representations are the underlying module kernels and cokernels:
submodules inherit open stabilizers and quotient stabilizers contain those of lifts.
A locally constant cochain on compact G^n has finite image and clopen fibers. Choose a
lift of each image value through a coefficient surjection and use it on that fiber.
This is a locally constant lift. The kernel equation is pointwise, proving exactness
and monicity of the first map in every degree. No finiteness of the ring is used.
(blueprint: lem-sc-locally-constant-cochains-exact). -/
theorem exists_locallyConstantCochains_exact
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
        ∃ a : C.Additive,
          letI := a
          ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
            ((S.map C).map (HomologicalComplex.eval
              AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n)).ShortExact := by
  obtain ⟨C, e, hm, hd⟩ := exists_locallyConstantCochains_structure G A E
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have ha : C.Additive := by
    constructor
    intro M N f h
    ext n x
    apply (e N n).injective
    ext g
    change e N n (((C.map (f + h)).f n) x) g =
      e N n (((C.map f).f n) x + ((C.map h).f n) x) g
    simp only [map_add, LocallyConstant.add_apply]
    rw [hm, hm, hm]
    rw [Functor.map_add]
    rfl
  let := ha
  exact ⟨C, e, hm, hd, ha, locallyConstantCochains_degreewise_exact G A E C e hm⟩

end Rep
