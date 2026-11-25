/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology
public import WeilConjectures.RepresentationTheory.HomogeneousInhomogeneousContinuousCohomology

/-!
# Continuous cohomology from a transported injective resolution

Source: Stacks Project, Etale Cohomology, Section 0DVG.
(blueprint: lem-sc-discrete-resolution-continuous-cohomology).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- Additive equivalence between the homology of the invariants of a transported injective
resolution and homogeneous continuous cohomology, with all coefficient modules in the same
universe.

Source: Stacks Project, Etale Cohomology, Section 0DVG, profinite comparison.
(blueprint: lem-sc-discrete-resolution-continuous-cohomology).

Proof: An equivalence of abelian categories preserves injective objects and exactness,
so E carries the given resolution to an injective resolution in discrete representations.
Continuous inhomogeneous cochains are exact on short exact sequences: a continuous map
from a compact finite power of G to a discrete module has finite image, and finitely many
lifts through a surjection give a continuous lifting. Their degree-zero cohomology is
invariants. For a discrete module M, the orbit map m maps to (x maps to x*m) embeds M
into locally constant functions G to M with right translation. Each locally constant
function has open stabilizer: compactness gives a finite clopen partition, and continuity
of multiplication gives a common open subgroup stabilizing this partition. The insertion
operator h(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1) satisfies dh+hd=1 in positive
degrees; it is continuous by the compact-open exponential law and finite clopen partitions.
This effaces positive continuous cohomology. The cohomological delta-functor is therefore
universal, and agrees with derived invariants in degree zero; extending the identity in
both directions and using uniqueness gives inverse comparisons in every degree.
The compact-open exponential law identifies iterated maps with jointly continuous maps.
Homogeneous equivariant cochains evaluate at (1,g1,g1*g2,...) to inhomogeneous cochains;
the inverse sends c to (g0,...,gn maps to g0*c(g0^-1*g1,...,g(n-1)^-1*gn)). Expanding
alternating omission proves compatibility with the differential. Postcomposition with
the equivariant coefficient equivalence identifies the complexes for E(F) and N.
Taking kernel modulo image, which computes underlying TopModuleCat homology, completes
the comparison with the invariant complex of the given resolution. This uses integer
modules and does not require a finite coefficient ring. -/
noncomputable def invariantResolutionHomologyAddEquivContinuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    ((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃+
      continuousCohomology q N := by
  classical
  have hN : ∀ x : N.V, IsOpen {g : G | N.ρ g x = x} := by
    intro x
    have hx := (E.functor.obj F).property (e.symm x)
    have hs : {g : G | N.ρ g x = x} =
        {g : G | (E.functor.obj F).obj.ρ g (e.symm x) = e.symm x} := by
      ext g
      constructor
      · intro hg
        apply e.injective
        rw [he, e.apply_symm_apply, hg]
      · intro hg
        have h := congrArg e hg
        change N.ρ g x = x
        simpa only [he, e.apply_symm_apply] using h
    rw [hs]
    exact hx
  have htex := exists_homogeneousCochains_inhomogeneous_coordinates G N hN
  have ht := htex.choose_spec
  set t := htex.choose
  clear_value t
  let V := forget₂ (TopModuleCat.{max u s} ℤ) (ModuleCat.{max u s} ℤ) ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat
  let K := (V.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (TopRep.homogeneousCochains N)
  let t' : ∀ n : ℕ, K.X n ≃+
      LocallyConstant (Fin n → G) (E.functor.obj F).obj.V :=
    fun n ↦ (t n).trans (AddEquiv.mk' (LocallyConstant.congrRight e.symm.toEquiv)
      fun _ _ ↦ by ext; simp [LocallyConstant.congrRight])
  have ht' : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
      t' (n + 1) ((K.d n (n + 1)) x) g =
        (E.functor.obj F).obj.ρ (g 0) (t' n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • t' n x (Fin.contractNth k (· * ·) g) := by
    intro n x g
    change e.symm (t (n + 1) ((K.d n (n + 1)) x) g) = _
    apply e.injective
    rw [e.apply_symm_apply]
    change t (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) g = _
    rw [ht, map_add, map_sum]
    change N.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g) =
      e ((E.functor.obj F).obj.ρ (g 0) (e.symm (t n x (fun k ↦ g k.succ)))) +
        ∑ k : Fin (n + 1),
          e ((-1 : ℤ) ^ (k.val + 1) •
            e.symm (t n x (Fin.contractNth k (· * ·) g)))
    simp only [he, e.apply_symm_apply, map_zsmul]
  let a := invariantResolutionHomologyAddEquivInhomogeneous G A E F I K t' ht' q
  let b : K.homology q ≅ V.obj (continuousCohomology q N) :=
    ((TopRep.homogeneousCochains N).sc q).mapHomologyIso V
  exact a.trans b.addCommGroupIsoToAddEquiv

end Rep
