/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Topology.Separation.Regular
public import Mathlib.CategoryTheory.Abelian.Exact

import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Abelian structure on discrete modules with a continuous group action

Source: Stacks Project, Etale Cohomology, Definition 04JP and the following paragraph,
in Section 0A2H (blueprint: lem-exc-discrete-modules-abelian-structure).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private def discreteVectorStabilizer {A : Type u} [Ring A] {G : Type v} [Group G]
    (M : Rep.{w} A G) (x : M) : Subgroup G where
  carrier := {g | M.ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change M.ρ (g * h) x = x
    rw [M.ρ_mul, LinearMap.comp_apply, hh, hg]
  inv_mem' := by
    intro g hg
    exact (M.ρ.inv_apply_eq_iff).2 hg.symm

private theorem discreteOpenImage {A : Type u} [Ring A] {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {M N : Rep.{w} A G}
    (f : M ⟶ N) (x : M) (hx : IsOpen {g : G | M.ρ g x = x}) :
    IsOpen {g : G | N.ρ g (f.hom x) = f.hom x} := by
  apply Subgroup.isOpen_mono (H₁ := discreteVectorStabilizer M x)
    (H₂ := discreteVectorStabilizer N (f.hom x)) _ hx
  intro g hg
  change N.ρ g (f.hom x) = f.hom x
  rw [← Rep.hom_comm_apply, hg]

/-- Stacks Project, Definition 04JP and the paragraph after it (Section 0A2H).
The zero module has its unique action. Binary direct sums have componentwise action and
open stabilizers by intersection. An equivariant map has the ordinary module kernel,
whose stabilizers stay open, and the ordinary quotient cokernel, whose stabilizers contain
the open stabilizers of representatives. The usual universal properties are equivariant.
Addition of maps is equivariant; mono and epi coincide with injective and surjective maps,
respectively. These calculations give the abelian-category criterion of `def-sp-abelian`.
The image and kernel computed in this category are the underlying module image and kernel,
so exactness at each term is exactly underlying module exactness.
(blueprint: lem-exc-discrete-modules-abelian-structure) -/
theorem discreteRep_abelian_structure (A : Type u) [Ring A] [Finite A]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ h : CategoryTheory.Abelian (DiscreteContinuousRep.{u, v, w} A G),
      (letI : CategoryTheory.Abelian (DiscreteContinuousRep.{u, v, w} A G) := h
       let forgetDiscrete : DiscreteContinuousRep.{u, v, w} A G ⥤ ModuleCat.{w} A :=
         (ObjectProperty.ι (fun X : Rep.{w} A G =>
           ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})) ⋙
           forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
       forgetDiscrete.Additive ∧
       PreservesFiniteLimits forgetDiscrete ∧
       PreservesFiniteColimits forgetDiscrete ∧
       ∀ S : ShortComplex (DiscreteContinuousRep.{u, v, w} A G),
         S.Exact ↔ (S.map forgetDiscrete).Exact) := by
  let P : ObjectProperty (Rep.{w} A G) :=
    fun X ↦ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}
  -- Injective equivariant maps identify stabilizers.
  have : P.IsClosedUnderSubobjects := ⟨by
    intro X Y f hf hY x
    have hinj := (Rep.mono_iff_injective f).1 hf
    have heq : {g : G | X.ρ g x = x} = {g : G | Y.ρ g (f.hom x) = f.hom x} := by
      ext g
      change X.ρ g x = x ↔ Y.ρ g (f.hom x) = f.hom x
      rw [← Rep.hom_comm_apply]
      exact ⟨fun h ↦ congrArg f.hom h, fun h ↦ hinj h⟩
    rw [heq]
    exact hY (f.hom x)⟩
  -- A quotient stabilizer contains the open stabilizer of any lift.
  have : P.IsClosedUnderQuotients := ⟨by
    intro X Y f hf hX y
    obtain ⟨x, rfl⟩ := (Rep.epi_iff_surjective f).1 hf y
    exact discreteOpenImage f x (hX x)⟩
  have : P.ContainsZero := ⟨by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := Rep.{w} A G)
    refine ⟨Z, hZ, ?_⟩
    have : Subsingleton Z.V := (Rep.isZero_iff Z).1 hZ
    intro x
    convert isOpen_univ (X := G) using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _⟩
  -- The projections jointly detect equality, including for the empty product.
  have : P.IsClosedUnderFiniteProducts := ⟨by
    intro J hJ
    refine ⟨?_⟩
    intro X hX
    obtain ⟨p⟩ := hX
    intro x
    have heq : {g : G | X.ρ g x = x} =
        ⋂ j : Discrete J, {g : G | (p.diag.obj j).ρ g ((p.π.app j).hom x) =
          (p.π.app j).hom x} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hg j
        rw [← Rep.hom_comm_apply]
        change (p.π.app j).hom (X.ρ g x) = (p.π.app j).hom x
        rw [hg]
      · intro hg
        apply Concrete.isLimit_ext
          (p.diag ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A))
          (isLimitOfPreserves (forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) p.isLimit)
        intro j
        exact (Rep.hom_comm_apply (p.π.app j) g x).trans (hg j)
    rw [heq]
    exact isOpen_iInter_of_finite fun j ↦ p.prop_diag_obj j ((p.π.app j).hom x)⟩
  -- Inherit kernels, cokernels, and the normal mono/epi axioms from representations.
  let h : Abelian P.FullSubcategory := inferInstance
  refine ⟨h, ?_⟩
  let : Abelian P.FullSubcategory := h
  change (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)).Additive ∧
    PreservesFiniteLimits (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) ∧
    PreservesFiniteColimits (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) ∧
    ∀ S : ShortComplex P.FullSubcategory,
      S.Exact ↔ (S.map (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A))).Exact
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) P.ι := fun f ↦ P.preservesKernels_ι f
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) P.ι := fun f ↦ P.preservesCokernels_ι f
  have : PreservesFiniteLimits P.ι :=
    Functor.preservesFiniteLimits_of_preservesKernels P.ι
  have : PreservesFiniteColimits P.ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels P.ι
  have : PreservesFiniteLimits (forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) := by
    infer_instance
  have : PreservesFiniteColimits (forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) := by
    infer_instance
  have : PreservesFiniteLimits (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)) :=
    comp_preservesFiniteColimits _ _
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro S
  exact (S.exact_map_iff_of_faithful
    (P.ι ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A))).symm

end Rep
