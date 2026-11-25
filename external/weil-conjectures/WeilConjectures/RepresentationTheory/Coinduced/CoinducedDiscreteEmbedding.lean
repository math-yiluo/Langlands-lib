/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Algebra
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer

/-!
# Coinduced embeddings of discrete continuous modules

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology.
The coinduced embedding is the agent-written comparison ingredient
(blueprint: lem-exc-coinduced-discrete-embedding).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

private def coinducedTranslation (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Type v) [Ring A] (V : Type w)
    [AddCommGroup V] [Module A V] : Representation A G (LocallyConstant G V) where
  toFun h := LocallyConstant.comapₗ A ⟨fun x ↦ x * h, continuous_mul_const h⟩
  map_one' := by ext f x; simp
  map_mul' h k := by ext f x; simp [mul_assoc]

private theorem coinducedTranslation_open (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] (V : Type w) [AddCommGroup V] [Module A V]
    (f : LocallyConstant G V) :
    IsOpen {h : G | coinducedTranslation G A V h f = f} := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of G) V f f.continuous
  let H : Subgroup G :=
    { carrier := {h | coinducedTranslation G A V h f = f}
      one_mem' := by simp
      mul_mem' := by
        intro h k hh hk
        change coinducedTranslation G A V (h * k) f = f
        rw [map_mul, Module.End.mul_apply, hk, hh]
      inv_mem' := by
        intro h hh
        have he := congrArg (fun z ↦ coinducedTranslation G A V h⁻¹ z) hh
        simpa [← Module.End.mul_apply, ← map_mul] using he.symm }
  have hle : (U : Set G) ⊆ H := by
    intro h hh
    change coinducedTranslation G A V h f = f
    ext x
    exact hU x h hh
  exact H.isOpen_of_openSubgroup (U := U.toOpenSubgroup) hle

private def discreteCoinducedObj (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    DiscreteContinuousRep.{v, u, max u w} A G :=
  ⟨Rep.of (coinducedTranslation G A M.obj.V), coinducedTranslation_open G A M.obj.V⟩

private def discreteCoinducedMap {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {A : Type v} [Ring A] {M N : DiscreteContinuousRep.{v, u, max u w} A G}
    (a : M ⟶ N) : discreteCoinducedObj G A M ⟶ discreteCoinducedObj G A N :=
  ObjectProperty.homMk (Rep.ofHom
    { toLinearMap := LocallyConstant.mapₗ A a.hom.hom.toLinearMap
      isIntertwining' := by
        intro h
        ext f x
        rfl })

private def discreteCoinducedFunctor (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] : DiscreteContinuousRep.{v, u, max u w} A G ⥤
      DiscreteContinuousRep.{v, u, max u w} A G where
  obj := discreteCoinducedObj G A
  map := discreteCoinducedMap
  map_id M := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    apply LocallyConstant.ext
    intro x
    rfl

private def discreteOrbitFunction {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type v} [Ring A]
    (M : DiscreteContinuousRep.{v, u, max u w} A G) (m : M.obj.V) :
    LocallyConstant G M.obj.V where
  toFun x := M.obj.ρ x m
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y : G ↦ x⁻¹ * y) ⁻¹' {h | M.obj.ρ h m = m},
      (M.property m).preimage (continuous_const_mul _), ?_, ?_⟩
    · simp
    · intro y hy
      change M.obj.ρ (x⁻¹ * y) m = m at hy
      have he := congrArg (fun z ↦ M.obj.ρ x z) hy
      simpa [← Module.End.mul_apply, ← map_mul] using he

private def discreteOrbitMap {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {A : Type v} [Ring A] (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    M ⟶ discreteCoinducedObj G A M :=
  ObjectProperty.homMk (Rep.ofHom
    { toLinearMap :=
        { toFun := discreteOrbitFunction M
          map_add' a b := by
            apply LocallyConstant.ext
            intro x
            exact map_add (M.obj.ρ x) a b
          map_smul' a b := by
            apply LocallyConstant.ext
            intro x
            exact (M.obj.ρ x).map_smul a b }
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro m
        apply LocallyConstant.ext
        intro x
        change M.obj.ρ x (M.obj.ρ h m) = M.obj.ρ (x * h) m
        simp [map_mul, Module.End.mul_apply] })

/-- Discrete continuous modules admit the natural injective orbit-map embedding into
continuous functions with right translation. `LocallyConstant G M.obj.V` is exactly
`Cont(G, M)` with discrete codomain, and its module operations are pointwise.
The linear equivalences identify the coinduced objects with those function modules.

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology
(blueprint: lem-exc-coinduced-discrete-embedding).

Proof: (1) Pointwise operations give the function module, and precomposition by right
multiplication gives a linear left action: translating successively by `k` then `h`
evaluates at `x * h * k`, and translation by one is the identity.
(2) `lem-exc-coinduced-functions-open-stabilizer` supplies an open normal subgroup
under whose right translations any continuous function is invariant. Its stabilizer
contains that subgroup, so is open; hence the coinduced object belongs to
`DiscreteContinuousRep`, the category used in `lem-exc-discrete-modules-abelian`.
(3) The orbit map is locally constant on the open left cosets of each element's
stabilizer. It is linear pointwise and equivariant since `(x * h) m = x (h m)`.
Evaluation at one proves injectivity. Equivariant linear maps commute with the orbit
maps pointwise, giving naturality; on functions the coinduced map is postcomposition. -/
theorem exists_coinduced_discrete_embedding
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ D : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        DiscreteContinuousRep.{v, u, max u w} A G,
      ∃ e : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        (D.obj M).obj.V ≃ₗ[A] LocallyConstant G M.obj.V,
      ∃ ι : 𝟭 (DiscreteContinuousRep.{v, u, max u w} A G) ⟶ D,
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G)
          (h : G) (f : (D.obj M).obj.V) (x : G),
          e M ((D.obj M).obj.ρ h f) x = e M f (x * h)) ∧
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (a : M ⟶ N)
          (f : (D.obj M).obj.V) (x : G),
          e N ((D.map a).hom.hom f) x = a.hom.hom (e M f x)) ∧
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (m : M.obj.V) (x : G),
          e M ((ι.app M).hom.hom m) x = M.obj.ρ x m) ∧
        (∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
          Function.Injective (ι.app M).hom.hom) := by
  let D := discreteCoinducedFunctor.{u, v, w} G A
  let ι : 𝟭 (DiscreteContinuousRep.{v, u, max u w} A G) ⟶ D :=
    { app := discreteOrbitMap
      naturality := by
        intro M N a
        apply ObjectProperty.hom_ext
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro m
        apply LocallyConstant.ext
        intro x
        exact (Rep.hom_comm_apply a.hom x m).symm }
  refine ⟨D, fun M ↦ LinearEquiv.refl A (LocallyConstant G M.obj.V), ι,
    ?_, ?_, ?_, ?_⟩
  · intro M h f x
    rfl
  · intro M N a f x
    rfl
  · intro M m x
    rfl
  · intro M m n h
    have he := congrArg (fun f : LocallyConstant G M.obj.V ↦ f 1) h
    change M.obj.ρ 1 m = M.obj.ρ 1 n at he
    simpa only [map_one, Module.End.one_apply] using he

end Rep
