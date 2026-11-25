/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Continuity of the coinduced contracting operator

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison.
The explicit contraction is an agent-written proof ingredient
(blueprint: lem-exc-coinduced-homotopy-continuous).
-/

@[expose] public section

universe u v w

namespace Rep

/-- The formula inserting `x` as the first group variable and evaluating the resulting
function at the identity defines a linear map between continuous cochains.
`LocallyConstant G M.obj.V` is the coinduced function module of
`exists_coinduced_discrete_embedding`. Nested locally constant maps encode the discrete
topology on that whole module, rather than a compact-open topology.
The index `n + 1` ranges over all positive degrees, including degree one at `n = 0`.

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison
(blueprint: lem-exc-coinduced-homotopy-continuous).

Proof: (1) The setup of `lem-exc-discrete-modules-abelian` and
`lem-exc-coinduced-discrete-embedding` supplies the discrete module and the pointwise
module structure on its continuous function module with right translation.
Evaluation at one and substitution in the first variable are linear pointwise.
(2) For fixed remaining variables, the function of `x` obtained by this formula is
continuous into the discrete module: insertion of `x` is continuous, and evaluation
at one is continuous from the discrete function module. For any fixed tuple of
remaining variables, joint continuity supplies product neighborhoods where the
value is constant. Compactness of `G` gives a finite cover in the `x` variable.
Intersect the finitely many neighborhoods of the remaining tuple. On this
intersection all `x` values agree with the original function, so the resulting
function-valued map is locally constant into the discrete coinduced module.
Thus it is a continuous cochain; pointwise linearity gives the asserted linear map. -/
theorem exists_coinduced_continuous_contraction
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{v, u, w} A G) (n : ℕ) :
    ∃ h : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V) →ₗ[A]
        LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V),
      ∀ (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
        (g : Fin n → G) (x : G),
        h F g x = F (Fin.cons x g) 1 := by
  have hcons : Continuous
      (fun p : (Fin n → G) × G ↦ (Fin.cons p.2 p.1 : Fin (n + 1) → G)) :=
    continuous_snd.finCons (A := fun _ : Fin (n + 1) ↦ G) continuous_fst
  let hF (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
      (g : Fin n → G) : LocallyConstant G M.obj.V :=
    ⟨fun x ↦ F (Fin.cons x g) 1,
      (F.isLocallyConstant.comp (fun f ↦ f 1)).comp_continuous
        (continuous_id.finCons (A := fun _ : Fin (n + 1) ↦ G) continuous_const)⟩
  have hlc (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V)) :
      IsLocallyConstant (hF F) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g ↦ ?_
    have hjoint : IsLocallyConstant
        (fun p : (Fin n → G) × G ↦ F (Fin.cons p.2 p.1)) :=
      F.isLocallyConstant.comp_continuous hcons
    have hfixed : IsLocallyConstant
        (fun p : (Fin n → G) × G ↦ F (Fin.cons p.2 g)) :=
      F.isLocallyConstant.comp_continuous
        (continuous_snd.finCons (A := fun _ : Fin (n + 1) ↦ G) continuous_const)
    have heq : ∀ x ∈ (Set.univ : Set G),
        ∀ᶠ p : (Fin n → G) × G in nhds (g, x),
          F (Fin.cons p.2 p.1) = F (Fin.cons p.2 g) := by
      intro x _
      filter_upwards [hjoint.eventually_eq (g, x), hfixed.eventually_eq (g, x)]
        with p hp hq
      exact hp.trans hq.symm
    have huniform := IsCompact.eventually_forall_of_forall_eventually
      (isCompact_univ : IsCompact (Set.univ : Set G))
      (P := fun g' x ↦ F (Fin.cons x g') = F (Fin.cons x g)) heq
    filter_upwards [huniform] with g' hg'
    exact LocallyConstant.ext fun x ↦ congrArg (fun f ↦ f 1) (hg' x (Set.mem_univ x))
  refine ⟨{ toFun := fun F ↦ ⟨hF F, hlc F⟩
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro F H
    apply LocallyConstant.ext
    intro g
    apply LocallyConstant.ext
    intro x
    rfl
  · intro a F
    apply LocallyConstant.ext
    intro g
    apply LocallyConstant.ext
    intro x
    rfl
  · intro F g x
    rfl

end Rep
