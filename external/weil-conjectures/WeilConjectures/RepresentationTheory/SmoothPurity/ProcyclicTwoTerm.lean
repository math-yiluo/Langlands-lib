/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.SmoothPurity.DiscreteContinuousCohomology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Intervals
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import WeilConjectures.RepresentationTheory.Coinduced.CoinducedDiscreteEmbedding
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsInvariantsZero
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Two-term continuous cohomology of the additive l-adic integers

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
statement and proof (blueprint: lem-exc-procyclic-two-term).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

section

open ZeroObject

set_option linter.style.haveILetI false

open scoped BigOperators
open Topology

private theorem sum_periods {V : Type*} [AddCommGroup V] (f : ℕ → V)
    (L : ℕ) (hf : Function.Periodic f L) (k : ℕ) :
    ∑ i ∈ Finset.range (k * L), f i = k • ∑ i ∈ Finset.range L, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simpa [Nat.add_comm] using (hf.nat_mul k) i

namespace Rep

private theorem universalDeltaFunctor_iso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (T R : CohomologicalDeltaFunctor C D) (hT : T.IsUniversal) (hR : R.IsUniversal)
    (e : T.F 0 ≅ R.F 0) (q : ℕ) : Nonempty (T.F q ≅ R.F q) := by
  obtain ⟨α, hα, _⟩ := hT R e.hom
  obtain ⟨β, hβ, _⟩ := hR T e.inv
  let idT : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ 𝟙 (T.F n), by intros; simp⟩
  let idR : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ 𝟙 (R.F n), by intros; simp⟩
  let αβ : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ α.app n ≫ β.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [α.naturality S hS n]
      simp only [Category.assoc]
      rw [β.naturality S hS n]⟩
  let βα : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ β.app n ≫ α.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [β.naturality S hS n]
      simp only [Category.assoc]
      rw [α.naturality S hS n]⟩
  have hαβ : αβ = idT := (hT T (𝟙 (T.F 0))).unique
    (by change α.app 0 ≫ β.app 0 = _; rw [hα, hβ]; exact e.hom_inv_id)
    rfl
  have hβα : βα = idR := (hR R (𝟙 (R.F 0))).unique
    (by change β.app 0 ≫ α.app 0 = _; rw [hβ, hα]; exact e.inv_hom_id)
    rfl
  refine ⟨⟨α.app q, β.app q, ?_, ?_⟩⟩
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom T T ↦ f.app q) hαβ
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom R R ↦ f.app q) hβα

variable {A : Type u} [Ring A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
private noncomputable abbrev ttX (M : DiscreteContinuousRep.{u, 0, w} A G) : ℕ → ModuleCat.{w} A
  | 0 => ModuleCat.of A M.obj.V
  | 1 => ModuleCat.of A M.obj.V
  | _ + 2 => 0
private noncomputable abbrev ttD (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G) :
    ∀ n, ttX M n ⟶ ttX M (n + 1)
  | 0 => ModuleCat.ofHom (M.obj.ρ τ - LinearMap.id)
  | 1 => 0
  | _ + 2 => 0
private noncomputable abbrev ttComplex (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G) :
    CochainComplex (ModuleCat.{w} A) ℕ :=
  CochainComplex.of (ttX M) (ttD τ M) (by
    intro n
    cases n with
    | zero => exact comp_zero
    | succ n => cases n <;> exact zero_comp)
private noncomputable def ttMap (τ : G) {M N : DiscreteContinuousRep.{u, 0, w} A G} (f : M ⟶ N) :
    ttComplex τ M ⟶ ttComplex τ N :=
  CochainComplex.ofHom (fun n ↦ match n with
    | 0 => ModuleCat.ofHom f.hom.hom
    | 1 => ModuleCat.ofHom f.hom.hom
    | _ + 2 => 0) (by
      intro n
      cases n with
      | zero =>
        simp only [ttComplex, CochainComplex.of_d]
        ext x
        change N.obj.ρ τ (f.hom.hom x) - f.hom.hom x =
          f.hom.hom (M.obj.ρ τ x - x)
        rw [map_sub, Rep.hom_comm_apply]
      | succ n => cases n <;> simp only [ttComplex, CochainComplex.of_d, ttD,
          comp_zero])
private noncomputable def ttFunctor (τ : G) : DiscreteContinuousRep.{u, 0, w} A G ⥤
    CochainComplex (ModuleCat.{w} A) ℕ where
  obj := ttComplex τ
  map := ttMap τ
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact (isZero_zero _).eq_of_src _ _
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact (isZero_zero _).eq_of_src _ _

private noncomputable abbrev ttForget : DiscreteContinuousRep.{u, 0, w} A G ⥤
    ModuleCat.{w} A :=
  ObjectProperty.ι (fun X : Rep.{w} A G ↦ ∀ m : X.V, IsOpen {g | X.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)

private local instance ttPreadditive
    [h : Abelian (DiscreteContinuousRep.{u, 0, w} A G)] :
    Preadditive (DiscreteContinuousRep.{u, 0, w} A G) := h.toPreadditive

private local instance ttModulePreadditive : Preadditive (ModuleCat.{w} A) :=
  (inferInstance : Abelian (ModuleCat.{w} A)).toPreadditive

attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

attribute [local instance 3000] ttPreadditive ttModulePreadditive

private local instance ttAdditive
    [Abelian (DiscreteContinuousRep.{u, 0, w} A G)]
    [PreservesFiniteLimits (ttForget.{u, w} (A := A) (G := G))] (τ : G) :
    (ttFunctor (A := A) τ).Additive := by
  haveI : (ttForget.{u, w} (A := A) (G := G)).Additive :=
    Functor.additive_of_preserves_binary_products _
  constructor
  intro M N f g
  apply HomologicalComplex.hom_ext
  intro n
  match n with
  | 0 => exact Functor.map_add (ttForget.{u, w} (A := A) (G := G))
  | 1 => exact Functor.map_add (ttForget.{u, w} (A := A) (G := G))
  | n + 2 => exact (isZero_zero _).eq_of_src _ _

end Rep

end

namespace Rep

end Rep
