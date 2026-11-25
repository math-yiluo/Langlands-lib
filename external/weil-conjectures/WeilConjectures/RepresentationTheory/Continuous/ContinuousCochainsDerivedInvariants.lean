/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.DiscreteModulesAbelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.RepresentationTheory.Coinduced.CoinducedContinuousAcyclic
import WeilConjectures.RepresentationTheory.Coinduced.CoinducedDiscreteEmbedding
import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsDeltaFunctor
import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsInvariantsZero

/-!
# Continuous inhomogeneous cochains compute derived invariants

Source: Stacks Project, Etale Cohomology, Section 59.58, Tag 0DVG
(blueprint: lem-exc-cochains-derived-invariants).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private def continuousLocallyConstantEquiv
    (A X Y : Type*) [Ring A] [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup Y] [Module A Y] [DiscreteTopology Y] [ContinuousConstSMul A Y] :
    C(X, Y) ≃ₗ[A] LocallyConstant X Y where
  toFun f := ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.continuous⟩
  invFun f := ⟨f, f.isLocallyConstant.continuous⟩
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' f g := by ext; rfl
  map_smul' a f := by ext; rfl

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

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
/-- Continuous inhomogeneous cochains compute the right derived functors of invariants.
The existential complex is specified by linear equivalences of its terms with continuous
maps from `G^n` to the discrete module, its maps on coefficients, and its inhomogeneous
differential; thus it is the usual complex up to natural termwise linear equivalence.
The term of the sum indexed by `Fin.last n` omits the last argument; the other terms
multiply adjacent arguments. In degree zero the formula is `g • m - m`.

Proof, following the DAG: degreewise exactness
(`lem-exc-continuous-cochains-short-exact`), the long exact homology sequence
(`lem-weil-pbc-complex-ses-homology-long-exact`) and its naturality
(`lem-weil-pbc-complex-ses-long-exact-naturality`) give a cohomological delta-functor
(`def-weil-pbc-delta-functor`). Its zeroth term is invariants; invariants are additive
and left exact by `lem-exc-discrete-modules-abelian`. The embedding into continuous
coinduction (`lem-exc-coinduced-discrete-embedding`) and its positive-degree acyclicity
(`lem-exc-coinduced-continuous-acyclic`) efface every positive-degree cochain cohomology.
Apply `lem-weil-pbc-effaceable-delta-functor-universal`. Enough injectives and
`lem-weil-pbc-right-derived-universal-delta-functor` give universality of derived
invariants. The two universal delta-functors extend the identity in degree zero in
both directions; uniqueness makes their composites identities, giving natural
isomorphisms in every degree.

Source: Stacks Project, Etale Cohomology, Section 59.58, Tag 0DVG, displayed
inhomogeneous differential and final profinite comparison
(blueprint: lem-exc-cochains-derived-invariants). -/
theorem continuousCochains_derived_invariants
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
    letI : Preadditive (ModuleCat.{max u w} A) :=
      (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
    letI := (Classical.choose_spec
      (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
      fun _ ↦ ⊥
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
      fun _ ↦ ⟨rfl⟩
    letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        ContinuousConstSMul A M.obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    let S := fun M : DiscreteContinuousRep.{v, u, max u w} A G =>
      ⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id)
    ∃ V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A,
      ∃ a : V.Additive,
        letI instAdditive : V.Additive := a
        ∃ t : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
            V.obj M ≃ₗ[A] S M,
          (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
            (x : V.obj M),
            (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) ∧
          ∃ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
              CochainComplex (ModuleCat.{max u w} A) ℕ,
            ∃ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
              (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
              (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
                (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
                e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) ∧
              (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
                (x : (F.obj M).X n) (g : Fin (n + 1) → G),
                e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
                  M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
                    ∑ k : Fin (n + 1),
                      (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) ∧
              ∀ q : ℕ, Nonempty ((@Functor.rightDerived _ _ _ _ h _ _ V a q) ≅
                F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
                  (ComplexShape.up ℕ) q) := by
  classical
  dsimp only
  let h := Classical.choose (discreteModules_abelian.{u, v, max u w} G A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := h.toPreadditive
  letI : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  letI := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.1
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, TopologicalSpace M.obj.V :=
    fun _ ↦ ⊥
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  letI : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
      ContinuousConstSMul A M.obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  obtain ⟨F, e, hmap, hd, T, hTF⟩ :=
    continuousCochains_deltaFunctor.{u, v, w} G A
  obtain ⟨V, a, t, ht, hlim, ⟨hzero⟩⟩ :=
    continuousCochains_invariants_zero.{u, v, w} G A F e hmap hd
  letI : V.Additive := a
  letI : PreservesFiniteLimits V := hlim
  obtain ⟨R, hRF, hR, ⟨hRzero⟩⟩ := V.exists_universal_rightDerived_deltaFunctor
  have hTuniv : T.IsUniversal := by
    apply effaceable_deltaFunctor_isUniversal
    intro q hq M
    obtain ⟨D, eD, ι, hD, _, _, hinj⟩ :=
      exists_coinduced_discrete_embedding.{u, v, w} G A
    have hm : Mono (ι.app M) := by
      constructor
      intro Z f g hfg
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply hinj M
      exact congrArg (fun k ↦ k.hom.hom x) hfg
    refine ⟨D.obj M, ι.app M, hm, ?_⟩
    have hz := coinducedContinuousCochains_isZero.{u, v, max u w} G A M (D.obj M)
      (eD M) (hD M) (F.obj (D.obj M))
      (fun n ↦ (e (D.obj M) n).trans
        (continuousLocallyConstantEquiv A (Fin n → G) (D.obj M).obj.V))
      (hd (D.obj M)) q hq
    rw [hTF]
    exact hz.eq_of_tgt _ _
  have hTzero : T.F 0 ≅ V := by
    rw [hTF]
    exact hzero
  have hRzero' : R.F 0 ≅ V := by
    rw [hRF]
    exact hRzero
  refine ⟨V, a, t, ht, F, e, hmap, hd, ?_⟩
  intro q
  obtain ⟨eqiso⟩ := universalDeltaFunctor_iso T R hTuniv hR
    (hTzero ≪≫ hRzero'.symm) q
  rw [hTF, hRF] at eqiso
  exact ⟨eqiso.symm⟩

end Rep
