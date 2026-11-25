/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.RepresentationTheory.SmoothPurity.DiscreteRep
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.ULift
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Short exact sequences of continuous inhomogeneous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG, section continuous-group-cohomology
(blueprint: lem-exc-continuous-cochains-short-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

private theorem cochain_action_continuous
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v} [Ring A] (M : DiscreteContinuousRep.{v, u, w} A G)
    [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
    (n : ℕ) (c : C((Fin n → G), M.obj.V)) :
    Continuous (fun g : Fin (n + 1) → G ↦
      M.obj.ρ (g 0) (c (fun i ↦ g i.succ))) := by
  let : MulAction G M.obj.V :=
    { smul := fun a x ↦ M.obj.ρ a x
      one_smul := by intro x; change M.obj.ρ 1 x = x; rw [map_one]; rfl
      mul_smul := by
        intro a b x
        change M.obj.ρ (a * b) x = M.obj.ρ a (M.obj.ρ b x)
        rw [map_mul]
        rfl }
  have : ContinuousSMul G M.obj.V :=
    continuousSMul_iff_stabilizer_isOpen.mpr M.property
  exact continuous_smul.comp ((continuous_apply 0).prodMk
    (c.continuous.comp (continuous_pi fun i ↦ continuous_apply i.succ)))

private noncomputable def cochainD
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v} [Ring A] (M : DiscreteContinuousRep.{v, u, w} A G)
    [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
    [ContinuousConstSMul A M.obj.V] (n : ℕ) :
    C((Fin n → G), M.obj.V) →ₗ[A] C((Fin (n + 1) → G), M.obj.V) where
  toFun c := ⟨fun g ↦ M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) • c (Fin.contractNth k (· * ·) g), by
    apply Continuous.add (cochain_action_continuous M n c)
    apply continuous_finsetSum
    intro k hk
    apply (continuous_of_discreteTopology
      (f := fun x : M.obj.V ↦ (-1 : ℤ) ^ (k.val + 1) • x)).comp
    apply c.continuous.comp
    apply continuous_pi
    intro i
    unfold Fin.contractNth
    split_ifs
    · exact continuous_apply _
    · exact (continuous_apply _).mul (continuous_apply _)
    · exact continuous_apply _⟩
  map_add' c d := by
    ext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' a c := by
    ext g
    simp [Finset.smul_sum, smul_comm a]

private theorem cochainD_sq
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v} [Ring A] (M : DiscreteContinuousRep.{v, u, w} A G)
    [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
    [ContinuousConstSMul A M.obj.V] (n : ℕ)
    (c : C((Fin n → G), M.obj.V)) : cochainD M (n + 1) (cochainD M n c) = 0 := by
  let R := ULift.{max u w} ℤ
  let H := ULift.{w} G
  let W := ULift.{u} M.obj.V
  let ρ : Representation R H W :=
    { toFun := fun g ↦
        { toFun := fun x ↦ ULift.up (M.obj.ρ g.down x.down)
          map_add' := by intro x y; apply ULift.ext; exact map_add _ _ _
          map_smul' := by
            intro a x
            apply ULift.ext
            exact map_zsmul (M.obj.ρ g.down) a.down x.down }
      map_one' := by
        ext x
        change M.obj.ρ 1 x.down = x.down
        simp
      map_mul' := by
        intro g h
        ext x
        change M.obj.ρ (g.down * h.down) x.down =
          M.obj.ρ g.down (M.obj.ρ h.down x.down)
        rw [map_mul]
        rfl }
  let B : Rep.{max u w} R H := Rep.of ρ
  let L (n : ℕ) (c : C((Fin n → G), M.obj.V)) : (Fin n → H) → W :=
    fun g ↦ ULift.up (c (fun i ↦ (g i).down))
  have hd : ∀ n c, L (n + 1) (cochainD M n c) =
      inhomogeneousCochains.d B n (L n c) := by
    intro n c
    funext g
    apply ULift.ext
    have hc : ∀ k : Fin (n + 1),
        (fun i ↦ (Fin.contractNth k (· * ·) g i).down) =
          Fin.contractNth k (· * ·) (fun i ↦ (g i).down) := by
      intro k
      funext i
      unfold Fin.contractNth
      split_ifs <;> rfl
    have hdown (f : Fin (n + 1) → W) :
        (∑ k, f k).down = ∑ k, (f k).down :=
      map_sum (ULift.moduleEquiv : W ≃ₗ[ℤ] M.obj.V) f Finset.univ
    simp only [L, cochainD, inhomogeneousCochains.d,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk]
    change _ = ((M.obj.ρ (g 0).down (c (fun i ↦ (g i.succ).down)) |> ULift.up) +
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k.val + 1)) •
        (ULift.up (c (fun i ↦ (Fin.contractNth k (· * ·) g i).down)) : W)).down
    rw [ULift.add_down, hdown]
    simp [ULift.smul_def, R, hc]
  have hs := groupCohomology.inhomogeneousCochains.d_comp_d n B
  have hz := congrArg (fun f ↦ f (L n c)) hs
  change inhomogeneousCochains.d B (n + 1)
    (inhomogeneousCochains.d B n (L n c)) = 0 at hz
  rw [← hd, ← hd] at hz
  ext g
  have hh := congrArg (fun f ↦ (f (fun i ↦ ULift.up (g i))).down) hz
  exact hh

private noncomputable abbrev cochainComplex
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v} [Ring A] (M : DiscreteContinuousRep.{v, u, w} A G)
    [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
    [ContinuousConstSMul A M.obj.V] :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (C((Fin n → G), M.obj.V)))
    (fun n ↦ ModuleCat.ofHom (cochainD M n)) (fun n ↦ by
      ext c g
      exact DFunLike.congr_fun (cochainD_sq M n c) g)

private noncomputable abbrev cochainMap
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type v} [Ring A] {M N : DiscreteContinuousRep.{v, u, w} A G}
    [TopologicalSpace M.obj.V] [DiscreteTopology M.obj.V]
    [ContinuousConstSMul A M.obj.V]
    [TopologicalSpace N.obj.V] [DiscreteTopology N.obj.V]
    [ContinuousConstSMul A N.obj.V] (f : M ⟶ N) :
    cochainComplex M ⟶ cochainComplex N :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom
      { toFun := fun c ↦ ⟨fun g ↦ f.hom.hom (c g),
          continuous_of_discreteTopology.comp c.continuous⟩
        map_add' := by intro c d; ext g; exact map_add f.hom.hom _ _
        map_smul' := by intro a c; ext g; exact map_smul f.hom.hom a (c g) }) (fun n ↦ by
      ext c g
      simp only [cochainComplex, CochainComplex.of_d]
      change N.obj.ρ (g 0) (f.hom.hom (c (fun i ↦ g i.succ))) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
          f.hom.hom (c (Fin.contractNth k (· * ·) g)) =
        f.hom.hom (M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
          ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
            c (Fin.contractNth k (· * ·) g))
      simp [map_add, map_sum, map_zsmul, Rep.hom_comm_apply])

/-- Continuous inhomogeneous cochains carry a short exact sequence of discrete continuous
representations to a short exact sequence of complexes. The equivalences `e` identify
complex terms with continuous maps, and specify both differentials and postcomposition maps.
The final term of the sum, indexed by `Fin.last n`, omits the last argument; the other terms
multiply adjacent arguments. At `n = 0` the formula is `g • m - m`.

Proof: (1) Underlying module exactness follows from `lem-exc-discrete-modules-abelian`.
Postcomposition with the injection is injective. A cochain in the kernel has a unique
pointwise preimage, continuous since inverse images of singletons are open. A set-theoretic
section of the surjection is continuous between discrete modules and lifts every cochain.
(2) Projections, adjacent multiplication and the action are continuous; the displayed
alternating sum therefore defines a continuous linear differential. Expanding two successive
differentials cancels all terms in pairs, using associativity and the action law, including
in degree zero. (3) Equivariant linear maps commute with each term of the differential,
so postcomposition gives cochain maps. Degreewise exactness gives short exactness of complexes
by `lem-weil-pbc-cochain-complexes-degreewise-exact`.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential and paragraph
beginning "However, a short exact sequence of discrete G-modules"
(blueprint: lem-exc-continuous-cochains-short-exact). -/
theorem continuousCochains_shortExact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (S : ShortComplex (DiscreteContinuousRep.{v, u, w} A G)) :
    S.ShortExact →
    let X : Fin 3 → DiscreteContinuousRep.{v, u, w} A G := ![S.X₁, S.X₂, S.X₃]
    letI : ∀ j : Fin 3, TopologicalSpace (X j).obj.V := fun _ ↦ ⊥
    letI : ∀ j : Fin 3, DiscreteTopology (X j).obj.V := fun _ ↦ ⟨rfl⟩
    letI : ∀ j : Fin 3, ContinuousConstSMul A (X j).obj.V :=
      fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
    ∃ (K : Fin 3 → CochainComplex (ModuleCat.{max u w} A) ℕ)
      (e : ∀ (j : Fin 3) (n : ℕ),
        (K j).X n ≃ₗ[A] C((Fin n → G), (X j).obj.V))
      (i : K 0 ⟶ K 1) (p : K 1 ⟶ K 2) (hip : i ≫ p = 0),
      (ShortComplex.mk i p hip).ShortExact ∧
      (∀ n : ℕ, Function.Injective (i.f n) ∧
        Set.range (i.f n) = {x | p.f n x = 0} ∧ Function.Surjective (p.f n)) ∧
      (∀ (n : ℕ) (f : (K 0).X n) (g : Fin n → G),
        e 1 n (i.f n f) g = S.f.hom.hom (e 0 n f g)) ∧
      (∀ (n : ℕ) (f : (K 1).X n) (g : Fin n → G),
        e 2 n (p.f n f) g = S.g.hom.hom (e 1 n f g)) ∧
      (∀ (j : Fin 3) (n : ℕ) (f : (K j).X n) (g : Fin (n + 1) → G),
        e j (n + 1) ((K j).d n (n + 1) f) g =
          (X j).obj.ρ (g 0) (e j n f (fun k ↦ g k.succ)) +
            ∑ k : Fin (n + 1),
              (-1 : ℤ) ^ (k.val + 1) • e j n f (Fin.contractNth k (· * ·) g)) := by
  classical
  intro hS
  -- Destruct the abelian structure before introducing the dependent cochain data.
  let F := ObjectProperty.ι (fun M : Rep.{w} A G ↦
    ∀ m : M.V, IsOpen {g : G | M.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
  obtain ⟨h, ha, hl, hc, he⟩ := discreteRep_abelian_structure A G
  let := h
  have : F.Additive := ha
  have := hl
  have := hc
  have hT : (S.map F).ShortExact := by
    have : Mono S.f := hS.mono_f
    have : Epi S.g := hS.epi_g
    refine ShortComplex.ShortExact.mk' ((he S).mp hS.exact) ?_ ?_
    · change Mono (F.map S.f)
      infer_instance
    · change Epi (F.map S.g)
      infer_instance
  have hf : Function.Injective S.f.hom.hom := hT.moduleCat_injective_f
  have hg : Function.Surjective S.g.hom.hom := hT.moduleCat_surjective_g
  have hex : ∀ y : S.X₂.obj.V, S.g.hom.hom y = 0 →
      ∃ x : S.X₁.obj.V, S.f.hom.hom x = y :=
    (ShortComplex.moduleCat_exact_iff (S.map F)).mp hT.exact
  dsimp only
  let X : Fin 3 → DiscreteContinuousRep.{v, u, w} A G := ![S.X₁, S.X₂, S.X₃]
  let : ∀ j : Fin 3, TopologicalSpace (X j).obj.V := fun _ ↦ ⊥
  let : ∀ j : Fin 3, DiscreteTopology (X j).obj.V := fun _ ↦ ⟨rfl⟩
  let : ∀ j : Fin 3, ContinuousConstSMul A (X j).obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let : TopologicalSpace S.X₁.obj.V := ⊥
  let : TopologicalSpace S.X₂.obj.V := ⊥
  let : TopologicalSpace S.X₃.obj.V := ⊥
  have : DiscreteTopology S.X₁.obj.V := ⟨rfl⟩
  have : DiscreteTopology S.X₂.obj.V := ⟨rfl⟩
  have : DiscreteTopology S.X₃.obj.V := ⟨rfl⟩
  let K (j : Fin 3) := cochainComplex (X j)
  let i : K 0 ⟶ K 1 := cochainMap S.f
  let p : K 1 ⟶ K 2 := cochainMap S.g
  have hip : i ≫ p = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    ext c g
    change S.g.hom.hom (S.f.hom.hom (c g)) = 0
    have h := congrArg (fun f ↦ f.hom.hom (c g)) S.zero
    exact h
  let T := ShortComplex.mk i p hip
  have hn : ∀ n : ℕ, Function.Injective (i.f n) ∧
      Set.range (i.f n) = {x | p.f n x = 0} ∧ Function.Surjective (p.f n) := by
    intro n
    refine ⟨?_, ?_, ?_⟩
    · intro c d hcd
      ext g
      apply hf
      exact congrArg (fun f ↦ f g) hcd
    · ext c
      constructor
      · rintro ⟨d, rfl⟩
        change p.f n (i.f n d) = 0
        ext g
        exact congrArg (fun f ↦ f.hom.hom (d g)) S.zero
      · intro hc
        let lift : S.X₂.obj.V → S.X₁.obj.V :=
          fun y ↦ if hy : S.g.hom.hom y = 0 then Classical.choose (hex y hy) else 0
        let d : C((Fin n → G), (X 0).obj.V) :=
          ⟨fun g ↦ lift (c g), (continuous_of_discreteTopology (f := lift)).comp c.continuous⟩
        refine ⟨d, ?_⟩
        ext g
        have hy : S.g.hom.hom (c g) = 0 := congrArg (fun f ↦ f g) hc
        change S.f.hom.hom (lift (c g)) = c g
        simp only [lift, dite_eq_left hy]
        exact Classical.choose_spec (hex _ hy)
    · intro c
      let d : C((Fin n → G), (X 1).obj.V) :=
        ⟨fun g ↦ Function.surjInv hg (c g),
          (continuous_of_discreteTopology (f := Function.surjInv hg)).comp c.continuous⟩
      refine ⟨d, ?_⟩
      ext g
      exact Function.surjInv_eq hg (c g)
  have hs : T.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let U := T.map (HomologicalComplex.eval (ModuleCat.{max u w} A)
      (ComplexShape.up ℕ) n)
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · apply (ShortComplex.moduleCat_exact_iff U).mpr
      intro c hc
      have hh : c ∈ Set.range (i.f n) := by
        rw [(hn n).2.1]
        exact hc
      exact hh
    · exact (ModuleCat.mono_iff_injective U.f).mpr (hn n).1
    · exact (ModuleCat.epi_iff_surjective U.g).mpr (hn n).2.2
  refine ⟨K, fun j n ↦ LinearEquiv.refl A _, i, p, hip, hs, hn, ?_, ?_, ?_⟩
  · intro n c g
    rfl
  · intro n c g
    rfl
  · intro j n c g
    change (((cochainComplex (X j)).d n (n + 1)) c) g = _
    simp only [cochainComplex, CochainComplex.of_d]
    rfl

end Rep
