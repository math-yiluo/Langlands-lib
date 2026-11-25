/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.DiscreteModulesAbelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.RepresentationTheory.Continuous.ContinuousCochainsShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Continuous cochain delta-functor

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-delta-functor).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section Construction

open ZeroObject

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {A : Type v} [Ring A] [Finite A]

private theorem action_continuous
    (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
    (c : @ContinuousMap (Fin n → G) M.obj.V _ ⊥) :
    @Continuous _ M.obj.V _ ⊥ (fun g : Fin (n + 1) → G ↦
      M.obj.ρ (g 0) (c (fun i ↦ g i.succ))) := by
  letI : TopologicalSpace M.obj.V := ⊥
  letI : DiscreteTopology M.obj.V := ⟨rfl⟩
  letI : MulAction G M.obj.V :=
    { smul := fun a x ↦ M.obj.ρ a x
      one_smul := by intro x; change M.obj.ρ 1 x = x; rw [map_one]; rfl
      mul_smul := by
        intro a b x
        change M.obj.ρ (a * b) x = M.obj.ρ a (M.obj.ρ b x)
        rw [map_mul]
        rfl }
  haveI : ContinuousSMul G M.obj.V :=
    continuousSMul_iff_stabilizer_isOpen.mpr M.property
  exact continuous_smul.comp ((continuous_apply 0).prodMk
    (c.continuous.comp (continuous_pi fun i ↦ continuous_apply i.succ)))

private local instance ccTopology (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    TopologicalSpace M.obj.V := ⊥

private local instance ccDiscreteTopology (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    DiscreteTopology M.obj.V := ⟨rfl⟩

private local instance ccContinuousConstSMul (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    ContinuousConstSMul A M.obj.V := ⟨fun _ ↦ continuous_of_discreteTopology⟩

private local instance ccContinuousConstZSMul (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    ContinuousConstSMul ℤ M.obj.V := ⟨fun _ ↦ continuous_of_discreteTopology⟩

private noncomputable def ccD
    (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ) :
    C(Fin n → G, M.obj.V) →ₗ[A] C(Fin (n + 1) → G, M.obj.V) where
  toFun c := ⟨fun g ↦ M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) • c (Fin.contractNth k (· * ·) g), by
    apply Continuous.add (action_continuous M n c)
    apply continuous_finsetSum
    intro k hk
    apply Continuous.const_smul (c := ((-1 : ℤ) ^ (k.val + 1)))
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
    simp [Finset.smul_sum, smul_add, smul_comm a]

private theorem ccD_sq
    [Abelian (DiscreteContinuousRep.{v, u, max u w} A G)]
    (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
    (c : C(Fin n → G, M.obj.V)) : ccD M (n + 1) (ccD M n c) = 0 := by
  let S : ShortComplex (DiscreteContinuousRep.{v, u, max u w} A G) :=
    ShortComplex.mk (𝟙 M) (0 : M ⟶ 0) (by simp)
  have hs : S.ShortExact :=
    (ShortComplex.Splitting.ofIsIsoOfIsZero S (by dsimp [S]; infer_instance)
      (isZero_zero _)).shortExact
  obtain ⟨K, e, i, p, hip, hK, _, _, _, hd⟩ := continuousCochains_shortExact G A S hs
  have hdiff : ∀ n x,
      e 0 (n + 1) ((K 0).d n (n + 1) x) = ccD M n (e 0 n x) := by
    intro n x
    ext g
    exact hd 0 n x g
  rw [← (e 0 n).apply_symm_apply c, ← hdiff, ← hdiff]
  have hz := congrArg (fun f ↦ f.hom ((e 0 n).symm c))
    ((K 0).d_comp_d n (n + 1) (n + 2))
  change (K 0).d (n + 1) (n + 2) ((K 0).d n (n + 1) ((e 0 n).symm c)) = 0 at hz
  rw [hz, map_zero]

variable [Abelian (DiscreteContinuousRep.{v, u, max u w} A G)]

private noncomputable abbrev ccComplex
    (M : DiscreteContinuousRep.{v, u, max u w} A G) :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A C(Fin n → G, M.obj.V))
    (fun n ↦ ModuleCat.ofHom (ccD M n)) (fun n ↦ by
      ext c g
      exact DFunLike.congr_fun (ccD_sq M n c) g)

private noncomputable abbrev ccMap
    {M N : DiscreteContinuousRep.{v, u, max u w} A G} (f : M ⟶ N) :
    ccComplex M ⟶ ccComplex N :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom
      { toFun := fun c ↦ ⟨fun g ↦ f.hom.hom (c g),
          continuous_of_discreteTopology.comp c.continuous⟩
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }) (fun n ↦ by
      ext c g
      simp only [ccComplex, CochainComplex.of_d]
      change N.obj.ρ (g 0) (f.hom.hom (c (fun i ↦ g i.succ))) +
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
          f.hom.hom (c (Fin.contractNth k (· * ·) g)) =
        f.hom.hom (M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
          ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
            c (Fin.contractNth k (· * ·) g))
      simp [map_add, map_sum, map_zsmul, Rep.hom_comm_apply])

private noncomputable abbrev ccFunctor :
    DiscreteContinuousRep.{v, u, max u w} A G ⥤
      CochainComplex (ModuleCat.{max u w} A) ℕ where
  obj := ccComplex
  map := ccMap
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    ext c g
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    ext c t
    rfl

end Construction

/-- Continuous inhomogeneous cochains form a cohomological delta-functor.

Proof: Construct each term as the module of continuous maps to the discrete coefficient
module. The action, projections and adjacent multiplication preserve continuity, and
expanding two differentials cancels the terms in pairs. Postcomposition by equivariant
linear maps commutes with the differential and gives a functor. The short exactness theorem
`lem-exc-continuous-cochains-short-exact` applies to these complexes: transport its maps
along their term equivalences. The homology long exact sequence and its naturality give
all the delta-functor axioms, including additivity and the initial monomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology; final profinite comparison via coinduction.
(blueprint: lem-exc-continuous-cochains-delta-functor). -/
theorem continuousCochains_deltaFunctor
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
        ∃ T : CohomologicalDeltaFunctor
            (DiscreteContinuousRep.{v, u, max u w} A G) (ModuleCat.{max u w} A),
          T.F = (fun q ↦ F ⋙ HomologicalComplex.homologyFunctor
            (ModuleCat.{max u w} A) (ComplexShape.up ℕ) q) := by
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
  let F := ccFunctor (G := G) (A := A)
  let U := ObjectProperty.ι (fun X : Rep.{max u w} A G ↦
    ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) ⋙
    forget₂ (Rep.{max u w} A G) (ModuleCat.{max u w} A)
  haveI : PreservesFiniteLimits U := (Classical.choose_spec
    (discreteModules_abelian.{u, v, max u w} G A)).choose_spec.2.1
  haveI : U.Additive := Functor.additive_of_preserves_binary_products U
  haveI : F.Additive := by
    constructor
    intro M N f g
    apply HomologicalComplex.hom_ext
    intro n
    ext c t
    exact congrArg (fun k ↦ k.hom (c t)) (Functor.map_add U (f := f) (g := g))
  letI : HasZeroMorphisms (DiscreteContinuousRep.{v, u, max u w} A G) :=
    Preadditive.preadditiveHasZeroMorphisms
  have hshort := continuousCochains_shortExact.{u, v, max u w} G A
  have hz : ObjectProperty.instHasZeroMorphismsFullSubcategory
      (fun X : Rep.{max u w} A G ↦ ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) =
      (Preadditive.preadditiveHasZeroMorphisms :
        HasZeroMorphisms (DiscreteContinuousRep.{v, u, max u w} A G)) :=
    Subsingleton.elim _ _
  rw [hz] at hshort
  have hs (S : ShortComplex (DiscreteContinuousRep.{v, u, max u w} A G))
      (hS : S.ShortExact) (n : ℕ) :
      ((S.map F).map (HomologicalComplex.eval
        (ModuleCat.{max u w} A) (ComplexShape.up ℕ) n)).ShortExact := by
    obtain ⟨K, e, i, p, hip, hK, _, hi, hp, _⟩ :=
      hshort S hS
    let L := ShortComplex.mk i p hip
    let R := (S.map F).map (HomologicalComplex.eval
      (ModuleCat.{max u w} A) (ComplexShape.up ℕ) n)
    have hL : (L.map (HomologicalComplex.eval
        (ModuleCat.{max u w} A) (ComplexShape.up ℕ) n)).ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact L).mp hK n
    apply ShortComplex.shortExact_of_iso (S₁ := L.map
      (HomologicalComplex.eval (ModuleCat.{max u w} A) (ComplexShape.up ℕ) n))
      (S₂ := R) _ hL
    exact ShortComplex.isoMk (e 0 n).toModuleIso (e 1 n).toModuleIso
      (e 2 n).toModuleIso (by
        ext x
        exact ContinuousMap.ext (fun t ↦ (hi n x t).symm)) (by
        ext x
        exact ContinuousMap.ext (fun t ↦ (hp n x t).symm))
  have hse (S : ShortComplex (DiscreteContinuousRep.{v, u, max u w} A G))
      (hS : S.ShortExact) : (S.map F).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (hs S hS)
  let T : CohomologicalDeltaFunctor
      (DiscreteContinuousRep.{v, u, max u w} A G) (ModuleCat.{max u w} A) :=
    { F := fun q ↦ F ⋙ HomologicalComplex.homologyFunctor _ _ q
      additive := fun _ ↦ inferInstance
      delta := fun S hS n ↦ (hse S hS).δ n (n + 1) rfl
      mono_zero := by
        intro S hS
        haveI : Mono ((F.map S.f).f 0) := (hs S hS 0).mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          (F.map S.f) 0 (by
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
          (F.mapShortComplex.map φ) (hse S hS) (hse R hR) n (n + 1) rfl }
  refine ⟨F, fun M n ↦ LinearEquiv.refl A _, ?_, ?_, T, rfl⟩
  · intro M N f n x g
    rfl
  · intro M n x g
    change (((ccComplex M).d n (n + 1)) x) g = _
    simp only [ccComplex, CochainComplex.of_d]
    rfl

end Rep
