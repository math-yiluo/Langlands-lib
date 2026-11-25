/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.DiscreteModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Degree-zero cochains and invariants

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology (blueprint: lem-exc-continuous-cochains-invariants-zero).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

section InvariantsFunctor

variable (A : Type v) [Ring A] (G : Type u) [Group G]

/-- Membership in the submodule `⨅ g, ker (ρ g - id)` of `G`-invariant vectors. -/
lemma mem_iInf_ker_sub_id {V : Type w} [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (x : V) :
    x ∈ ⨅ g : G, LinearMap.ker (ρ g - LinearMap.id) ↔ ∀ g, ρ g x = x := by
  simp [Submodule.mem_iInf, sub_eq_zero]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The functor of `G`-invariant vectors on discrete continuous representations over a
not necessarily commutative ring. -/
noncomputable def discreteInvariantsFunctor :
    DiscreteContinuousRep.{v, u, w} A G ⥤ ModuleCat.{w} A where
  obj M := ModuleCat.of A
    (⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id) : Submodule A M.obj.V)
  map {M N} f := ModuleCat.ofHom <|
    (f.hom.hom.toLinearMap ∘ₗ Submodule.subtype _).codRestrict _ fun x ↦ by
      rw [mem_iInf_ker_sub_id]
      intro g
      have hx := (mem_iInf_ker_sub_id A G M.obj.ρ x.1).1 x.2 g
      simp [← hom_comm_apply, hx]

variable [Small.{w} A]

/-- The trivial representation on (a shrunk copy of) `A`, which corepresents the invariants
functor. -/
noncomputable abbrev discreteTrivialUnit : DiscreteContinuousRep.{v, u, w} A G :=
  ⟨Rep.of (1 : Representation A G (Shrink.{w} A)), fun _ ↦ by simp⟩

/-- Invariant vectors of `M` correspond to morphisms from the trivial representation on `A`. -/
noncomputable def discreteInvariantsEquivHom (M : DiscreteContinuousRep.{v, u, w} A G) :
    (discreteInvariantsFunctor A G).obj M ≃ (discreteTrivialUnit A G ⟶ M) where
  toFun x := ⟨ConcreteCategory.ofHom (C := Rep.{w} A G)
    { toLinearMap := LinearMap.toSpanSingleton A M.obj.V x.1 ∘ₗ
        (Shrink.linearEquiv A A).toLinearMap
      isIntertwining' g := LinearMap.ext fun a ↦ by
        simp [(mem_iInf_ker_sub_id A G M.obj.ρ x.1).1 x.2 g] }⟩
  invFun f := ⟨f.hom.hom ((Shrink.linearEquiv A A).symm 1), by
    rw [mem_iInf_ker_sub_id]
    intro g
    rw [← hom_comm_apply]
    simp⟩
  left_inv x := Subtype.ext (by
    simp [-Shrink.linearEquiv_symm_apply, -Shrink.linearEquiv_apply])
  right_inv f := by
    refine InducedCategory.hom_ext (Rep.hom_ext ?_)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun a ↦ ?_)
    obtain ⟨b, rfl⟩ := (Shrink.linearEquiv A A).symm.surjective a
    conv_rhs => rw [← mul_one b, ← smul_eq_mul, LinearEquiv.map_smul]
    simp [-Shrink.linearEquiv_symm_apply, -Shrink.linearEquiv_apply]

/-- The invariants functor is corepresented by the trivial representation on `A`. -/
noncomputable def discreteInvariantsCoyonedaIso :
    discreteInvariantsFunctor A G ⋙ forget (ModuleCat.{w} A) ≅
      coyoneda.obj (Opposite.op (discreteTrivialUnit A G)) :=
  NatIso.ofComponents (fun M ↦ (discreteInvariantsEquivHom A G M).toIso) fun f ↦ by
    ext x
    refine InducedCategory.hom_ext (Rep.hom_ext ?_)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun a ↦ ?_)
    simp [discreteInvariantsFunctor, discreteInvariantsEquivHom]

instance : PreservesFiniteLimits (discreteInvariantsFunctor.{u, v, w} A G) := by
  have : PreservesLimits (discreteInvariantsFunctor.{u, v, w} A G ⋙ forget (ModuleCat.{w} A)) :=
    preservesLimits_of_natIso (discreteInvariantsCoyonedaIso A G).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{w} A))

/-- The invariants functor is additive for any preadditive structure with binary products on
the category of discrete representations, since it preserves finite limits. -/
lemma discreteInvariantsFunctor_additive [inst : Preadditive (DiscreteContinuousRep.{v, u, w} A G)]
    [HasZeroObject (DiscreteContinuousRep.{v, u, w} A G)]
    [HasBinaryProducts (DiscreteContinuousRep.{v, u, w} A G)] :
    (discreteInvariantsFunctor.{u, v, w} A G).Additive :=
  Functor.additive_of_preserves_binary_products _

end InvariantsFunctor

section CyclesZero

/-- A degree-zero cochain is determined by its value at the unique point. -/
lemma cochain_zero_ext {G V : Type*} [TopologicalSpace G] [TopologicalSpace V]
    {x y : C(Fin 0 → G, V)} (h : x default = y default) : x = y :=
  ContinuousMap.ext fun a ↦ by rwa [Subsingleton.elim a default]

variable {A : Type v} [Ring A] {G : Type u} [Group G] [TopologicalSpace G]
  {V : Type w} [AddCommGroup V] [Module A V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul A V] (ρ : Representation A G V)
  (K : CochainComplex (ModuleCat.{w} A) ℕ) (e₀ : K.X 0 ≃ₗ[A] C(Fin 0 → G, V))
  (e₁ : K.X 1 ≃ₗ[A] C(Fin 1 → G, V))

/-- The degree-zero cochain differential `m ↦ (g ↦ ρ(g) m - m)`, read through `e₀, e₁`. -/
lemma cochain_d_zero_apply
    (hd : ∀ (x : K.X 0) (g : Fin 1 → G), e₁ ((K.d 0 1).hom x) g =
      ρ (g 0) (e₀ x (fun k ↦ g k.succ)) +
        ∑ k : Fin 1, (-1 : ℤ) ^ (k.val + 1) • e₀ x (Fin.contractNth k (· * ·) g))
    (x : K.X 0) (g : Fin 1 → G) :
    e₁ ((K.d 0 1).hom x) g = ρ (g 0) (e₀ x default) - e₀ x default := by
  rw [hd, Fin.sum_univ_one, Subsingleton.elim (fun k : Fin 0 ↦ g k.succ) default,
    Subsingleton.elim (Fin.contractNth _ _ g) default]
  simp [sub_eq_add_neg]

/-- Degree-zero cycles of a cochain complex modelled on continuous cochains are the
invariant vectors. -/
noncomputable def cyclesZeroEquivInvariants
    (hd : ∀ (x : K.X 0) (g : Fin 1 → G), e₁ ((K.d 0 1).hom x) g =
      ρ (g 0) (e₀ x (fun k ↦ g k.succ)) +
        ∑ k : Fin 1, (-1 : ℤ) ^ (k.val + 1) • e₀ x (Fin.contractNth k (· * ·) g)) :
    K.cycles 0 ≃ₗ[A] (⨅ g : G, LinearMap.ker (ρ g - LinearMap.id) : Submodule A V) :=
  LinearEquiv.ofBijective
    { toFun z := ⟨e₀ ((K.iCycles 0).hom z) default, by
        rw [mem_iInf_ker_sub_id]
        intro g
        have h := cochain_d_zero_apply ρ K e₀ e₁ hd ((K.iCycles 0).hom z) fun _ ↦ g
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d] at h
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
          ContinuousMap.zero_apply] at h
        exact sub_eq_zero.1 h.symm⟩
      map_add' _ _ := by
        ext
        simp
      map_smul' _ _ := by
        ext
        simp }
    ⟨fun z z' h ↦
      (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
        (e₀.injective (cochain_zero_ext (congrArg Subtype.val h))), fun m ↦ by
      have hS : (ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)).Exact :=
        ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel 0 1 (by simp))
      obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS
        (e₀.symm (ContinuousMap.const _ m.1)) (e₁.injective (ContinuousMap.ext fun g ↦ by
          have hm := (mem_iInf_ker_sub_id A G ρ m.1).1 m.2 (g 0)
          simp [cochain_d_zero_apply ρ K e₀ e₁ hd, hm]))
      refine ⟨z, Subtype.ext ?_⟩
      dsimp at hz ⊢
      simp [hz]⟩

@[simp]
lemma cyclesZeroEquivInvariants_apply_coe
    (hd : ∀ (x : K.X 0) (g : Fin 1 → G), e₁ ((K.d 0 1).hom x) g =
      ρ (g 0) (e₀ x (fun k ↦ g k.succ)) +
        ∑ k : Fin 1, (-1 : ℤ) ^ (k.val + 1) • e₀ x (Fin.contractNth k (· * ·) g))
    (z : K.cycles 0) :
    (cyclesZeroEquivInvariants ρ K e₀ e₁ hd z).1 = e₀ ((K.iCycles 0).hom z) default :=
  rfl

end CyclesZero

/-- Elementwise form of `HomologicalComplex.cyclesMap_i` for complexes of modules. -/
lemma iCycles_cyclesMap_apply {A : Type v} [Ring A] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{w} A) c} (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.cyclesMap_i]
  rfl

set_option linter.unusedVariables false in
/-- Degree-zero continuous cochain homology is the left exact invariant functor.

Proof: A continuous map from the singleton `Fin 0 → G` is a constant coefficient.
The degree-zero differential is the function `g ↦ ρ(g)m - m`, so its kernel is exactly
`⨅ g, ker (ρ(g) - id)`. There are no incoming boundaries in degree zero; the homology
kernel description therefore gives a linear equivalence to this invariant submodule.
Postcomposition commutes with evaluation and with the kernel inclusion, making the
identifications natural. Define the invariant functor on maps by restriction of the
underlying equivariant linear map. Restriction preserves identities, compositions and
addition. This construction is data, independent of any existence choice. Finally the
forgetful functor detects module kernels and finite products by
`lem-exc-discrete-modules-abelian`; taking invariant elements commutes with both kernels
and finite products. Thus the constructed invariant functor preserves finite limits.
The degree-zero equivalences assemble into the asserted natural isomorphism.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
label section-continuous-group-cohomology, degree-zero differential and invariants.
(blueprint: lem-exc-continuous-cochains-invariants-zero). -/
theorem continuousCochains_invariants_zero
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
    ∀ F : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        CochainComplex (ModuleCat.{max u w} A) ℕ,
      ∀ e : ∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ),
        (F.obj M).X n ≃ₗ[A] C(Fin n → G, M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
          (n : ℕ) (x : (F.obj M).X n) (g : Fin n → G),
          e N n (((F.map f).f n).hom x) g = f.hom.hom (e M n x g)) →
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (n : ℕ)
          (x : (F.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((F.obj M).d n (n + 1)).hom x) g =
            M.obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) →
    ∃ V : DiscreteContinuousRep.{v, u, max u w} A G ⥤ ModuleCat.{max u w} A,
      ∃ a : V.Additive,
        letI instAdditive : V.Additive := a
        ∃ t : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
            V.obj M ≃ₗ[A] S M,
          (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (f : M ⟶ N)
            (x : V.obj M),
            (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) ∧
          PreservesFiniteLimits V ∧
          Nonempty ((F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
            (ComplexShape.up ℕ) 0) ≅ V) := by
  intro h S F e hnat hd
  let (M : DiscreteContinuousRep.{v, u, max u w} A G) : TopologicalSpace M.obj.V := ⊥
  let (M : DiscreteContinuousRep.{v, u, max u w} A G) : DiscreteTopology M.obj.V := ⟨rfl⟩
  let (M : DiscreteContinuousRep.{v, u, max u w} A G) : ContinuousConstSMul A M.obj.V :=
    ⟨fun _ ↦ continuous_of_discreteTopology⟩
  refine ⟨discreteInvariantsFunctor.{u, v, max u w} A G,
    discreteInvariantsFunctor_additive.{u, v, max u w} A G (inst := h.toPreadditive),
    fun M ↦ LinearEquiv.refl A _, fun M N f x ↦ rfl, inferInstance, ⟨?_⟩⟩
  refine NatIso.ofComponents (fun M ↦ (F.obj M).isoHomologyπ₀.symm ≪≫
    (cyclesZeroEquivInvariants M.obj.ρ (F.obj M) (e M 0) (e M 1) (hd M 0)).toModuleIso) ?_
  intro M N f
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Iso.trans_hom,
    Iso.symm_hom, CochainComplex.isoHomologyπ₀_inv_naturality_assoc, Category.assoc, cancel_epi]
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ Subtype.ext ?_)
  simp [discreteInvariantsFunctor, iCycles_cyclesMap_apply, hnat]

end Rep
