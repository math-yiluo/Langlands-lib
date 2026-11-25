/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Tactic.Abel

/-!
# LocallyConstantCochainsAcyclicEmbedding

Source: Stacks Project, Etale Cohomology, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-acyclic-embedding).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

private theorem continuous_insert (G : Type u) [TopologicalSpace G] (n : ℕ) :
    Continuous (fun p : (Fin n → G) × G ↦ (Fin.cons p.2 p.1 : Fin (n + 1) → G)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using continuous_snd
  · simpa only [Fin.cons_succ, Function.comp_def] using
      (continuous_apply j).comp continuous_fst

private def evaluationContraction (G : Type u) [Group G] [TopologicalSpace G]
    [CompactSpace G] (V : Type s) [AddCommGroup V] (n : ℕ) :
    LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V) →+
      LocallyConstant (Fin n → G) (LocallyConstant G V) where
  toFun F :=
    { toFun := fun g ↦
        { toFun := fun x ↦ F (Fin.cons x g) 1
          isLocallyConstant := by
            exact (F.isLocallyConstant.comp (fun a ↦ a 1)).comp_continuous
              ((continuous_insert G n).comp (continuous_const.prodMk continuous_id)) }
      isLocallyConstant := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro g
        have hf : IsLocallyConstant
            (fun p : (Fin n → G) × G ↦ F (Fin.cons p.2 p.1) 1) :=
          (F.isLocallyConstant.comp (fun a ↦ a 1)).comp_continuous (continuous_insert G n)
        have hf₀ : IsLocallyConstant
            (fun p : (Fin n → G) × G ↦ F (Fin.cons p.2 g) 1) :=
          (F.isLocallyConstant.comp (fun a ↦ a 1)).comp_continuous
            ((continuous_insert G n).comp (continuous_const.prodMk continuous_snd))
        have hopen : IsOpen {p : (Fin n → G) × G |
            F (Fin.cons p.2 p.1) 1 = F (Fin.cons p.2 g) 1} :=
          (hf.prodMk hf₀) {p | p.1 = p.2}
        have he := isCompact_univ.eventually_forall_of_forall_eventually
          (x₀ := g) (P := fun g' x ↦ F (Fin.cons x g') 1 = F (Fin.cons x g) 1)
          (fun x _ ↦ hopen.mem_nhds (by rfl))
        filter_upwards [he] with g' hg'
        apply LocallyConstant.ext
        intro x
        exact hg' x (Set.mem_univ x) }
  map_zero' := by
    apply LocallyConstant.ext
    intro g
    apply LocallyConstant.ext
    intro x
    rfl
  map_add' F H := by
    apply LocallyConstant.ext
    intro g
    apply LocallyConstant.ext
    intro x
    rfl

private theorem contract_insert_zero (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) :
    Fin.contractNth 0 (· * ·) (Fin.cons x g) =
      Fin.cons (x * g 0) (fun i ↦ g i.succ) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Fin.contractNth]
  · simp [Fin.contractNth]

private theorem contract_insert_succ (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) (k : Fin (n + 1)) :
    Fin.contractNth k.succ (· * ·) (Fin.cons x g) =
      Fin.cons x (Fin.contractNth k (· * ·) g) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Fin.contractNth]
  · simp [Fin.contractNth]

/-- Evaluation at one after inserting the function variable contracts the positive-degree
cochains with values in a right-translation function module. The coefficient group is
arbitrary; in particular it need not be finite or torsion. Both the additive map and its
value are uniquely determined by the displayed evaluation formula.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, final profinite comparison;
explicit evaluation contraction in the parent acyclic-embedding node.

Proof: Define h_n(F)(g)(x) = F(cons x g)(1). Insertion is continuous and postcomposition
by evaluation preserves local constancy, so this is locally constant in x. For fixed g,
joint local constancy on G times G^n gives product neighborhoods on which the value
is constant. A finite subcover in the compact x variable and intersection of the
corresponding g neighborhoods makes the whole function of x constant near g.
This proves local constancy into the discrete function module. Evaluation and insertion
commute with addition, giving an additive h_n. Expand d_n h_n F at g,x: its first term
is F(cons (x*g_0) (tail g))(1). Expand h_(n+1) d_(n+1) F using the differential at
cons x g and evaluate at one: the action term is F(g)(x), and its first merged term
is the negative of the preceding first term. The remaining merged terms and the
last deletion terms cancel pairwise because their signs differ by one exponent.
Hence the sum is F(g)(x). Extensionality gives the asserted identity, including n=0.
(blueprint: lem-sc-locally-constant-cochains-acyclic-embedding). -/
private theorem integerCoinduced_contraction
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (V : Type s) [AddCommGroup V]
    (d : ∀ n : ℕ,
      LocallyConstant (Fin n → G) (LocallyConstant G V) →+
        LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V))
    (hd : ∀ (n : ℕ) (F : LocallyConstant (Fin n → G) (LocallyConstant G V))
      (g : Fin (n + 1) → G) (x : G),
      d n F g x = F (fun k ↦ g k.succ) (x * g 0) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) g) x) :
    ∃ h : ∀ n : ℕ,
      LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V) →+
        LocallyConstant (Fin n → G) (LocallyConstant G V),
      (∀ (n : ℕ) (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V))
        (g : Fin n → G) (x : G), h n F g x = F (Fin.cons x g) 1) ∧
      (∀ (n : ℕ) (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V)),
        d n (h n F) + h (n + 1) (d (n + 1) F) = F) := by
  refine ⟨evaluationContraction G V, ?_, ?_⟩
  · intros; rfl
  · intro n F
    apply LocallyConstant.ext
    intro g
    apply LocallyConstant.ext
    intro x
    change d n (evaluationContraction G V n F) g x +
      d (n + 1) F (Fin.cons x g) 1 = F g x
    rw [hd, hd]
    simp only [Fin.cons_succ, Fin.cons_zero, one_mul]
    change F (Fin.cons (x * g 0) (fun k ↦ g k.succ)) 1 +
      (∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (k.val + 1) • F (Fin.cons x (Fin.contractNth k (· * ·) g)) 1) +
      (F g x + ∑ k : Fin (n + 2),
        (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) (Fin.cons x g)) 1) =
        F g x
    rw [Fin.sum_univ_succ (fun k : Fin (n + 2) ↦
      (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) (Fin.cons x g)) 1)]
    simp only [Fin.val_zero, zero_add, pow_one, neg_one_zsmul,
      contract_insert_zero, contract_insert_succ, Fin.val_succ]
    simp only [pow_succ', mul_zsmul, neg_one_zsmul, Finset.sum_neg_distrib]
    abel


private def rightTranslation (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type s) [AddCommGroup V] :
    Representation ℤ G (LocallyConstant G V) where
  toFun h := LocallyConstant.comapₗ ℤ ⟨fun x ↦ x * h, continuous_mul_const h⟩
  map_one' := by ext f x; simp
  map_mul' h k := by ext f x; simp [mul_assoc]

private theorem rightTranslation_open (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Type s) [AddCommGroup V] (f : LocallyConstant G V) :
    IsOpen {h : G | rightTranslation G V h f = f} := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of G) V f f.continuous
  let H : Subgroup G :=
    { carrier := {h | rightTranslation G V h f = f}
      one_mem' := by simp
      mul_mem' := by
        intro h k hh hk
        change rightTranslation G V (h * k) f = f
        rw [map_mul, Module.End.mul_apply, hk, hh]
      inv_mem' := by
        intro h hh
        have he := congrArg (fun z ↦ rightTranslation G V h⁻¹ z) hh
        simpa [← Module.End.mul_apply, ← map_mul] using he.symm }
  have hle : (U : Set G) ⊆ H := by
    intro h hh
    change rightTranslation G V h f = f
    ext x
    exact hU x h hh
  exact H.isOpen_of_openSubgroup (U := U.toOpenSubgroup) hle

private def integerCoinduced (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    DiscreteContinuousRep.{0, u, max u s} ℤ G :=
  ⟨Rep.of (rightTranslation G M.obj.V), rightTranslation_open G M.obj.V⟩

private def orbitFunction (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (m : M.obj.V) : LocallyConstant G M.obj.V where
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

private def integerOrbitMap (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) : M ⟶ integerCoinduced G M := by
  let : Module ℤ M.obj.V := M.obj.hV2
  exact ObjectProperty.homMk (Rep.ofHom (ρ := M.obj.ρ)
    (σ := (integerCoinduced G M).obj.ρ)
    { toLinearMap :=
        { toFun := orbitFunction G M
          map_add' := by
            intro a b
            apply LocallyConstant.ext
            intro x
            change M.obj.ρ x (a + b) = M.obj.ρ x a + M.obj.ρ x b
            exact map_add _ _ _
          map_smul' := by
            intro a b
            apply LocallyConstant.ext
            intro x
            have h₁ := congrArg (fun z : M.obj.V ↦ M.obj.ρ x z)
              (int_smul_eq_zsmul M.obj.hV2 a b)
            exact h₁.trans ((map_zsmul (M.obj.ρ x).toAddMonoidHom a b).trans
              (map_zsmul (LocallyConstant.evalAddMonoidHom x) a (orbitFunction G M b)).symm) }
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro m
        apply LocallyConstant.ext
        intro x
        change M.obj.ρ x (M.obj.ρ h m) = M.obj.ρ (x * h) m
        simp [map_mul, Module.End.mul_apply] })

private theorem integerOrbitMap_mono (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) : Mono (integerOrbitMap G M) := by
  constructor
  intro Z a b hab
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  let : Module ℤ Z.obj.V := Z.obj.hV2
  let : Module ℤ M.obj.V := M.obj.hV2
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have he := congrArg (fun f : Z ⟶ integerCoinduced G M ↦
    (show LocallyConstant G M.obj.V from f.hom.hom z) (1 : G)) hab
  simpa [integerOrbitMap, orbitFunction] using he

/-- Every object embeds in one whose locally constant integer cochain complex is
exact in all positive degrees.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, final profinite comparison;
step 4 of lem-sc-locally-constant-cochains-effaceable (explicit contraction).

Proof: Construct D(E(M)) as LC(G,E(M)) with pointwise integer module structure and
right translation rho(h)f(x)=f(x*h). Every function has a finite clopen partition.
Compactness and continuity of multiplication give a common identity neighborhood
preserving that partition under right translation. A compact Hausdorff totally
disconnected group has an open subgroup inside that neighborhood. Thus stabilizers
are open and D(E(M)) is a discrete representation. The orbit map m to (x to rho(x)m)
is locally constant, integer-linear and equivariant; evaluation at 1 is its left
inverse, so it is monic. Take N=E.inverse.obj D(E(M)) and transport the orbit map via
the unit and counit of E. These are specified constructions, not arbitrary existence
choices. Transport the coordinates of C(N) through the counit to cochains with values
in LC(G,E(M)). For a degree n+1 cochain F put h_n(F)(g)(x)=F(x,g)(1).
This is locally constant in x. For local constancy in g with the whole function of x
fixed, cover the compact x factor by finitely many product neighborhoods on which F
is constant and intersect their g neighborhoods. The contraction is additive.
Expand d_n h_n F and h_(n+1) d_(n+1) F at g,x using the differential equation.
The action face uses right translation. Their sum is F(g)(x): the merged first face
cancels the extra translation term, each interior merged face cancels with the
opposite sign, and the final deletion terms cancel. This includes n=0.
Consequently every positive-degree cocycle F is d(h(F)), and conversely every boundary
is a cocycle. The coordinate equivalences transport this equality of kernel and image
to exactness of C(N) in every positive degree. The coefficient equation identifies
transport under the counit. The orbit map remains monic under the equivalence.
(blueprint: lem-sc-locally-constant-cochains-acyclic-embedding). -/
theorem locallyConstantCochains_acyclic_embedding
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    (hd : ∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
      e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
        (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))
    (M : A) : ∃ (N : A) (f : M ⟶ N), Mono f ∧
      ∀ n : ℕ, 0 < n → (C.obj N).ExactAt n := by
  classical
  have _ := hm
  let D := integerCoinduced G (E.functor.obj M)
  let N := E.inverse.obj D
  let ι := integerOrbitMap G (E.functor.obj M)
  let f : M ⟶ N := (E.unitIso.app M).hom ≫ E.inverse.map ι
  have : Mono ι := integerOrbitMap_mono G (E.functor.obj M)
  refine ⟨N, f, inferInstance, ?_⟩
  let i := E.counitIso.app D
  let q : (E.functor.obj N).obj.V ≃+ LocallyConstant G (E.functor.obj M).obj.V :=
    { toFun := i.hom.hom.hom
      invFun := i.inv.hom.hom
      left_inv := by
        intro y
        change (i.hom ≫ i.inv).hom.hom y = y
        rw [i.hom_inv_id]
        rfl
      right_inv := by
        intro y
        change (i.inv ≫ i.hom).hom.hom y = y
        rw [i.inv_hom_id]
        rfl
      map_add' := by intro a b; exact map_add _ _ _ }
  let r : ∀ n : ℕ, LocallyConstant (Fin n → G) (E.functor.obj N).obj.V ≃+
      LocallyConstant (Fin n → G) (LocallyConstant G (E.functor.obj M).obj.V) :=
    fun n ↦
      { LocallyConstant.congrRight q.toEquiv with
        map_add' := by
          intro a b
          apply LocallyConstant.ext
          intro g
          exact q.map_add (a g) (b g) }
  let t : ∀ n : ℕ, (C.obj N).X n ≃+
      LocallyConstant (Fin n → G) (LocallyConstant G (E.functor.obj M).obj.V) :=
    fun n ↦ (e N n).trans (r n)
  let d : ∀ n : ℕ,
      LocallyConstant (Fin n → G) (LocallyConstant G (E.functor.obj M).obj.V) →+
        LocallyConstant (Fin (n + 1) → G) (LocallyConstant G (E.functor.obj M).obj.V) :=
    fun n ↦ (t (n + 1)).toAddMonoidHom.comp
      (((C.obj N).d n (n + 1)).hom.comp (t n).symm.toAddMonoidHom)
  have hdt : ∀ n x, d n (t n x) = t (n + 1) (((C.obj N).d n (n + 1)) x) := by
    intro n x
    simp [d]
  have hdf : ∀ n F g x, d n F g x = F (fun k ↦ g k.succ) (x * g 0) +
      ∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) g) x := by
    intro n F g x
    obtain ⟨y, rfl⟩ := (t n).surjective F
    rw [hdt]
    change q (e N (n + 1) (((C.obj N).d n (n + 1)) y) g) x =
      q (e N n y (fun k ↦ g k.succ)) (x * g 0) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) • q (e N n y (Fin.contractNth k (· * ·) g)) x
    rw [hd]
    have hsum : ∀ a : Fin (n + 1) → LocallyConstant G (E.functor.obj M).obj.V,
        (∑ k, a k) x = ∑ k, a k x := by
      intro a
      exact map_sum (LocallyConstant.evalAddMonoidHom x) a Finset.univ
    have hsmul : ∀ (z : ℤ) (a : LocallyConstant G (E.functor.obj M).obj.V),
        (z • a) x = z • a x := by
      intro z a
      exact map_zsmul (LocallyConstant.evalAddMonoidHom x) z a
    simp only [map_add, map_sum, map_zsmul, LocallyConstant.add_apply, hsum, hsmul]
    apply congrArg (fun z ↦ z + ∑ k : Fin (n + 1),
      (-1 : ℤ) ^ (k.val + 1) • q (e N n y (Fin.contractNth k (· * ·) g)) x)
    have he := Rep.hom_comm_apply i.hom.hom (g 0) (e N n y (fun k ↦ g k.succ))
    have he' := congrArg
      (fun z : D.obj.V ↦ (show LocallyConstant G (E.functor.obj M).obj.V from z) x) he
    exact he'
  obtain ⟨h, _, hh⟩ := integerCoinduced_contraction G (E.functor.obj M).obj.V d hdf
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [(C.obj N).exactAt_iff' k (k + 1) (k + 2) (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  refine ⟨(t k).symm (h k (t (k + 1) x)), ?_⟩
  change ((C.obj N).d k (k + 1)).hom ((t k).symm (h k (t (k + 1) x))) = x
  apply (t (k + 1)).injective
  have hz : d (k + 1) (t (k + 1) x) = 0 := by
    rw [hdt]
    change t (k + 2) (((C.obj N).d (k + 1) (k + 2)) x) = 0
    rw [show ((C.obj N).d (k + 1) (k + 2)) x = 0 from hx, map_zero]
  have he := hh k (t (k + 1) x)
  rw [hz, map_zero, add_zero] at he
  simpa [d] using he

end Rep
