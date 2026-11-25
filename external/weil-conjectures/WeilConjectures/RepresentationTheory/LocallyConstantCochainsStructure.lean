/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.RepresentationTheory.HomogeneousInhomogeneousContinuousCohomology

/-!
# Construction of locally constant inhomogeneous cochains
Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential.
(blueprint: lem-sc-locally-constant-cochains-structure).
-/

@[expose] public section
universe u v w s
open CategoryTheory
namespace Rep
private theorem action_lc
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (n : ℕ) (c : LocallyConstant (Fin n → G) M.obj.V) :
    IsLocallyConstant (fun g : Fin (n + 1) → G ↦
      M.obj.ρ (g 0) (c (fun i ↦ g i.succ))) := by
  let : TopologicalSpace M.obj.V := ⊥
  have : DiscreteTopology M.obj.V := discreteTopology_bot _
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
  apply (IsLocallyConstant.iff_continuous _).mpr
  exact continuous_smul.comp ((continuous_apply 0).prodMk
    (c.continuous.comp (continuous_pi fun i ↦ continuous_apply i.succ)))

private noncomputable def lcD
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) (n : ℕ) :
    LocallyConstant (Fin n → G) M.obj.V →+
      LocallyConstant (Fin (n + 1) → G) M.obj.V where
  toFun c := ⟨fun g ↦ M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) • c (Fin.contractNth k (· * ·) g), by
    apply IsLocallyConstant.add (action_lc M n c)
    have h : ∀ k : Fin (n + 1), IsLocallyConstant (fun g : Fin (n + 1) → G ↦
        (-1 : ℤ) ^ (k.val + 1) • c (Fin.contractNth k (· * ·) g)) := by
      intro k
      apply IsLocallyConstant.comp _ (fun x ↦ (-1 : ℤ) ^ (k.val + 1) • x)
      apply c.isLocallyConstant.comp_continuous
      apply continuous_pi
      intro i
      unfold Fin.contractNth
      split_ifs
      · exact continuous_apply _
      · exact (continuous_apply _).mul (continuous_apply _)
      · exact continuous_apply _
    classical
    exact Finset.induction_on Finset.univ (IsLocallyConstant.const 0)
      (fun k t hk ht ↦ by
        simpa only [Finset.sum_insert hk] using (h k).comp₂ ht (· + ·))⟩
  map_zero' := by ext g; simp [zsmul_zero]
  map_add' c d := by
    ext g
    simp [Finset.sum_add_distrib, add_add_add_comm, zsmul_add]

private theorem lcD_sq
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) (n : ℕ)
    (c : LocallyConstant (Fin n → G) M.obj.V) : lcD M (n + 1) (lcD M n c) = 0 := by
  let : TopologicalSpace M.obj.V := ⊥
  have : DiscreteTopology M.obj.V := ⟨rfl⟩
  let ρ : ContRepresentation ℤ G M.obj.V := .ofMonoidHom
    { toFun := fun g ↦ ⟨M.obj.ρ g, continuous_of_discreteTopology⟩
      map_one' := by ext x; change M.obj.ρ 1 x = x; simp
      map_mul' := by
        intro g h
        ext x
        change M.obj.ρ (g * h) x = M.obj.ρ g (M.obj.ρ h x)
        simp [map_mul] }
  have : @ContinuousSMul ℤ M.obj.V M.obj.hV2.toSMul _ _ :=
    @ContinuousSMul.mk _ _ M.obj.hV2.toSMul _ _ continuous_of_discreteTopology
  let N : TopRep.{max u s} ℤ G := TopRep.of ρ
  obtain ⟨e, he⟩ := exists_homogeneousCochains_inhomogeneous_coordinates G N M.property
  have hd : ∀ n x, e (n + 1) (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) =
      lcD M n (e n x) := by
    intro n x
    ext g
    exact he n x g
  rw [← (e n).apply_symm_apply c, ← hd, ← hd]
  have hs := (TopRep.homogeneousCochains N).d_comp_d n (n + 1) (n + 2)
  have hh := congrArg (fun f ↦ f.hom ((e n).symm c)) hs
  change (((TopRep.homogeneousCochains N).d (n + 1) (n + 2)).hom
    (((TopRep.homogeneousCochains N).d n (n + 1)).hom ((e n).symm c))) = 0 at hh
  rw [hh, map_zero]

private noncomputable abbrev lcComplex
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    CochainComplex AddCommGrpCat.{max u s} ℕ :=
  CochainComplex.of (fun n ↦ AddCommGrpCat.of (LocallyConstant (Fin n → G) M.obj.V))
    (fun n ↦ AddCommGrpCat.ofHom (lcD M n)) (fun n ↦ by
      ext c g
      exact DFunLike.congr_fun (lcD_sq M n c) g)

private noncomputable abbrev lcMap
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {M N : DiscreteContinuousRep.{0, u, max u s} ℤ G} (f : M ⟶ N) :
    lcComplex M ⟶ lcComplex N :=
  CochainComplex.ofHom
    (fun n ↦ AddCommGrpCat.ofHom
      (LocallyConstant.mapAddMonoidHom f.hom.hom.toAddMonoidHom)) (fun n ↦ by
        ext c g
        simp only [lcComplex, CochainComplex.of_d]
        change N.obj.ρ (g 0) (f.hom.hom (c (fun i ↦ g i.succ))) +
          ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
            f.hom.hom (c (Fin.contractNth k (· * ·) g)) =
          f.hom.hom (M.obj.ρ (g 0) (c (fun i ↦ g i.succ)) +
            ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
              c (Fin.contractNth k (· * ·) g))
        simp [map_add, map_sum, map_zsmul, Rep.hom_comm_apply])

private noncomputable abbrev lcFunctor
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    DiscreteContinuousRep.{0, u, max u s} ℤ G ⥤
      CochainComplex AddCommGrpCat.{max u s} ℕ where
  obj := lcComplex
  map := lcMap
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

/-- The locally constant integer cochain complex has natural additive coordinates.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential,
and the construction part of lem-sc-locally-constant-cochains-exact.
(blueprint: lem-sc-locally-constant-cochains-structure).

Proof: Take degree n to be the additive group of locally constant functions
from G^n to the carrier of E(M). Define the differential by the formula below.
The non-action faces preserve local constancy by continuous precomposition
with the projections and adjacent multiplication maps. For the action face,
fix a point (g_0,t). The cochain is constant with value m near t. On the open
coset g_0 Stab(m), the action on m is constant, so this face is locally constant.
All faces are additive in the coefficient, and so is their signed sum.
To prove square-zero, give the coefficient module its discrete topology and regard
its representation as a topological representation (each action map is continuous).
Use exists_homogeneousCochains_inhomogeneous_coordinates to identify our explicit
differential with the differential of Mathlib's homogeneous complex. Apply that
complex's square-zero equation and transport it through the additive coordinates.
The coefficient topology does not change the locally constant function type.
These additive maps and their square-zero relation define the complex.
Postcompose cochains with E(f). Equivariance gives commutation with the
action face, and additivity gives commutation with the signed sum, hence
these are complex morphisms. Identity and composition hold pointwise.
This defines the functor C on A; take identity additive coordinates e.
The two required equations are then the definitions of the maps and
of the differential. This construction does not assert exactness. -/
theorem exists_locallyConstantCochains_structure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    ∃ C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ,
      ∃ e : ∀ (M : A) (n : ℕ),
          (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V,
        (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
          e N n (((C.map f).f n) x) g =
            (E.functor.map f).hom.hom (e M n x g)) ∧
        (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
            (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) := by
  refine ⟨E.functor ⋙ lcFunctor, fun M n ↦ AddEquiv.refl _, ?_, ?_⟩
  · intro M N f n x g
    rfl
  · intro M n x g
    change (((lcComplex (E.functor.obj M)).d n (n + 1)) x) g = _
    simp only [lcComplex, CochainComplex.of_d]
    rfl
end Rep
