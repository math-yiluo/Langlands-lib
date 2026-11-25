/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.BigOperators.Fin

/-!
# LocallyConstantCochainsInvariantsZero

Source: Stacks Project, Etale Cohomology, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-invariants-zero).
-/

@[expose] public section

universe u v w s

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Degree-zero locally constant integer cochain homology is naturally invariants.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, degree-zero differential;
step 3 of lem-sc-locally-constant-cochains-effaceable.

Proof: Fin 0 to G is a singleton. Evaluation identifies its locally constant maps
additively with E(M). The displayed differential for n=0 evaluates to rho(g)m-m,
since contractNth at the sole index drops the argument and the sign is -1.
Its kernel is precisely the invariant submodule. There is no incoming differential
in the N-indexed cochain complex at zero, so homology is this kernel. Compose the
coordinate equivalence, evaluation, and the kernel identification to obtain an
isomorphism in AddCommGrpCat. The coefficient equation makes evaluation commute with
every map of A; restriction to kernels gives naturality. The inverse sends an invariant
element to the constant zero-degree cocycle. These maps are inverse pointwise,
and assemble into the claimed natural isomorphism.
(blueprint: lem-sc-locally-constant-cochains-invariants-zero). -/
theorem locallyConstantCochains_invariants_zero
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
    : Nonempty ((C ⋙ HomologicalComplex.homologyFunctor
        AddCommGrpCat.{max u s} (ComplexShape.up ℕ) 0) ≅
      (E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
        forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)) := by
  classical
  let z : Fin 0 → G := fun _ ↦ 1
  have hdiff (M : A) (x : (C.obj M).X 0) (g : Fin 1 → G) :
      e M 1 (((C.obj M).d 0 1) x) g =
        (E.functor.obj M).obj.ρ (g 0) (e M 0 x z) - e M 0 x z := by
    rw [hd]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, zero_add, pow_one,
      neg_one_zsmul, add_zero, sub_eq_add_neg]
    congr 1
    · exact congrArg (fun t ↦ (E.functor.obj M).obj.ρ (g 0) (e M 0 x t))
        (Subsingleton.elim _ _)
    · exact congrArg (fun t ↦ -(e M 0 x t)) (Subsingleton.elim _ _)
  let V := E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat
  let i (M : A) : V.obj M ⟶ (C.obj M).X 0 := AddCommGrpCat.ofHom
    { toFun := fun m ↦ (e M 0).symm (LocallyConstant.const _ m.val)
      map_zero' := by
        apply (e M 0).injective
        simp only [AddEquiv.apply_symm_apply, map_zero]
        ext g
        rfl
      map_add' := by
        intro x y
        apply (e M 0).injective
        simp only [AddEquiv.apply_symm_apply, map_add]
        ext g
        rfl }
  have hi (M : A) : i M ≫ (C.obj M).d 0 1 = 0 := by
    ext m
    apply (e M 1).injective
    ext g
    change e M 1 (((C.obj M).d 0 1) (i M m)) g = e M 1 0 g
    rw [map_zero, LocallyConstant.zero_apply, hdiff]
    change (E.functor.obj M).obj.ρ (g 0)
      ((e M 0) ((e M 0).symm (LocallyConstant.const _ m.val)) z) -
      ((e M 0) ((e M 0).symm (LocallyConstant.const _ m.val)) z) = 0
    simp only [AddEquiv.apply_symm_apply, LocallyConstant.coe_const, Function.const_apply]
    exact sub_eq_zero.mpr (m.property (g 0))
  let j (M : A) : V.obj M ⟶ (C.obj M).cycles 0 :=
    (C.obj M).liftCycles (i M) 1 (by simp) (hi M)
  let p (M : A) : (C.obj M).cycles 0 ⟶ V.obj M := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ⟨e M 0 ((C.obj M).iCycles 0 x) z, by
        intro g
        apply sub_eq_zero.mp
        have hx := ConcreteCategory.congr_hom ((C.obj M).iCycles_d 0 1) x
        change ((C.obj M).d 0 1) ((C.obj M).iCycles 0 x) = 0 at hx
        have hx' := hdiff M ((C.obj M).iCycles 0 x) (fun _ ↦ g)
        rw [hx, map_zero, LocallyConstant.zero_apply] at hx'
        exact hx'.symm⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by
        intro x y
        apply Subtype.ext
        change e M 0 ((C.obj M).iCycles 0 (x + y)) z =
          e M 0 ((C.obj M).iCycles 0 x) z + e M 0 ((C.obj M).iCycles 0 y) z
        simp }
  have hj (M : A) : j M ≫ (C.obj M).iCycles 0 = i M :=
    (C.obj M).liftCycles_i (i M) 1 (by simp) (hi M)
  have hpj (M : A) : p M ≫ j M = 𝟙 _ := by
    apply (cancel_mono ((C.obj M).iCycles 0)).mp
    rw [Category.assoc, hj]
    ext x
    apply (e M 0).injective
    ext g
    change (e M 0) ((e M 0).symm
      (LocallyConstant.const _ (e M 0 ((C.obj M).iCycles 0 x) z))) g =
        e M 0 ((C.obj M).iCycles 0 x) g
    simp only [AddEquiv.apply_symm_apply, LocallyConstant.coe_const, Function.const_apply]
    exact congrArg (e M 0 ((C.obj M).iCycles 0 x)) (Subsingleton.elim _ _)
  have hjp (M : A) : j M ≫ p M = 𝟙 _ := by
    ext x
    apply Subtype.ext
    have hx := ConcreteCategory.congr_hom (hj M) x
    change (C.obj M).iCycles 0 (j M x) = i M x at hx
    change e M 0 ((C.obj M).iCycles 0 (j M x)) z = x.val
    rw [hx]
    change (e M 0) ((e M 0).symm (LocallyConstant.const _ x.val)) z = x.val
    simp
  let a (M : A) : (C.obj M).cycles 0 ≅ V.obj M :=
    { hom := p M, inv := j M, hom_inv_id := hpj M, inv_hom_id := hjp M }
  refine ⟨NatIso.ofComponents
    (fun M ↦ (C.obj M).isoHomologyπ₀.symm ≪≫ a M) ?_⟩
  intro M N f
  change HomologicalComplex.homologyMap (C.map f) 0 ≫
    (C.obj N).isoHomologyπ₀.inv ≫ p N =
    (C.obj M).isoHomologyπ₀.inv ≫ p M ≫ V.map f
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc]
  congr 1
  ext x
  apply Subtype.ext
  have hx := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (C.map f) 0) x
  change (C.obj N).iCycles 0 (HomologicalComplex.cyclesMap (C.map f) 0 x) =
    ((C.map f).f 0) ((C.obj M).iCycles 0 x) at hx
  change e N 0 ((C.obj N).iCycles 0
    (HomologicalComplex.cyclesMap (C.map f) 0 x)) z =
    (E.functor.map f).hom.hom (e M 0 ((C.obj M).iCycles 0 x) z)
  rw [hx]
  exact hm M N f 0 ((C.obj M).iCycles 0 x) z

end Rep
