/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty

/-!
# Finite tensor comparison for towers with eventually zero tensor kernels

Source: Stacks Project, More on Algebra, proof of Tag 0912; Algebra, Tag 0597.
(blueprint: lem-weil-pbc-tensor-limit-of-pro-zero-kernels)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

private theorem tensor_square
    {A : Type u} [CommRing A]
    {P : Type*} {Q : Type*} {M : Type*} {N : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : P →ₗ[A] Q) (g : M →ₗ[A] N) (x : TensorProduct A P M) :
    f.rTensor N (g.lTensor P x) = g.lTensor Q (f.rTensor M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem exists_limit_of_succ
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (x : ∀ n : ℕ, F.obj (op n))
    (hx : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n) :
    ∃ y : (limit F : ModuleCat.{v} A), ∀ n, limit.π F (op n) y = x n := by
  have hmap : ∀ n m (h : n ≤ m), F.map (homOfLE h).op (x m) = x n := by
    intro n m h
    induction h with
    | refl => simp
    | @step m h ih =>
      have he : (homOfLE (Nat.le_succ_of_le h)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.map_comp]
      change F.map (homOfLE h).op (F.map (homOfLE (Nat.le_succ m)).op (x (m + 1))) = _
      rw [hx, ih]
  let s : (F ⋙ forget (ModuleCat A)).sections := ⟨fun j ↦ x j.unop, by
    intro j j' f
    change F.map f (x j.unop) = x j'.unop
    have he : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [he]
    exact hmap _ _ _⟩
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves (forget (ModuleCat A)) (limit.isLimit F))
  refine ⟨e.symm s, ?_⟩
  intro n
  exact congrArg (fun s : (F ⋙ forget (ModuleCat A)).sections ↦ s.val (op n))
    (e.apply_symm_apply s)

private noncomputable def freeTensorEquiv
    (A : Type u) [CommRing A] (d : ℕ) (N : Type*) [AddCommGroup N] [Module A N] :
    TensorProduct A (Fin d → A) N ≃ₗ[A] (Fin d → N) :=
  TensorProduct.comm A _ _ ≪≫ₗ TensorProduct.piScalarRight A A N (Fin d)

private theorem freeTensorEquiv_naturality
    {A : Type u} [CommRing A] (d : ℕ) {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (x : TensorProduct A (Fin d → A) M) (i : Fin d) :
    freeTensorEquiv A d N (f.lTensor (Fin d → A) x) i =
      f (freeTensorEquiv A d M x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul p m => simp [freeTensorEquiv]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private theorem free_comparison
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (d : ℕ) :
    Function.Injective
        (LinearMap.pi fun n : ℕ ↦ (limit.π F (op n)).hom.lTensor (Fin d → A)) ∧
      ∀ x : ∀ n : ℕ, TensorProduct A (Fin d → A) (F.obj (op n)),
        (∀ n, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor (Fin d → A)
          (x (n + 1)) = x n) →
        ∃ y : TensorProduct A (Fin d → A) (limit F : ModuleCat.{v} A),
          ∀ n, (limit.π F (op n)).hom.lTensor (Fin d → A) y = x n := by
  constructor
  · intro x y hxy
    apply (freeTensorEquiv A d (limit F : ModuleCat.{v} A)).injective
    funext i
    apply Concrete.limit_ext F
    intro j
    have h := congrFun hxy j.unop
    have hi := congrArg (fun t ↦ freeTensorEquiv A d (F.obj j) t i) h
    simpa only [LinearMap.pi_apply, freeTensorEquiv_naturality] using hi
  · intro x hx
    have hlift (i : Fin d) : ∃ y : (limit F : ModuleCat.{v} A),
        ∀ n, limit.π F (op n) y = freeTensorEquiv A d (F.obj (op n)) (x n) i := by
      apply exists_limit_of_succ F
      intro n
      rw [← freeTensorEquiv_naturality, hx]
    choose y hy using hlift
    refine ⟨(freeTensorEquiv A d (limit F : ModuleCat.{v} A)).symm y, ?_⟩
    intro n
    apply (freeTensorEquiv A d (F.obj (op n))).injective
    funext i
    rw [freeTensorEquiv_naturality, LinearEquiv.apply_symm_apply]
    exact hy i n

private theorem comparison_surjective
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (Q : Type w) [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (x : ∀ n : ℕ, TensorProduct A Q (F.obj (op n)))
    (hx : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor Q
      (x (n + 1)) = x n) :
    ∃ y : TensorProduct A Q (limit F : ModuleCat.{v} A),
      ∀ n, (limit.π F (op n)).hom.lTensor Q y = x n := by
  classical
  obtain ⟨d, p, hp⟩ := Module.Finite.exists_fin' A Q
  let P := Fin d → A
  let K := p.ker
  have hex (n : ℕ) := rTensor_exact (F.obj (op n)) p.exact_subtype_ker_map hp
  have hstep (n : ℕ) (b : TensorProduct A P (F.obj (op n)))
      (hb : p.rTensor (F.obj (op n)) b = x n) :
      ∃ b' : TensorProduct A P (F.obj (op (n + 1))),
        p.rTensor (F.obj (op (n + 1))) b' = x (n + 1) ∧
        (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor P b' = b := by
    let t := (F.map (homOfLE (Nat.le_succ n)).op).hom
    obtain ⟨b', hb'⟩ := p.rTensor_surjective (F.obj (op (n + 1))) hp (x (n + 1))
    have hk : p.rTensor (F.obj (op n)) (t.lTensor P b' - b) = 0 := by
      rw [map_sub, tensor_square, hb', hx, hb, sub_self]
    obtain ⟨a, ha⟩ := ((hex n) _).mp hk
    obtain ⟨a', ha'⟩ := t.lTensor_surjective K (hsurj n) a
    refine ⟨b' - K.subtype.rTensor (F.obj (op (n + 1))) a', ?_, ?_⟩
    · rw [map_sub, (hex (n + 1)).apply_apply_eq_zero, sub_zero, hb']
    · rw [map_sub, ← tensor_square, ha', ha, sub_sub_cancel]
  let B (n : ℕ) := {b : TensorProduct A P (F.obj (op n)) //
    p.rTensor (F.obj (op n)) b = x n}
  let b0 : B 0 := ⟨(p.rTensor_surjective (F.obj (op 0)) hp (x 0)).choose,
    (p.rTensor_surjective (F.obj (op 0)) hp (x 0)).choose_spec⟩
  let next (n : ℕ) (b : B n) : B (n + 1) :=
    ⟨(hstep n b.val b.property).choose, (hstep n b.val b.property).choose_spec.1⟩
  let b : ∀ n, B n := fun n ↦ Nat.rec (motive := B) b0 next n
  have hc : ∀ n, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor P
      (b (n + 1)).val = (b n).val := by
    intro n
    exact (hstep n (b n).val (b n).property).choose_spec.2
  obtain ⟨z, hz⟩ := (free_comparison F d).2 (fun n ↦ (b n).val) hc
  refine ⟨p.rTensor (limit F : ModuleCat.{v} A) z, ?_⟩
  intro n
  rw [← tensor_square, hz]
  exact (b n).property

private theorem tensor_transition_comp
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (P : Type*) [AddCommGroup P] [Module A P]
    {i j k : ℕᵒᵖ} (f : i ⟶ j) (g : j ⟶ k)
    (x : TensorProduct A P (F.obj i)) :
    (F.map g).hom.lTensor P ((F.map f).hom.lTensor P x) =
      (F.map (f ≫ g)).hom.lTensor P x := by
  rw [← LinearMap.lTensor_comp_apply]
  exact congrArg (fun h : F.obj i →ₗ[A] F.obj k ↦ h.lTensor P x)
    (congrArg Hom.hom (F.map_comp f g)).symm

private theorem compatible_preimages_of_proZero
    {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : P →ₗ[A] Q)
    (z : ∀ j : ℕᵒᵖ, TensorProduct A Q (F.obj j))
    (hz : ∀ {i j : ℕᵒᵖ} (g : i ⟶ j), (F.map g).hom.lTensor Q (z i) = z j)
    (hrange : ∀ j, ∃ b : TensorProduct A P (F.obj j), f.rTensor (F.obj j) b = z j)
    (hker : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      ∀ b : TensorProduct A P (F.obj (op m)), f.rTensor (F.obj (op m)) b = 0 →
        (F.map (homOfLE hnm).op).hom.lTensor P b = 0) :
    ∃ b : ∀ j : ℕᵒᵖ, TensorProduct A P (F.obj j),
      (∀ j, f.rTensor (F.obj j) (b j) = z j) ∧
      ∀ {i j : ℕᵒᵖ} (g : i ⟶ j), (F.map g).hom.lTensor P (b i) = b j := by
  classical
  let E : ℕᵒᵖ ⥤ Type (max u v) := {
    obj := fun j ↦ {b : TensorProduct A P (F.obj j) // f.rTensor (F.obj j) b = z j}
    map := fun {i j} g ↦ ↾fun b ↦ ⟨(F.map g).hom.lTensor P b.val, by
      rw [tensor_square, b.property, hz]⟩
    map_id := by
      intro i
      apply ConcreteCategory.hom_ext
      intro b
      apply Subtype.ext
      simp
    map_comp := by
      intro i j k g h
      apply ConcreteCategory.hom_ext
      intro b
      apply Subtype.ext
      exact (tensor_transition_comp F P g h b.val).symm }
  let (j : ℕᵒᵖ) : Nonempty (E.obj j) := ⟨⟨(hrange j).choose, (hrange j).choose_spec⟩⟩
  have hML : E.IsMittagLeffler := by
    intro j
    obtain ⟨m, hnm, hm⟩ := hker j.unop
    let t : op m ⟶ j := (homOfLE hnm).op
    refine ⟨op m, t, ?_⟩
    intro k g
    rintro _ ⟨b, rfl⟩
    let l := max m k.unop
    let s : op l ⟶ op m := (homOfLE (Nat.le_max_left m k.unop)).op
    let r : op l ⟶ k := (homOfLE (Nat.le_max_right m k.unop)).op
    obtain ⟨c⟩ := (inferInstance : Nonempty (E.obj (op l)))
    refine ⟨E.map r c, ?_⟩
    apply Subtype.ext
    have hk : f.rTensor (F.obj (op m))
        (b.val - (F.map s).hom.lTensor P c.val) = 0 := by
      rw [map_sub, tensor_square, c.property, hz, b.property, sub_self]
    have he := hm _ hk
    rw [map_sub, sub_eq_zero] at he
    change (F.map g).hom.lTensor P ((F.map r).hom.lTensor P c.val) =
      (F.map t).hom.lTensor P b.val
    rw [he, tensor_transition_comp, tensor_transition_comp]
    congr 2
  obtain ⟨b, hb⟩ := Functor.nonempty_sections_of_isMittagLeffler E hML
  refine ⟨fun j ↦ (b j).val, fun j ↦ (b j).property, ?_⟩
  intro i j g
  exact congrArg Subtype.val (hb g)

/-- A surjective tower with eventually zero finite tensor kernels commutes with finite tensor.
Source: Stacks Project, More on Algebra, proof of Tag 0912; Algebra, Tag 0597.
(blueprint: lem-weil-pbc-tensor-limit-of-pro-zero-kernels)

Proof: choose a finite free presentation 0 → K → P → Q → 0. Noetherianity makes
K finite. For surjectivity, lift a compatible family in Q ⊗ F_n recursively to
P ⊗ F_n. Given a lift at n and an arbitrary lift at n+1, their difference at n
is in the kernel, hence is the image of an element of K ⊗ F_n by tensor right
exactness. Lift that element along the surjective transition of K ⊗ F and subtract
it at n+1. This corrects compatibility. Finite free tensor commutes with limits:
under P=A^d it is the interchange of a finite product with compatible sequences.
The compatible P-family therefore comes from P ⊗ lim F; mapping it to Q proves
surjectivity. This part needs no Noetherianity and applies to every finite module.
For injectivity, lift y ∈ Q ⊗ lim F to z ∈ P ⊗ lim F by tensor right exactness.
If all coordinates of y vanish, those of z have preimages in K ⊗ F_n. These
preimage fibres form a tower of nonempty sets. Their differences lie in the tensor
kernels in hker. For each n choose m whose transition kills that kernel. For any
other stage k ≥ n, choose a preimage at a common later stage l ≥ m,k. Its image
at n equals the image of every preimage at m, since their difference at m is killed
on transition to n. The fibres are thus Mittag--Leffler. Tag 0597, as formalized
in `Functor.nonempty_sections_of_isMittagLeffler`, supplies compatible preimages.
The already proved surjectivity for K lifts these to K ⊗ lim F. Their image in
P ⊗ lim F equals z, by the finite free comparison's injectivity. Thus y=0.
All identifications send q ⊗ t to (q ⊗ π_n(t))_n, the stated comparison. -/
theorem tensor_limit_comparison_of_proZero_kernels
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (hker : ∀ (P : Type u) [AddCommGroup P] [Module A P] [Module.Finite A P]
      (K : Submodule A P) (n : ℕ),
      ∃ (m : ℕ) (hnm : n ≤ m),
        ∀ x : TensorProduct A K (F.obj (op m)),
          K.subtype.rTensor (F.obj (op m)) x = 0 →
          (F.map (homOfLE hnm).op).hom.lTensor K x = 0)
    (Q : Type w) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Injective (LinearMap.pi fun n : ℕ ↦ (limit.π F (op n)).hom.lTensor Q) ∧
      ∀ x : ∀ n : ℕ, TensorProduct A Q (F.obj (op n)),
        (∀ n : ℕ, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor Q (x (n + 1))
          = x n) →
        ∃ y : TensorProduct A Q (limit F : ModuleCat.{v} A),
          ∀ n : ℕ, (limit.π F (op n)).hom.lTensor Q y = x n := by
  refine ⟨?_, comparison_surjective F hsurj Q⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨d, p, hp⟩ := Module.Finite.exists_fin' A Q
  let P := Fin d → A
  let K := p.ker
  obtain ⟨z, hz⟩ := p.rTensor_surjective (limit F : ModuleCat.{v} A) hp y
  have hzero (n : ℕ) : (limit.π F (op n)).hom.lTensor Q y = 0 := by
    have h := congrFun hy n
    simpa only [LinearMap.pi_apply, LinearMap.zero_apply, Pi.zero_apply] using h
  let zc (j : ℕᵒᵖ) := (limit.π F j).hom.lTensor P z
  have hzc {i j : ℕᵒᵖ} (g : i ⟶ j) :
      (F.map g).hom.lTensor P (zc i) = zc j := by
    dsimp [zc]
    rw [← LinearMap.lTensor_comp_apply]
    exact congrArg (fun f ↦ f.lTensor P z) (congrArg Hom.hom (limit.w F g))
  have hrange (j : ℕᵒᵖ) : ∃ b : TensorProduct A K (F.obj j),
      K.subtype.rTensor (F.obj j) b = zc j := by
    apply ((rTensor_exact (F.obj j) p.exact_subtype_ker_map hp) _).mp
    dsimp [zc]
    rw [tensor_square, hz]
    exact hzero j.unop
  obtain ⟨b, hb, hbc⟩ := compatible_preimages_of_proZero F K.subtype zc
    (fun g ↦ hzc g) hrange (hker P K)
  obtain ⟨a, ha⟩ := comparison_surjective F hsurj K (fun n ↦ b (op n))
    (fun n ↦ hbc (homOfLE (Nat.le_succ n)).op)
  have hza : K.subtype.rTensor (limit F : ModuleCat.{v} A) a = z := by
    apply (free_comparison F d).1
    ext n
    change (limit.π F (op n)).hom.lTensor P
      (K.subtype.rTensor (limit F : ModuleCat.{v} A) a) = zc (op n)
    rw [← tensor_square, ha, hb]
  rw [← hz, ← hza]
  have he := rTensor_exact (limit F : ModuleCat.{v} A) p.exact_subtype_ker_map hp
  exact he.apply_apply_eq_zero a

end ModuleCat
