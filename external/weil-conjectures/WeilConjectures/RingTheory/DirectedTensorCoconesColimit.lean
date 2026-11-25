/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-! # Colimits of coherent iterated tensor diagrams

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-weil-pbc-directed-tensor-cocones-colimit-n3)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Restrict tensor representatives to a prescribed cofinal upper tail. -/
private theorem tail_rep_zero
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (M₀ : Type w) [AddCommGroup M₀] [Module (F.obj i₀) M₀] (k : I) (hik : i₀ ≤ k) :
    let S := F.obj i₀
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
    (∀ x : R ⊗[S] M₀, ∃ (i : I) (h : k ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE (hik.trans h))).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE (hik.trans h))) }
      ∃ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = x) ∧
    (∀ (i : I) (h : k ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE (hik.trans h))).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE (hik.trans h))) }
      ∀ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = 0 →
        ∃ (i' : I) (h' : i ≤ i'),
          letI : Algebra S (F.obj i') := (F.map (homOfLE (hik.trans (h.trans h')))).hom.toAlgebra
          let αᵢ'ᵢ : F.obj i →ₐ[S] F.obj i' :=
            { (F.map (homOfLE h')).hom with
              commutes' := fun s ↦
                congrArg (fun f : F.obj i₀ ⟶ F.obj i' ↦ f s)
                  (F.map_comp (homOfLE (hik.trans h)) (homOfLE h')).symm }
          αᵢ'ᵢ.toLinearMap.rTensor M₀ t = 0) := by
  obtain ⟨hs, hz⟩ := TensorProduct.directedColimitBaseChangeElementwise F i₀ M₀
  dsimp only
  constructor
  · intro x
    obtain ⟨j, hj, t, ht⟩ := hs x
    obtain ⟨l, hkl, hjl⟩ := exists_ge_ge k j
    let : Algebra (F.obj i₀) ↥(colimit F) := (colimit.ι F i₀).hom.toAlgebra
    let : Algebra (F.obj i₀) (F.obj j) := (F.map (homOfLE hj)).hom.toAlgebra
    let : Algebra (F.obj i₀) (F.obj l) :=
      (F.map (homOfLE (hik.trans hkl))).hom.toAlgebra
    let αj : F.obj j →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F j).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
          (colimit.w F (homOfLE hj)) }
    let αl : F.obj l →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F l).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
          (colimit.w F (homOfLE (hik.trans hkl))) }
    let αjl : F.obj j →ₐ[F.obj i₀] F.obj l :=
      { (F.map (homOfLE hjl)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj l ↦ f s)
          (F.map_comp (homOfLE hj) (homOfLE hjl)).symm }
    refine ⟨l, hkl, αjl.toLinearMap.rTensor M₀ t, ?_⟩
    change αl.toLinearMap.rTensor M₀ (αjl.toLinearMap.rTensor M₀ t) = x
    have he : αl.toLinearMap.rTensor M₀ (αjl.toLinearMap.rTensor M₀ t) =
        αj.toLinearMap.rTensor M₀ t := by
      clear ht
      induction t using TensorProduct.inductionOn with
      | tmul a m =>
        simp only [LinearMap.rTensor_tmul]
        exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] m)
          (ConcreteCategory.congr_hom (colimit.w F (homOfLE hjl)) a)
      | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
    exact he.trans ht
  · intro j hj t ht
    exact hz j (hik.trans hj) t ht

/-- Representatives and eventual vanishing recognize a filtered ring colimit. -/
private theorem colimit_of_rep_zero
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ CommRingCat.{w}) [HasColimit G]
    [PreservesColimit G (forget CommRingCat.{w})] (c : Cocone G)
    (hs : ∀ x : c.pt, ∃ j t, (c.ι.app j).hom t = x)
    (hz : ∀ (j : J) (t : G.obj j), (c.ι.app j).hom t = 0 →
      ∃ (k : J) (r : j ⟶ k), (G.map r).hom t = 0) : Nonempty (IsColimit c) := by
  classical
  let U := forget CommRingCat.{w}
  have ht : IsColimit (U.mapCocone c) := by
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨j, t, h⟩ := hs x
      exact ⟨j, t, h.symm⟩
    · intro j a b hab
      change ↥(G.obj j) at a b
      have hzero : (c.ι.app j).hom (a - b) = 0 := by
        change (c.ι.app j).hom a = (c.ι.app j).hom b at hab
        simpa only [map_sub, sub_eq_zero] using hab
      obtain ⟨k, r, hr⟩ := hz j (a - b) hzero
      refine ⟨k, r, ?_⟩
      change (G.map r).hom a = (G.map r).hom b
      simpa only [map_sub, sub_eq_zero] using hr
  let : ReflectsColimit G U := reflectsColimit_of_reflectsIsomorphisms _ U
  exact ⟨isColimitOfReflects U ht⟩

/-- Tensoring an elementwise module direct limit preserves its representatives and kernels. -/
private theorem tensor_rep_zero
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (R : Type w) [CommRing R]
    (A : J → Type x) [∀ j, AddCommGroup (A j)] [∀ j, Module R (A j)]
    (f : ∀ j k, j ≤ k → A j →ₗ[R] A k)
    [DirectedSystem A (fun {j k} h ↦ f j k h)]
    (B : Type y) [AddCommGroup B] [Module R B]
    (μ : ∀ j, A j →ₗ[R] B)
    (hμ : ∀ (j k : J) (h : j ≤ k) t, μ k (f j k h t) = μ j t)
    (hs : ∀ x : B, ∃ j t, μ j t = x)
    (hz : ∀ j t, μ j t = 0 → ∃ (k : J) (h : j ≤ k), f j k h t = 0)
    (N : Type*) [AddCommGroup N] [Module R N] :
    (∀ x : B ⊗[R] N, ∃ j t, (μ j).rTensor N t = x) ∧
    (∀ j t, (μ j).rTensor N t = 0 →
      ∃ (k : J) (h : j ≤ k), (f j k h).rTensor N t = 0) := by
  classical
  let g : Module.DirectLimit A f →ₗ[R] B :=
    Module.DirectLimit.lift R J A f μ hμ
  have ginj : Function.Injective g := by
    intro a b hab
    have hzero : g (a - b) = 0 := by simpa only [map_sub, sub_eq_zero] using hab
    obtain ⟨j, t, ht⟩ := Module.DirectLimit.exists_of (a - b)
    have hμt : μ j t = 0 := by
      simpa only [← ht, g, Module.DirectLimit.lift_of] using hzero
    obtain ⟨k, h, hf⟩ := hz j t hμt
    apply sub_eq_zero.mp
    rw [← ht, ← Module.DirectLimit.of_f (f := f) (i := j) (j := k) (hij := h), hf]
    exact map_zero _
  have gsurj : Function.Surjective g := by
    intro b
    obtain ⟨j, t, ht⟩ := hs b
    refine ⟨Module.DirectLimit.of R J A f j t, ?_⟩
    simpa only [g, Module.DirectLimit.lift_of] using ht
  let e₀ : Module.DirectLimit A f ≃ₗ[R] B := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  let ft (j k : J) (h : j ≤ k) := (f j k h).rTensor N
  let e : Module.DirectLimit (fun j ↦ A j ⊗[R] N) ft ≃ₗ[R] B ⊗[R] N :=
    (TensorProduct.directLimitLeft f N).symm.trans (e₀.rTensor N)
  have e_of (j : J) (t : A j ⊗[R] N) :
      e (Module.DirectLimit.of R J (fun j ↦ A j ⊗[R] N) ft j t) =
        (μ j).rTensor N t := by
    induction t using TensorProduct.inductionOn with
    | tmul a n =>
      dsimp only [e, ft]
      rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
        LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
      change g (Module.DirectLimit.of R J A f j a) ⊗ₜ[R] n = μ j a ⊗ₜ[R] n
      simp only [g, Module.DirectLimit.lift_of]
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  let : DirectedSystem (fun j ↦ A j ⊗[R] N) (fun {j k} h ↦ ft j k h) :=
    inferInstance
  constructor
  · intro x
    obtain ⟨j, t, ht⟩ := Module.DirectLimit.exists_of (e.symm x)
    refine ⟨j, t, ?_⟩
    rw [← e_of, ht, e.apply_symm_apply]
  · intro j t ht
    have hz : Module.DirectLimit.of R J (fun j ↦ A j ⊗[R] N) ft j t = 0 := by
      apply e.injective
      rw [e_of, map_zero]
      exact ht
    exact Module.DirectLimit.of.zero_exact hz

/-- Canonical cocones of coherent tensor diagrams over a directed upper tail are colimits.

Source: Stacks Project, Algebra, Tags 00D6, 00D7 and 00DD.
(blueprint: lem-weil-pbc-directed-tensor-cocones-colimit-n3)

Proof:
1. Restrict the tensor representative theorem to the tail above i. Move any
   representative at j to a common upper bound of i and j; cocone naturality
   identifies its image with the original representative. The eventual-zero
   assertion already stays in this tail.
2. Choose the P-linear transitions β supplied by hDt. Their underlying maps
   are the canonical tensor transitions. Tensor induction and F.map_comp prove
   the directed-system laws; hμs and colimit.w prove compatibility with μs.
3. The module direct limit of the Bⱼ with these transitions maps linearly to B.
   Tensor representatives prove surjectivity. Represent a difference in the
   direct limit; eventual vanishing and DirectLimit.of_f prove injectivity.
   Tensor this linear equivalence over P with Q and use directLimitLeft.
   Representatives and eventual vanishing in this tensor direct limit give
   the same assertions for Bⱼ tensor_P Q and B tensor_P Q.
4. Transport representatives and eventual zero through d, dLim, c and cLim,
   using hcD, hcE, hDt and hEt. Apply the filtered colimit criterion for types:
   equality at one stage is eventual vanishing of the difference. The forgetful
   functor from commutative rings preserves these filtered colimits and reflects
   isomorphisms, hence reflects the two colimit cocones. The common ring universe
   admits the required colimits by universe shrinking.
The argument includes zero rings and the singleton tail and uses no finite
presentation hypothesis or comparison map.
-/
theorem isColimit_directed_tensor_cocones
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (i : I) (hi : i₀ ≤ i)
    (aPs : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀))
    (D E : {j : I // i ≤ j} ⥤ CommRingCat.{max v w x y})
    (d : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q)
    (c : ∀ j : {j : I // i ≤ j},
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀))
    (cD : Cocone D) (cE : Cocone E)
    (dLim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      ↥cD.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q)
    (cLim : letI := (colimit.ι F i₀).hom.toAlgebra
      ↥cE.pt ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (μs : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      letI := aP
      (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
        (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμs : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j.val).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
              (colimit.w F (homOfLE (hi.trans j.property))) }
      (μs j).toRingHom =
        (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (hcD : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := aPs j
      letI := aP
      dLim.toRingHom.comp (cD.ι.app j).hom =
        (Algebra.TensorProduct.map (μs j) (AlgHom.id P Q)).toRingHom.comp
          (d j).toRingHom)
    (hDt : ∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
      letI := aPs j
      letI := aPs k
      ∃ β : (↥(F.obj j.val) ⊗[F.obj i₀] B₀) →ₐ[P]
          (↥(F.obj k.val) ⊗[F.obj i₀] B₀),
        (let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
          { (F.map (homOfLE (leOfHom r))).hom with
            commutes' := fun s ↦
              congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                (F.map_comp (homOfLE (hi.trans j.property))
                  (homOfLE (leOfHom r))).symm };
          β.toRingHom =
            (Algebra.TensorProduct.map αjk
              (AlgHom.id (F.obj i₀) B₀)).toRingHom) ∧
        (d k).toRingHom.comp (D.map r).hom =
          (Algebra.TensorProduct.map β (AlgHom.id P Q)).toRingHom.comp
            (d j).toRingHom)
    (hcE : ∀ j : {j : I // i ≤ j},
      letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      let αj : F.obj j.val →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j.val).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
              (colimit.w F (homOfLE (hi.trans j.property))) }
      cLim.toRingHom.comp (cE.ι.app j).hom =
        (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
          (c j).toRingHom)
    (hEt : ∀ {j k : {j : I // i ≤ j}} (r : j ⟶ k),
      letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
      letI := (F.map (homOfLE (hi.trans k.property))).hom.toAlgebra
      let αjk : F.obj j.val →ₐ[F.obj i₀] F.obj k.val :=
          { (F.map (homOfLE (leOfHom r))).hom with
            commutes' := fun s ↦
              congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
                (F.map_comp (homOfLE (hi.trans j.property))
                  (homOfLE (leOfHom r))).symm }
      (c k).toRingHom.comp (E.map r).hom =
        (Algebra.TensorProduct.map αjk (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp
          (c j).toRingHom)
    : Nonempty (IsColimit cD) ∧ Nonempty (IsColimit cE) := by
  classical
  let J := {j : I // i ≤ j}
  let : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let : IsFiltered J := inferInstance
  let : HasColimitsOfSize.{v, v} CommRingCat.{max v w x y} :=
    hasColimitsOfSizeOfUnivLE.{max v w x y, max v w x y} _
  let : PreservesFilteredColimitsOfSize.{v, v}
      (forget CommRingCat.{max v w x y}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max v w x y, max v w x y} _
  let S := F.obj i₀
  let : Algebra S ↥(colimit F) := (colimit.ι F i₀).hom.toAlgebra
  let : ∀ j : J, Algebra S (F.obj j.val) :=
    fun j ↦ (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
  let Bs : J → Type (max v w) := fun j ↦ ↥(F.obj j.val) ⊗[S] B₀
  let B := ↥(colimit F) ⊗[S] B₀
  let : Algebra P B := aP
  let : ∀ j, Algebra P (Bs j) := aPs
  let α (j : J) : F.obj j.val →ₐ[S] ↥(colimit F) :=
    { (colimit.ι F j.val).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE (hi.trans j.property))) }
  let τ (j k : J) (h : j ≤ k) : F.obj j.val →ₐ[S] F.obj k.val :=
    { (F.map (homOfLE h)).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj k.val ↦ f s)
        (F.map_comp (homOfLE (hi.trans j.property)) (homOfLE h)).symm }
  let γ (j : J) := Algebra.TensorProduct.map (α j) (AlgHom.id S B₀)
  let γt (j k : J) (h : j ≤ k) :=
    Algebra.TensorProduct.map (τ j k h) (AlgHom.id S B₀)
  let β (j k : J) (h : j ≤ k) : Bs j →ₐ[P] Bs k := (hDt (homOfLE h)).choose
  have β_eq (j k : J) (h : j ≤ k) (t : Bs j) : β j k h t = γt j k h t :=
    DFunLike.congr_fun (hDt (homOfLE h)).choose_spec.1 t
  have μ_eq (j : J) (t : Bs j) : μs j t = γ j t :=
    DFunLike.congr_fun (hμs j) t
  let f (j k : J) (h : j ≤ k) := (β j k h).toLinearMap
  let : DirectedSystem Bs (fun {j k} h ↦ f j k h) :=
    { map_self := by
        intro j t
        change β j j le_rfl t = t
        rw [β_eq]
        induction t using TensorProduct.inductionOn with
        | tmul a b =>
          change (F.map (homOfLE (le_refl j.val))).hom a ⊗ₜ[S] b = a ⊗ₜ[S] b
          simp
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
      map_map := by
        intro l k j hjk hkl t
        change β k l hkl (β j k hjk t) = β j l (hjk.trans hkl) t
        simp only [β_eq]
        induction t using TensorProduct.inductionOn with
        | tmul a b =>
          change (F.map (homOfLE hkl)).hom ((F.map (homOfLE hjk)).hom a) ⊗ₜ[S] b =
            (F.map (homOfLE (hjk.trans hkl))).hom a ⊗ₜ[S] b
          exact congrArg (fun a ↦ a ⊗ₜ[S] b)
            (ConcreteCategory.congr_hom (F.map_comp (homOfLE hjk) (homOfLE hkl)) a).symm
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu }
  have μcompat (j k : J) (h : j ≤ k) (t : Bs j) :
      μs k (f j k h t) = μs j t := by
    change μs k (β j k h t) = μs j t
    simp only [μ_eq, β_eq]
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      change (colimit.ι F k.val).hom ((F.map (homOfLE h)).hom a) ⊗ₜ[S] b =
        (colimit.ι F j.val).hom a ⊗ₜ[S] b
      exact congrArg (fun a ↦ a ⊗ₜ[S] b)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a)
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  obtain ⟨hBs, hBz⟩ := tail_rep_zero F i₀ B₀ i hi
  have Bs_rep (x : B) : ∃ j t, μs j t = x := by
    obtain ⟨j, hj, t, ht⟩ := hBs x
    refine ⟨⟨j, hj⟩, t, ?_⟩
    rw [μ_eq]
    exact ht
  have Bs_zero (j : J) (t : Bs j) (ht : μs j t = 0) :
      ∃ (k : J) (h : j ≤ k), f j k h t = 0 := by
    rw [μ_eq] at ht
    obtain ⟨k, hjk, hk⟩ := hBz j.val j.property t ht
    let k' : J := ⟨k, j.property.trans hjk⟩
    refine ⟨k', hjk, ?_⟩
    change β j k' hjk t = 0
    rw [β_eq]
    exact hk
  obtain ⟨hDs, hDz⟩ := tensor_rep_zero P Bs f B (fun j ↦ (μs j).toLinearMap)
    μcompat Bs_rep Bs_zero Q
  have hE : Nonempty (IsColimit cE) := by
    obtain ⟨hCs, hCz⟩ := tail_rep_zero F i₀ C₀ i hi
    apply colimit_of_rep_zero E cE
    · intro x
      obtain ⟨j, hj, t, ht⟩ := hCs (cLim x)
      let j' : J := ⟨j, hj⟩
      refine ⟨j', (c j').symm t, ?_⟩
      apply cLim.injective
      have hc := DFunLike.congr_fun (hcE j') ((c j').symm t)
      change cLim ((cE.ι.app j').hom ((c j').symm t)) =
        (α j').toLinearMap.rTensor C₀ (c j' ((c j').symm t)) at hc
      rw [RingEquiv.apply_symm_apply] at hc
      exact hc.trans ht
    · intro j t ht
      have hz : (Algebra.TensorProduct.map (α j) (AlgHom.id S C₀)) (c j t) = 0 := by
        have hc := DFunLike.congr_fun (hcE j) t
        change cLim ((cE.ι.app j).hom t) =
          (Algebra.TensorProduct.map (α j) (AlgHom.id S C₀)) (c j t) at hc
        rw [ht, map_zero] at hc
        exact hc.symm
      obtain ⟨k, hjk, hk⟩ := hCz j.val j.property (c j t) hz
      let k' : J := ⟨k, j.property.trans hjk⟩
      refine ⟨k', homOfLE hjk, ?_⟩
      apply (c k').injective
      have hc := DFunLike.congr_fun (hEt (homOfLE (show j ≤ k' from hjk))) t
      change c k' ((E.map (homOfLE hjk)).hom t) =
        (τ j k' hjk).toLinearMap.rTensor C₀ (c j t) at hc
      change c k' ((E.map (homOfLE hjk)).hom t) = c k' 0
      rw [map_zero]
      exact hc.trans hk
  have hD : Nonempty (IsColimit cD) := by
    apply colimit_of_rep_zero D cD
    · intro x
      obtain ⟨j, t, ht⟩ := hDs (dLim x)
      refine ⟨j, (d j).symm t, ?_⟩
      apply dLim.injective
      have hc := DFunLike.congr_fun (hcD j) ((d j).symm t)
      change dLim ((cD.ι.app j).hom ((d j).symm t)) =
        (μs j).toLinearMap.rTensor Q (d j ((d j).symm t)) at hc
      rw [RingEquiv.apply_symm_apply] at hc
      exact hc.trans ht
    · intro j t ht
      have hz : (μs j).toLinearMap.rTensor Q (d j t) = 0 := by
        have hc := DFunLike.congr_fun (hcD j) t
        change dLim ((cD.ι.app j).hom t) =
          (μs j).toLinearMap.rTensor Q (d j t) at hc
        rw [ht, map_zero] at hc
        exact hc.symm
      obtain ⟨k, hjk, hk⟩ := hDz j (d j t) hz
      refine ⟨k, homOfLE hjk, ?_⟩
      apply (d k).injective
      have hc := DFunLike.congr_fun (hDt (homOfLE hjk)).choose_spec.2 t
      change d k ((D.map (homOfLE hjk)).hom t) =
        (f j k hjk).rTensor Q (d j t) at hc
      change d k ((D.map (homOfLE hjk)).hom t) = d k 0
      rw [map_zero]
      exact hc.trans hk
  exact ⟨hD, hE⟩

end RingHom
