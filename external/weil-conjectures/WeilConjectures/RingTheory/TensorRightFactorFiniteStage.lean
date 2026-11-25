/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import Mathlib.Data.Finset.Order

/-! # Descending the right factor after descending the coefficient structure

Source: Stacks Project, Algebra, Tags 02JO (3), 00QO and 00DD.
(blueprint: lem-weil-pbc-tensor-right-factor-finite-stage)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Once the P-structure is descended, a P-linear map out of Q descends later.

Source: Stacks Project, Algebra, Tag 02JO (3), the construction of Ψ;
Tag 00QO (lemma-characterize-finite-presentation) and Tag 00DD.
(blueprint: lem-weil-pbc-tensor-right-factor-finite-stage)

Proof: on the upper tail of j, equip Bᵢ with the ring map P → Bⱼ → Bᵢ
and Cᵢ with its composite with id ⊗ φ₀. Tensor induction proves transition
composition, compatibility with limit maps, and the two squares involving φ₀.
The hypothesis on μBj makes Bᵢ → B P-linear. The same squares prove that
Cᵢ → C and all C transition maps are P-linear for the induced P-structures.
Regard f as a P-algebra homomorphism using hf. The elementwise base-change
lemma gives representatives on the upper tail of i₀; move each to a common
upper bound with j to obtain representatives on the chosen tail. It also gives
eventual vanishing on this tail. Choose a finite polynomial presentation of Q
over P. Lift its finitely many generators to a common C stage and evaluate
polynomials using the descended P-structure. Polynomial extensionality proves
that this evaluation maps to f composed with the presentation. Advance to a
common stage killing all kernel generators, and descend the resulting
polynomial map through the surjective presentation. The descended map q
factors f. To check its P-linearity, compare a polynomial representative of
algebraMap P Q r with the constant polynomial r: their difference belongs to
the kernel, which the evaluation kills. P-linearity of the transition map then
gives q(algebraMap P Q r) = algebraMap P Cᵢ r. Retain the constructed
P-structure on Bᵢ and its canonical P-linear map μB. This constructs only
q : Q → Cᵢ, leaving tensor assembly to the comparison theorem. Empty finite
presentations and zero rings use the same finite bounds and kernel argument.
-/
theorem exists_tensor_right_factor_finite_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (j : I) (hj : i₀ ≤ j)
    (aPj : letI := (F.map (homOfLE hj)).hom.toAlgebra
      Algebra P (↥(F.obj j) ⊗[F.obj i₀] B₀))
    (μBj : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hj)).hom.toAlgebra
      letI := aPj
      letI := aP
      (↥(F.obj j) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμBj : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hj)).hom.toAlgebra
      let αj : F.obj j →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F j).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hj)) }
      μBj.toRingHom =
        (Algebra.TensorProduct.map αj (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (f : letI := (colimit.ι F i₀).hom.toAlgebra
      Q →+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (hf : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      f.comp (algebraMap P Q) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom.comp
          (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀))) :
    ∃ (i : I) (hi : i₀ ≤ i),
    letI := (colimit.ι F i₀).hom.toAlgebra
    letI := (F.map (homOfLE hi)).hom.toAlgebra
    let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F i).hom with
        commutes' := fun s ↦
          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
    ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)),
      letI := aPi
      letI := aP
      ∃ (μB : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
          (↥(colimit F) ⊗[F.obj i₀] B₀)),
        μB.toRingHom =
          (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom ∧
        ∃ (q : Q →+* (↥(F.obj i) ⊗[F.obj i₀] C₀)),
          q.comp (algebraMap P Q) =
            (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom.comp
              (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀)) ∧
          (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp q = f
    := by
  classical
  let := (colimit.ι F i₀).hom.toAlgebra
  let := aP
  let J := {i : I // j ≤ i}
  let : Nonempty J := ⟨⟨j, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let h₀ (i : J) := hj.trans i.property
  let B (i : J) :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    ↥(F.obj i.val) ⊗[F.obj i₀] C₀
  let : ∀ i, CommRing (B i) := fun i ↦ by dsimp [B]; infer_instance
  let α (i : J) :
      let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
      F.obj i.val →ₐ[F.obj i₀] ↥(colimit F) :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    { (colimit.ι F i.val).hom with
      commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s)
        (colimit.w F (homOfLE (h₀ i))) }
  let μ (i : J) : B i →+* (↥(colimit F) ⊗[F.obj i₀] C₀) :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    (Algebra.TensorProduct.map (α i) (AlgHom.id (F.obj i₀) C₀)).toRingHom
  let t (i j : J) (h : i ≤ j) : B i →+* B j :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    let := (F.map (homOfLE (h₀ j))).hom.toAlgebra
    let β : F.obj i.val →ₐ[F.obj i₀] F.obj j.val :=
      { (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj j.val ↦ f s)
          (F.map_comp (homOfLE (h₀ i)) (homOfLE h)).symm }
    (Algebra.TensorProduct.map β (AlgHom.id (F.obj i₀) C₀)).toRingHom
  have compat (i j : J) (h : i ≤ j) : (μ j).comp (t i j h) = μ i := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      dsimp [μ, t]
      exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a)
    | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
  have trans (i j k : J) (hij : i ≤ j) (hjk : j ≤ k) :
      (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk) := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      let := (F.map (homOfLE (h₀ k))).hom.toAlgebra
      dsimp [t]
      exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
        (ConcreteCategory.congr_hom (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm
    | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
  let Bj (i : J) :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    ↥(F.obj i.val) ⊗[F.obj i₀] B₀
  let : ∀ i, CommRing (Bj i) := fun i ↦ by dsimp [Bj]; infer_instance
  let μB (i : J) : Bj i →+* (↥(colimit F) ⊗[F.obj i₀] B₀) :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    (Algebra.TensorProduct.map (α i) (AlgHom.id (F.obj i₀) B₀)).toRingHom
  let tjB (i : J) :
      (let := (F.map (homOfLE hj)).hom.toAlgebra
       ↥(F.obj j) ⊗[F.obj i₀] B₀) →+* Bj i :=
    let := (F.map (homOfLE hj)).hom.toAlgebra
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    let β : F.obj j →ₐ[F.obj i₀] F.obj i.val :=
      { (F.map (homOfLE i.property)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj i.val ↦ f s)
          (F.map_comp (homOfLE hj) (homOfLE i.property)).symm }
    (Algebra.TensorProduct.map β (AlgHom.id (F.obj i₀) B₀)).toRingHom
  let pB (i : J) : P →+* Bj i :=
    let := (F.map (homOfLE hj)).hom.toAlgebra
    let := aPj
    (tjB i).comp (algebraMap P (↥(F.obj j) ⊗[F.obj i₀] B₀))
  have pBcompat (i : J) : (μB i).comp (pB i) =
      algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) := by
    have square : (μB i).comp (tjB i) = μBj.toRingHom := by
      rw [hμBj]
      apply RingHom.ext
      intro z
      let := (F.map (homOfLE hj)).hom.toAlgebra
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        dsimp [μB, tjB, α]
        exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
          (ConcreteCategory.congr_hom (colimit.w F (homOfLE i.property)) a)
      | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
    dsimp only [pB]
    rw [← RingHom.comp_assoc, square]
    exact μBj.comp_algebraMap
  let φ (i : J) : Bj i →+* B i :=
    let := (F.map (homOfLE (h₀ i))).hom.toAlgebra
    (Algebra.TensorProduct.map (Algebra.ofId (F.obj i.val) (F.obj i.val)) φ₀).toRingHom
  let φlim :=
    (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom
  have φsquare (i : J) : (μ i).comp (φ i) = φlim.comp (μB i) := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
  let pC (i : J) := (φ i).comp (pB i)
  let pClim := φlim.comp (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀))
  have pCtrans (i k : J) (hik : i ≤ k) (r : P) : t i k hik (pC i r) = pC k r := by
    let := (F.map (homOfLE hj)).hom.toAlgebra
    let := aPj
    have square (z : ↥(F.obj j) ⊗[F.obj i₀] B₀) :
        t i k hik (φ i (tjB i z)) = φ k (tjB k z) := by
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        let := (F.map (homOfLE (h₀ k))).hom.toAlgebra
        dsimp [t, φ, tjB]
        exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] φ₀ b)
          (ConcreteCategory.congr_hom
            (F.map_comp (homOfLE i.property) (homOfLE hik)) a).symm
      | add z u hz hu => simpa only [map_add] using congrArg₂ (· + ·) hz hu
    exact square (algebraMap P (↥(F.obj j) ⊗[F.obj i₀] B₀) r)
  let : ∀ i, Algebra P (B i) := fun i ↦ (pC i).toAlgebra
  let := pClim.toAlgebra
  have pCcompat (i : J) : (μ i).comp (pC i) = pClim := by
    dsimp only [pC, pClim]
    rw [← RingHom.comp_assoc, φsquare, RingHom.comp_assoc, pBcompat]
  let μP (i : J) : B i →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] C₀) :=
    { μ i with commutes' := fun r ↦ RingHom.congr_fun (pCcompat i) r }
  let fP : Q →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] C₀) :=
    { f with commutes' := fun r ↦ RingHom.congr_fun hf r }
  have rep (z : ↥(colimit F) ⊗[F.obj i₀] C₀) : ∃ i : J, ∃ x : B i, μ i x = z := by
    obtain ⟨i, hi, x, hx⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ C₀).1 z
    obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
    let ik : J := ⟨k, hjk⟩
    let := (F.map (homOfLE hi)).hom.toAlgebra
    let := (F.map (homOfLE (h₀ ik))).hom.toAlgebra
    let β : F.obj i →ₐ[F.obj i₀] F.obj k :=
      { (F.map (homOfLE hik)).hom with
        commutes' := fun s ↦ congrArg (fun f : F.obj i₀ ⟶ F.obj k ↦ f s)
          (F.map_comp (homOfLE hi) (homOfLE hik)).symm }
    refine ⟨ik, Algebra.TensorProduct.map β (AlgHom.id (F.obj i₀) C₀) x, ?_⟩
    rw [← hx]
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      dsimp [μ, α, β]
      exact congrArg (fun a ↦ a ⊗ₜ[F.obj i₀] b)
        (ConcreteCategory.congr_hom (colimit.w F (homOfLE hik)) a)
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  have vanish (i : J) (z : B i) (hz : μ i z = 0) :
      ∃ (j : J) (h : i ≤ j), t i j h z = 0 := by
    obtain ⟨j, hij, he⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise F i₀ C₀).2 i.val (h₀ i) z hz
    exact ⟨⟨j, i.property.trans hij⟩, hij, he⟩
  obtain ⟨n, π, hπ, s, hs⟩ := Algebra.FinitePresentation.out (R := P) (A := Q)
  choose l x hx using fun k : Fin n ↦ rep (fP (π (MvPolynomial.X k)))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image l)
  have hli (k : Fin n) : l k ≤ i := hi _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  let p : MvPolynomial (Fin n) P →+* B i :=
    MvPolynomial.eval₂Hom (algebraMap P (B i)) (fun k ↦ t (l k) i (hli k) (x k))
  have hp : (μ i).comp p = fP.toRingHom.comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp only [RingHom.comp_apply, p, MvPolynomial.eval₂Hom_C]
      change μP i (algebraMap P (B i) z) = fP (π (MvPolynomial.C z))
      rw [(μP i).commutes]
      simp
    · intro k
      simp only [RingHom.comp_apply, p, MvPolynomial.eval₂Hom_X', AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom]
      change μ i (t (l k) i (hli k) (x k)) = fP (π (MvPolynomial.X k))
      exact (RingHom.congr_fun (compat (l k) i (hli k)) (x k)).trans (hx k)
  have relations (r : s) : ∃ (j : J) (h : i ≤ j), t i j h (p r) = 0 := by
    apply vanish
    have hr : π r = 0 := hs.le (Ideal.subset_span r.property)
    exact (RingHom.congr_fun hp r).trans (by simp [hr])
  choose j hij hj using relations
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (r : s) : j r ≤ k := hk _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩))
  let pk := (t i k hik).comp p
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker pk := by
    rw [← hs, Ideal.span_le]
    intro r hr
    change t i k hik (p r) = 0
    let r' : s := ⟨r, hr⟩
    rw [← trans i (j r') k (hij r') (hjk r')]
    change t (j r') k (hjk r') (t i (j r') (hij r') (p r')) = 0
    rw [hj, map_zero]
  let pP : Q →+* B k := RingHom.liftOfSurjective π.toRingHom hπ ⟨pk, hker⟩
  have hfactor : (μ k).comp pP = f := by
    apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := hπ z
    change μ k (pP (π z)) = f (π z)
    rw [show pP (π z) = pk z from
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ _]
    change μ k (t i k hik (p z)) = f (π z)
    exact (RingHom.congr_fun (compat i k hik) (p z)).trans (RingHom.congr_fun hp z)
  have hq : pP.comp (algebraMap P Q) = pC k := by
    apply RingHom.ext
    intro r
    obtain ⟨z, hz⟩ := hπ (algebraMap P Q r)
    have hc : π (MvPolynomial.C r) = algebraMap P Q r := by simp
    have hrel : z - MvPolynomial.C r ∈ RingHom.ker π.toRingHom := by
      change π (z - MvPolynomial.C r) = 0
      rw [map_sub, hz, hc, sub_self]
    have hzero := hker hrel
    have hpk : pk z = pk (MvPolynomial.C r) := by
      have : pk (z - MvPolynomial.C r) = 0 := hzero
      simpa only [map_sub, sub_eq_zero] using this
    change pP (algebraMap P Q r) = pC k r
    rw [← hz]
    rw [show pP (π z) = pk z from RingHom.liftOfRightInverse_comp_apply _ _ _ _ _]
    rw [hpk]
    change t i k hik (p (MvPolynomial.C r)) = pC k r
    rw [show p (MvPolynomial.C r) = pC i r from MvPolynomial.eval₂Hom_C _ _ r]
    exact pCtrans i k hik r
  let := (pB k).toAlgebra
  let μBk : Bj k →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀) :=
    { μB k with commutes' := fun r ↦ RingHom.congr_fun (pBcompat k) r }
  exact ⟨k.val, h₀ k, (pB k).toAlgebra, μBk, rfl, pP, hq, hfactor⟩

end RingHom
