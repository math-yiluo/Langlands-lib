/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JacobiZariskiHomologySequence
import WeilConjectures.FieldTheory.FieldExtensionCompleteIntersectionSubalgebras
import WeilConjectures.RingTheory.JacobiZariskiRegularSequenceLeftInjective

/-!
# Left exactness of the Jacobi–Zariski sequence for fields

Source: Stacks Project, More on Algebra, Tag 07E2, `lemma-transitivity-gamma`
(blueprint: lem-weil-pbc-transitivity-gamma).
-/

@[expose] public section

universe u v w

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
open _root_.TensorProduct in
private theorem left_injective_at_regular_stage
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [Field B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (n : ℕ) (fs : List (MvPolynomial (Fin n) B))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) B) fs)
    (β : MvPolynomial (Fin n) B →ₐ[B] C)
    (hβ : Function.Surjective β) (hker : RingHom.ker β.toRingHom = Ideal.ofList fs) :
    Function.Injective ((H1Cotangent.map A A B C).liftBaseChange C) := by
  let P := (Generators.self A B).toExtension
  let Q := (Generators.self A C).toExtension
  obtain ⟨j, hj, hinj⟩ :=
    jacobiZariski_left_injective_of_regularSequence A B C n fs hreg β hβ hker
  let t : C ⊗[B] H1Cotangent A B →ₗ[C] (P.cotangentComplex.baseChange C).ker :=
    { toFun := fun x ↦ ⟨(LinearMap.lTensor C P.h1Cotangentι) x, by
        change P.cotangentComplex.baseChange C ((LinearMap.lTensor C P.h1Cotangentι) x) = 0
        induction x using TensorProduct.inductionOn with
        | tmul c h => simp [P, LinearMap.baseChange_tmul]
        | add x y hx hy => simp [hx, hy]⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := by
        intro c x
        apply Subtype.ext
        change (LinearMap.lTensor C P.h1Cotangentι) (c • x) =
          c • (LinearMap.lTensor C P.h1Cotangentι) x
        induction x using TensorProduct.inductionOn with
        | tmul c' h => simp [smul_tmul']
        | add x y hx hy => simp [smul_add, hx, hy] }
  have ht : Function.Injective t := by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap P.h1Cotangentι
      P.h1Cotangentι_injective (congrArg Subtype.val hxy)
  have hcomp (x : C ⊗[B] H1Cotangent A B) :
      j (t x) = (H1Cotangent.map A A B C).liftBaseChange C x := by
    apply Q.h1Cotangentι_injective
    rw [hj]
    induction x using TensorProduct.inductionOn with
    | tmul c h => rfl
    | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  intro x y hxy
  apply ht
  apply hinj
  rw [hcomp, hcomp, hxy]

set_option backward.isDefEq.respectTransparency false in
open _root_.TensorProduct in
private theorem eval_rename_subalgebra
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (S : Subalgebra B C) (p : MvPolynomial S A) :
    algebraMap S C (MvPolynomial.aeval _root_.id p) =
      MvPolynomial.aeval _root_.id (MvPolynomial.rename (Subtype.val : S → C) p) := by
  rw [MvPolynomial.aeval_rename]
  exact MvPolynomial.comp_aeval_apply (_root_.id : S → S) (S.val.restrictScalars A) p

set_option backward.isDefEq.respectTransparency false in
open _root_.TensorProduct in
private theorem relation_square_finite_support
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (g : MvPolynomial C A) (hg : g ∈ (Generators.self A C).ker ^ 2) :
    ∃ E : Finset C, ∀ S : Subalgebra B C, (∀ c ∈ E, c ∈ S) →
      ∃ q : MvPolynomial S A,
        MvPolynomial.rename (Subtype.val : S → C) q = g ∧
        q ∈ (Generators.self A S).ker ^ 2 := by
  classical
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg ?_ ?_
  · intro p hp q hq
    refine ⟨p.vars ∪ q.vars, ?_⟩
    intro S hS
    obtain ⟨p', hp'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
      (Subtype.val : S → C) Subtype.val_injective (by
        intro c hc
        exact ⟨⟨c, hS c (Finset.mem_union_left _ hc)⟩, rfl⟩)
    obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q
      (Subtype.val : S → C) Subtype.val_injective (by
        intro c hc
        exact ⟨⟨c, hS c (Finset.mem_union_right _ hc)⟩, rfl⟩)
    have descend (r : MvPolynomial C A) (hr : r ∈ (Generators.self A C).ker)
        (r' : MvPolynomial S A) (hr' : MvPolynomial.rename Subtype.val r' = r) :
        r' ∈ (Generators.self A S).ker := by
      rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
      apply (show Function.Injective (algebraMap S C) from Subtype.val_injective)
      rw [map_zero]
      change algebraMap S C (MvPolynomial.aeval _root_.id r') = 0
      rw [eval_rename_subalgebra A B C S, hr']
      exact Generators.aeval_val_eq_zero (P := Generators.self A C) hr
    refine ⟨p' * q', by simp [hp', hq'], ?_⟩
    rw [pow_two]
    exact Ideal.mul_mem_mul (descend p hp p' hp') (descend q hq q' hq')
  · intro x y hx hy
    obtain ⟨E, hE⟩ := hx
    obtain ⟨F, hF⟩ := hy
    refine ⟨E ∪ F, ?_⟩
    intro S hS
    obtain ⟨p, hp, hpker⟩ := hE S (fun c hc ↦ hS c (Finset.mem_union_left _ hc))
    obtain ⟨q, hq, hqker⟩ := hF S (fun c hc ↦ hS c (Finset.mem_union_right _ hc))
    exact ⟨p + q, by simp [hp, hq], Ideal.add_mem _ hpker hqker⟩

set_option backward.isDefEq.respectTransparency false in
open _root_.TensorProduct in
private theorem canonical_conormal_tmul
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (c : C) (h : H1Cotangent A B) (g : (Generators.self A B).ker)
    (hg : Extension.Cotangent.mk g = h.val) :
    ∃ hg' : MvPolynomial.X c * MvPolynomial.rename (algebraMap B C) g.val ∈
        (Generators.self A C).ker,
      (((H1Cotangent.map A A B C).liftBaseChange C) (c ⊗ₜ[B] h)).val =
        Extension.Cotangent.mk ⟨_, hg'⟩ := by
  let P := Generators.self A B
  let Q := Generators.self A C
  let f := (Generators.defaultHom P Q).toExtensionHom
  have hf : f.toAlgHom = MvPolynomial.rename (algebraMap B C) := by
    apply MvPolynomial.algHom_ext
    intro b
    change (MvPolynomial.aeval (fun b ↦ MvPolynomial.X (R := A) (algebraMap B C b)))
      (MvPolynomial.X b) = (MvPolynomial.rename (algebraMap B C)) (MvPolynomial.X b)
    rw [MvPolynomial.aeval_X, MvPolynomial.rename_X]
  have hg' : MvPolynomial.X c * MvPolynomial.rename (algebraMap B C) g.val ∈ Q.ker := by
    apply Q.ker.mul_mem_left
    change MvPolynomial.rename (algebraMap B C) g.val ∈ Q.ker
    rw [← hf]
    change algebraMap Q.toExtension.Ring C (f.toRingHom g.val) = 0
    rw [f.algebraMap_toRingHom]
    change algebraMap B C (MvPolynomial.aeval _root_.id g.val) = 0
    have hg0 := Generators.aeval_val_eq_zero (P := P) g.property
    change MvPolynomial.aeval _root_.id g.val = 0 at hg0
    rw [hg0, map_zero]
  refine ⟨hg', ?_⟩
  change c • Extension.Cotangent.map f h.val = _
  rw [← hg, Extension.Cotangent.map_mk]
  apply Extension.Cotangent.ext
  rw [Extension.Cotangent.val_smul, Extension.Cotangent.val_mk,
    Extension.Cotangent.val_mk]
  change MvPolynomial.X c • Ideal.toCotangent Q.ker _ = Ideal.toCotangent Q.ker _
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul, smul_eq_mul, hf]
  rfl

set_option backward.isDefEq.respectTransparency false in
open _root_.TensorProduct in
private theorem tensor_conormal_finite_support
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (x : C ⊗[B] H1Cotangent A B) :
    ∃ g : (Generators.self A C).ker,
      (((H1Cotangent.map A A B C).liftBaseChange C) x).val =
        Extension.Cotangent.mk g ∧
      ∃ E : Finset C, ∀ S : Subalgebra B C, (∀ c ∈ E, c ∈ S) →
        ∃ (y : S ⊗[B] H1Cotangent A B) (q : (Generators.self A S).ker),
          _root_.TensorProduct.map S.val.toLinearMap LinearMap.id y = x ∧
          MvPolynomial.rename (Subtype.val : S → C) q.val = g.val ∧
          (((H1Cotangent.map A A B S).liftBaseChange S) y).val =
            Extension.Cotangent.mk q := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul c h =>
      obtain ⟨g, hg⟩ := Extension.Cotangent.mk_surjective h.val
      obtain ⟨hG, hGrep⟩ := canonical_conormal_tmul A B C c h g hg
      refine ⟨⟨_, hG⟩, hGrep, {c}, ?_⟩
      intro S hS
      let cS : S := ⟨c, hS c (Finset.mem_singleton_self _)⟩
      obtain ⟨hQ, hQrep⟩ := canonical_conormal_tmul A B S cS h g hg
      refine ⟨cS ⊗ₜ[B] h, ⟨_, hQ⟩, by simp [cS], ?_, hQrep⟩
      simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.rename_rename]
      congr 1
  | add x y hx hy =>
      obtain ⟨g, hg, E, hE⟩ := hx
      obtain ⟨h, hh, F, hF⟩ := hy
      refine ⟨g + h, ?_, E ∪ F, ?_⟩
      · simpa only [map_add, Extension.H1Cotangent.val_add] using congrArg₂ (· + ·) hg hh
      · intro S hS
        obtain ⟨xS, p, hxs, hp, hpmap⟩ :=
          hE S (fun c hc ↦ hS c (Finset.mem_union_left _ hc))
        obtain ⟨yS, q, hys, hq, hqmap⟩ :=
          hF S (fun c hc ↦ hS c (Finset.mem_union_right _ hc))
        refine ⟨xS + yS, p + q, ?_, ?_, ?_⟩
        · simp [hxs, hys]
        · simpa only [Submodule.coe_add, map_add] using congrArg₂ (· + ·) hp hq
        · simpa only [map_add, Extension.H1Cotangent.val_add] using
            congrArg₂ (· + ·) hpmap hqmap

open _root_.TensorProduct in
/-- Left injectivity in the transitivity sequence for a tower of fields.
Source: Stacks Project, More on Algebra, Tag 07E2, with the complete-intersection
subalgebra argument. The proof proceeds by descending a kernel element to a finite
complete-intersection subalgebra and applying the regular-sequence injectivity lemma.
(blueprint: lem-weil-pbc-transitivity-gamma) -/
private theorem transitivityGamma_left_injective
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    Function.Injective ((H1Cotangent.map K K L M).liftBaseChange M) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hx0 : (H1Cotangent.map K K L M).liftBaseChange M x = 0 := hx
  obtain ⟨g, hg, E, hE⟩ := tensor_conormal_finite_support K L M x
  have hg0 : Extension.Cotangent.mk (P := (Generators.self K M).toExtension) g = 0 := by
    rw [← hg, hx0]
    rfl
  have hgsq :=
    (Extension.Cotangent.mk_eq_zero_iff (P := (Generators.self K M).toExtension) g).mp hg0
  obtain ⟨F, hF⟩ := relation_square_finite_support K L M g.val hgsq
  obtain ⟨n, c, fs, _, hreg, ι, hι, hEF⟩ :=
    FieldTheory.exists_completeIntersection_subalgebra L M (E ∪ F)
  let S : Subalgebra L M := ι.range
  have hS : ∀ m ∈ E ∪ F, m ∈ S := by
    intro m hm
    exact hEF m hm
  obtain ⟨y, q, hy, hq, hqrep⟩ :=
    hE S (fun m hm ↦ hS m (Finset.mem_union_left _ hm))
  obtain ⟨r, hr, hrsq⟩ :=
    hF S (fun m hm ↦ hS m (Finset.mem_union_right _ hm))
  have hqr : q.val = r := MvPolynomial.rename_injective _ Subtype.val_injective (hq.trans hr.symm)
  have hq0 : Extension.Cotangent.mk (P := (Generators.self K S).toExtension) q = 0 :=
    (Extension.Cotangent.mk_eq_zero_iff (P := (Generators.self K S).toExtension) q).mpr (hqr ▸ hrsq)
  have hy0 : (H1Cotangent.map K K L S).liftBaseChange S y = 0 := by
    apply Subtype.ext
    rw [hqrep, hq0]
    rfl
  let β : MvPolynomial (Fin n) L →ₐ[L] S :=
    ι.rangeRestrict.comp (Ideal.Quotient.mkₐ L (Ideal.ofList fs))
  have hβ : Function.Surjective β :=
    ι.rangeRestrict_surjective.comp (Ideal.Quotient.mkₐ_surjective L _)
  have hker : RingHom.ker β.toRingHom = Ideal.ofList fs := by
    ext p
    change β p = 0 ↔ p ∈ Ideal.ofList fs
    change ι.rangeRestrict (Ideal.Quotient.mkₐ L (Ideal.ofList fs) p) = 0 ↔ _
    rw [← map_zero ι.rangeRestrict]
    rw [(show Function.Injective ι.rangeRestrict from
      fun a b hab ↦ hι (congrArg Subtype.val hab)).eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hinj := left_injective_at_regular_stage K L S n fs hreg β hβ hker
  have hyzero : y = 0 := hinj (hy0.trans (map_zero _).symm)
  rw [← hy, hyzero, map_zero]
  exact Submodule.zero_mem _


/-- Source: Stacks Project, More on Algebra, Tag 07E2, `lemma-transitivity-gamma`
(blueprint: lem-weil-pbc-transitivity-gamma).

For a tower of fields, the entire Jacobi–Zariski sequence is exact, including its left
endpoint. Tensor factors are written with `M` first, as in
`Algebra.jacobiZariski_homology_sequence`; the symmetry sends `h ⊗ c` to `c ⊗ h`.
The left map sends `c ⊗ h` to `c • H1Cotangent.map K K L M h`, the map induced by
`K[L] → K[M]` on canonical presentations.

Proof, following Stacks Tags 07E2, 07D5, 07D4, 07BQ, and 07BV:
1. Mathlib proves the five exactness and surjectivity clauses, including exactness
   at the first homology of M/K since M is flat over the field L.
2. At a regular-sequence presentation over L, use
   `jacobiZariski_left_injective_of_regularSequence`. Tensoring the inclusion of
   H1 into the conormal module is injective because every L-module is flat.
   The formula on pure tensors identifies the resulting composite with the
   canonical base-change map, proving injectivity at that finite stage.
3. By tensor induction, express an arbitrary tensor x by a polynomial relation g
   representing its image in the conormal module. Choose the finite set E of its
   tensor coefficients. For every subalgebra containing E, construct a tensor y
   and a polynomial q representing its image, with y mapping to x and q to g.
4. If x is in the kernel, g belongs to the square of the presentation ideal.
   Induction on membership in the product ideal supplies a finite set F of
   variables supporting the relation factors. In every subalgebra containing F,
   g lifts to a member of the square of that subalgebra's presentation ideal.
   Evaluation commutes with variable renaming, and the subalgebra inclusion is
   injective, so all lifted factors remain relations.
5. Apply `FieldTheory.exists_completeIntersection_subalgebra` to E union F.
   Its embedded quotient has image S with the required regular presentation.
   Injectivity of variable renaming identifies the two lifted representatives;
   hence the tensor y is in the kernel at S. Step 2 gives y = 0, and therefore
   x = 0. Combine this injectivity with step 1. -/
theorem transitivityGamma
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    Function.Injective ((H1Cotangent.map K K L M).liftBaseChange M) ∧
      Function.Exact ((H1Cotangent.map K K L M).liftBaseChange M)
        (H1Cotangent.map K L M M) ∧
      Function.Exact (H1Cotangent.map K L M M) (H1Cotangent.δ K L M) ∧
      Function.Exact (H1Cotangent.δ K L M) (KaehlerDifferential.mapBaseChange K L M) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange K L M)
        (KaehlerDifferential.map K L M M) ∧
      Function.Surjective (KaehlerDifferential.map K L M M) := by
  refine ⟨transitivityGamma_left_injective K L M, ?_⟩
  exact ⟨H1Cotangent.exact_liftBaseChange_map_of_flat K L M,
    H1Cotangent.exact_map_δ K L M,
    H1Cotangent.exact_δ_mapBaseChange K L M,
    KaehlerDifferential.exact_mapBaseChange_map K L M,
    KaehlerDifferential.map_surjective K L M⟩

end Algebra
