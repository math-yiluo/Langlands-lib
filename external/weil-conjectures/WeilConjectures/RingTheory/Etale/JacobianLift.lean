/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Lifting étale algebras across a quotient

Let `I` be an ideal of a ring `A` and `B̄` an `A ⧸ I`-algebra with a square Jacobian
presentation `B̄ = (A ⧸ I)[x₁, …, xₘ] ⧸ (f̄₁, …, f̄ₘ)`. Choosing coefficientwise lifts
`fᵢ ∈ A[x₁, …, xₘ]` and putting `Δ = det (∂fᵢ / ∂xⱼ)`, the algebra
`Bˡⁱᶠᵗ = A[x₁, …, xₘ, t] ⧸ (f₁, …, fₘ, tΔ - 1)` is étale over `A` and reduces to `B̄` modulo `I`.
Since every étale algebra has a square Jacobian presentation, every étale `A ⧸ I`-algebra lifts
to an étale `A`-algebra, with no nilpotence assumption on `I` [Stacks 04D1].

## Main definitions

- `Algebra.SquareJacobianPresentation.Lift`: the algebra `Bˡⁱᶠᵗ`.
- `Algebra.SquareJacobianPresentation.reduction`: its map to `B̄`.

## Main statements

- `Algebra.SquareJacobianPresentation.etale_lift_and_ker_reduction_and_surjective`: `Bˡⁱᶠᵗ` is
  étale over `A` and `Bˡⁱᶠᵗ ⧸ I Bˡⁱᶠᵗ ≅ B̄` (`Algebra.SquareJacobianPresentation.reductionEquiv`).
- `Algebra.Etale.exists_etale_quotientEquiv`: every étale `A ⧸ I`-algebra lifts.
-/

@[expose] public section

universe t u v
open MvPolynomial

namespace Algebra.SquareJacobianPresentation

variable {A : Type u} [CommRing A] (I : Ideal A) {B : Type v} [CommRing B] [Algebra (A ⧸ I) B]
  {ι : Type t} [Fintype ι] [DecidableEq ι] (P : SquareJacobianPresentation (A ⧸ I) B ι)

/-- A coefficientwise lift to `A[xᵢ]` of the relation `f̄ᵢ` of `P`. -/
noncomputable def liftRelation (i : ι) : MvPolynomial ι A :=
  (map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (P.relation i)).choose

omit [DecidableEq ι] in
lemma map_liftRelation (i : ι) : map (Ideal.Quotient.mk I) (P.liftRelation I i) = P.relation i :=
  (map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (P.relation i)).choose_spec

/-- The Jacobian determinant `Δ = det (∂fᵢ / ∂xⱼ)` of the lifted relations. -/
noncomputable def liftJacobian : MvPolynomial ι A :=
  (Matrix.of fun i j : ι ↦ pderiv i (P.liftRelation I j)).det

/-- The relations `f₁, …, fₘ, tΔ - 1` of the lift, in the variables `xᵢ = X (some i)` and
`t = X none`. -/
noncomputable def liftRelations : Option ι → MvPolynomial (Option ι) A
  | some i => rename some (P.liftRelation I i)
  | none => X none * rename some (P.liftJacobian I) - 1

/-- **The lift of a square Jacobian presentation.** For a square Jacobian presentation
`B̄ = (A ⧸ I)[x₁, …, xₘ] ⧸ (f̄₁, …, f̄ₘ)`, with coefficientwise lifts `fᵢ ∈ A[x₁, …, xₘ]` and
`Δ = det (∂fᵢ / ∂xⱼ)`, this is `A[x₁, …, xₘ, t] ⧸ (f₁, …, fₘ, tΔ - 1)`. Its map to `B̄` is
`Algebra.SquareJacobianPresentation.reduction`, sending `t` to `Δ̄⁻¹`.
(blueprint: `proposition-extension-zero-restriction-closed-subscheme`) -/
abbrev Lift : Type (max t u) :=
  MvPolynomial (Option ι) A ⧸ Ideal.span (Set.range (P.liftRelations I))

/-- The square Jacobian presentation of `P.Lift I`, before the Jacobian is shown to be a unit. -/
noncomputable def liftPresentation :
    PreSubmersivePresentation A (P.Lift I) (Option ι) (Option ι) :=
  .naive _root_.id Function.injective_id

omit [Fintype ι] [DecidableEq ι] in
lemma pderiv_none_rename_some (p : MvPolynomial ι A) : pderiv none (rename some p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma jacobiMatrix_liftPresentation (i j : Option ι) :
    (P.liftPresentation I).jacobiMatrix i j = pderiv i (P.liftRelations I j) := by
  rw [PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

lemma jacobiMatrix_liftPresentation_det :
    (P.liftPresentation I).jacobiMatrix.det =
      rename some (P.liftJacobian I) * rename some (P.liftJacobian I) := by
  let e := Equiv.optionEquivSumPUnit.{t} ι
  rw [← Matrix.det_reindex_self e, ← Matrix.fromBlocks_toBlocks (Matrix.reindex e e _)]
  have h₂₁ : (Matrix.reindex e e (P.liftPresentation I).jacobiMatrix).toBlocks₂₁ = 0 := by
    ext ⟨⟩ j
    simp [Matrix.toBlocks₂₁, e, jacobiMatrix_liftPresentation, liftRelations,
      pderiv_none_rename_some]
  rw [h₂₁, Matrix.det_fromBlocks_zero₂₁, mul_comm]
  congr 1
  · rw [Matrix.det_unique]
    simp [Matrix.toBlocks₂₂, e, jacobiMatrix_liftPresentation, liftRelations,
      pderiv_none_rename_some]
  · have : (Matrix.reindex e e (P.liftPresentation I).jacobiMatrix).toBlocks₁₁ =
        (rename some : MvPolynomial ι A →ₐ[A] _).mapMatrix
          (Matrix.of fun i j : ι ↦ pderiv i (P.liftRelation I j)) := by
      ext i j
      simp [Matrix.toBlocks₁₁, e, jacobiMatrix_liftPresentation, liftRelations,
        pderiv_rename (Option.some_injective ι)]
    rw [this, ← AlgHom.map_det, liftJacobian]

lemma isUnit_jacobian_liftPresentation : IsUnit (P.liftPresentation I).jacobian := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacobiMatrix_liftPresentation_det,
    map_mul]
  have h : algebraMap (P.liftPresentation I).Ring (P.Lift I) (rename some (P.liftJacobian I)) *
      algebraMap (P.liftPresentation I).Ring (P.Lift I) (X none) = 1 := by
    rw [← map_mul, ← sub_eq_zero, mul_comm,
      ← map_one (algebraMap (P.liftPresentation I).Ring (P.Lift I)), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨none, rfl⟩)
  have h' := IsUnit.of_mul_eq_one _ h
  exact h'.mul h'

/-- The square Jacobian presentation `A[xᵢ, t] ⧸ (fᵢ, tΔ - 1)` of `P.Lift I`. -/
noncomputable def liftSquareJacobianPresentation :
    SquareJacobianPresentation A (P.Lift I) (Option ι) where
  toPreSubmersivePresentation := P.liftPresentation I
  jacobian_isUnit := P.isUnit_jacobian_liftPresentation I
  map_eq_id := rfl

/-- The lift `A[xᵢ, t] ⧸ (fᵢ, tΔ - 1)` is étale over `A`. -/
instance etale_lift : Etale A (P.Lift I) :=
  (P.liftSquareJacobianPresentation I).etale

/-- The Jacobian of `P` is the reduction of the Jacobian determinant of the lifted relations. -/
lemma jacobian_eq_aeval_map_liftJacobian :
    P.jacobian = aeval P.val (map (Ideal.Quotient.mk I) (P.liftJacobian I)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Generators.algebraMap_apply,
    liftJacobian, RingHom.map_det]
  congr 2
  refine Matrix.ext fun i j ↦ ?_
  rw [PreSubmersivePresentation.jacobiMatrix_apply, P.map_eq_id]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← pderiv_map,
    map_liftRelation]
  rfl

/-- The value of the lift-to-`B̄` evaluation on the variables: `xᵢ ↦ xᵢ`, `t ↦ Δ̄⁻¹`. -/
noncomputable def reductionVal : Option ι → B
  | some i => P.val i
  | none => ↑P.jacobian_isUnit.unit⁻¹

/-- The evaluation `A[xᵢ, t] → B̄`, `xᵢ ↦ xᵢ`, `t ↦ Δ̄⁻¹`. -/
noncomputable def reductionAux : MvPolynomial (Option ι) A →+* B :=
  eval₂Hom ((algebraMap (A ⧸ I) B).comp (Ideal.Quotient.mk I)) (P.reductionVal I)

omit [DecidableEq ι] in
lemma reductionAux_rename_some (p : MvPolynomial ι A) :
    P.reductionAux I (rename some p) = aeval P.val (map (Ideal.Quotient.mk I) p) := by
  simp only [reductionAux, coe_eval₂Hom, eval₂_rename, aeval_def, eval₂_map]
  rfl

lemma span_le_ker_reductionAux :
    Ideal.span (Set.range (P.liftRelations I)) ≤ RingHom.ker (P.reductionAux I) := by
  rw [Ideal.span_le]
  rintro _ ⟨(_ | i), rfl⟩
  · simp only [liftRelations, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one,
      reductionAux_rename_some, ← jacobian_eq_aeval_map_liftJacobian]
    simp [reductionAux, reductionVal]
  · simp [liftRelations, reductionAux_rename_some, map_liftRelation,
      Presentation.aeval_val_relation]

/-- The reduction map `Bˡⁱᶠᵗ → B̄`, `xᵢ ↦ xᵢ`, `t ↦ Δ̄⁻¹`. -/
noncomputable def reduction : P.Lift I →+* B :=
  Ideal.Quotient.lift _ (P.reductionAux I) fun _ h ↦ P.span_le_ker_reductionAux I h

@[simp]
lemma reduction_mk (p : MvPolynomial (Option ι) A) :
    P.reduction I (Ideal.Quotient.mk _ p) = P.reductionAux I p :=
  rfl

lemma reduction_algebraMap (a : A) :
    P.reduction I (algebraMap A (P.Lift I) a) = algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a) := by
  change P.reductionAux I (C a) = _
  simp [reductionAux]

lemma surjective_reduction : Function.Surjective (P.reduction I) := by
  intro b
  obtain ⟨p, rfl⟩ := P.aeval_val_surjective b
  obtain ⟨q, rfl⟩ := map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  exact ⟨Ideal.Quotient.mk _ (rename some q), by rw [reduction_mk, reductionAux_rename_some]⟩

/-- The ideal `I Bˡⁱᶠᵗ` of the lift. -/
local notation "J" => I.map (algebraMap A (P.Lift I))

/-- The inverse of the reduction on polynomials: `(A ⧸ I)[xᵢ] → Bˡⁱᶠᵗ ⧸ I Bˡⁱᶠᵗ`. -/
noncomputable def inverseAux : MvPolynomial ι (A ⧸ I) →+* P.Lift I ⧸ J :=
  eval₂Hom (Ideal.quotientMap _ (algebraMap A (P.Lift I)) Ideal.le_comap_map)
    fun i ↦ Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (X (some i)))

lemma inverseAux_comp_map :
    (P.inverseAux I).comp (map (Ideal.Quotient.mk I)) =
      (Ideal.Quotient.mk J).comp ((Ideal.Quotient.mk _).comp (rename some).toRingHom) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.comp_apply, map_C, inverseAux, coe_eval₂Hom, eval₂_C]
    rw [Ideal.quotientMap_mk]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
    rfl
  · simp [inverseAux]

lemma ker_le_ker_inverseAux : P.ker ≤ RingHom.ker (P.inverseAux I) := by
  rw [← P.span_range_relation_eq_ker, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, ← map_liftRelation,
    ← RingHom.comp_apply, inverseAux_comp_map]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range (P.liftRelations I)))
      (rename some (P.liftRelation I i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨some i, rfl⟩)
  rw [hz, map_zero]

/-- The inverse of the reduction, `B̄ → Bˡⁱᶠᵗ ⧸ I Bˡⁱᶠᵗ`. -/
noncomputable def inverse : B →+* P.Lift I ⧸ J :=
  (Ideal.Quotient.lift _ (P.inverseAux I) fun _ h ↦ P.ker_le_ker_inverseAux I h).comp
    P.quotientEquiv.symm.toRingHom

lemma inverse_algebraMap (p : MvPolynomial ι (A ⧸ I)) :
    P.inverse I (algebraMap P.Ring B p) = P.inverseAux I p := by
  have : P.quotientEquiv.symm (algebraMap P.Ring B p) = Ideal.Quotient.mk _ p := by
    rw [AlgEquiv.symm_apply_eq, Presentation.quotientEquiv_mk]
  change Ideal.Quotient.lift P.ker (P.inverseAux I) (fun _ h ↦ P.ker_le_ker_inverseAux I h)
    (P.quotientEquiv.symm (algebraMap P.Ring B p)) = _
  rw [this, Ideal.Quotient.lift_mk]

lemma inverse_comp_reduction :
    (P.inverse I).comp (P.reduction I) = Ideal.Quotient.mk J := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun o ↦ ?_))
  · have h := congr($(P.inverseAux_comp_map I) (C a))
    simp only [RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      rename_C] at h
    simp only [RingHom.comp_apply, reduction_mk, reductionAux, coe_eval₂Hom, eval₂_C]
    rw [IsScalarTower.algebraMap_apply (A ⧸ I) P.Ring B, inverse_algebraMap,
      MvPolynomial.algebraMap_eq, h]
  · rcases o with (_ | i)
    · simp only [RingHom.comp_apply, reduction_mk, reductionAux, coe_eval₂Hom, eval₂_X,
        reductionVal]
      have hΔ : P.inverse I P.jacobian =
          Ideal.Quotient.mk J (Ideal.Quotient.mk _ (rename some (P.liftJacobian I))) := by
        rw [jacobian_eq_aeval_map_liftJacobian, ← Generators.algebraMap_apply,
          inverse_algebraMap, ← RingHom.comp_apply, inverseAux_comp_map]
        rfl
      have h₁ : P.inverse I ↑P.jacobian_isUnit.unit⁻¹ * P.inverse I P.jacobian = 1 := by
        rw [← map_mul, IsUnit.val_inv_mul, map_one]
      have h₂ : Ideal.Quotient.mk J (Ideal.Quotient.mk _ (X none)) *
          Ideal.Quotient.mk J (Ideal.Quotient.mk _ (rename some (P.liftJacobian I))) = 1 := by
        have hz : Ideal.Quotient.mk (Ideal.span (Set.range (P.liftRelations I)))
            (X none * rename some (P.liftJacobian I) - 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨none, rfl⟩)
        rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk J),
          ← map_one (Ideal.Quotient.mk (Ideal.span (Set.range (P.liftRelations I)))),
          ← map_sub, ← map_sub, hz, map_zero]
      rw [hΔ] at h₁
      exact left_inv_eq_right_inv h₁ ((mul_comm _ _).trans h₂)
    · simp only [RingHom.comp_apply, reduction_mk, reductionAux, coe_eval₂Hom, eval₂_X,
        reductionVal]
      have : P.val i = algebraMap P.Ring B (X i) := by simp [Generators.algebraMap_apply]
      rw [this, inverse_algebraMap]
      simp [inverseAux]

lemma ker_reduction : RingHom.ker (P.reduction I) = J := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · have h := congr($(P.inverse_comp_reduction I) x)
    simp only [RingHom.comp_apply, (RingHom.mem_ker).1 hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [reduction_algebraMap, Ideal.Quotient.eq_zero_iff_mem.2 ha]

/-- **The lift reduces to `B̄`.** The reduction map `Bˡⁱᶠᵗ → B̄`, `xᵢ ↦ xᵢ`, `t ↦ Δ̄⁻¹`, induces
an isomorphism `Bˡⁱᶠᵗ ⧸ I Bˡⁱᶠᵗ ≃ B̄`. -/
noncomputable def reductionEquiv : P.Lift I ⧸ J ≃+* B :=
  (Ideal.quotEquivOfEq (P.ker_reduction I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (P.surjective_reduction I))

@[simp]
lemma reductionEquiv_mk (x : P.Lift I) :
    P.reductionEquiv I (Ideal.Quotient.mk _ x) = P.reduction I x :=
  rfl

/-- **Étale algebras lift across a quotient.** The lift `Bˡⁱᶠᵗ = A[xᵢ, t] ⧸ (fᵢ, tΔ - 1)` of a
square Jacobian presentation of `B̄` over `A ⧸ I` is étale over `A`, and its reduction
`Bˡⁱᶠᵗ → B̄` is surjective with kernel `I Bˡⁱᶠᵗ`, i.e. induces `Bˡⁱᶠᵗ ⧸ I Bˡⁱᶠᵗ ≃ B̄`
(`Algebra.SquareJacobianPresentation.reductionEquiv`). No nilpotence assumption on `I` is
needed. Every étale `A ⧸ I`-algebra has a square Jacobian presentation, hence such a lift
(`Algebra.Etale.exists_etale_quotientEquiv`).
(blueprint: `proposition-extension-zero-restriction-closed-subscheme`) -/
@[stacks 04D1]
theorem etale_lift_and_ker_reduction_and_surjective :
    Etale A (P.Lift I) ∧ RingHom.ker (P.reduction I) = I.map (algebraMap A (P.Lift I)) ∧
      Function.Surjective (P.reduction I) :=
  ⟨inferInstance, P.ker_reduction I, P.surjective_reduction I⟩

end Algebra.SquareJacobianPresentation

/-- **Every étale algebra over a quotient lifts.** For an ideal `I` of `A` and an étale
`A ⧸ I`-algebra `B`, there is an étale `A`-algebra `C` with `C ⧸ I C ≃ B` compatibly with the
maps from `A`. The algebra `C` is the lift of a square Jacobian presentation of `B`
(`Algebra.SquareJacobianPresentation.Lift`). -/
@[stacks 04D1]
theorem Algebra.Etale.exists_etale_quotientEquiv {A : Type u} [CommRing A] (I : Ideal A)
    (B : Type v) [CommRing B] [Algebra (A ⧸ I) B] [Etale (A ⧸ I) B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Etale A C ∧
      ∃ e : C ⧸ I.map (algebraMap A C) ≃+* B,
        ∀ a : A, e (algebraMap A _ a) = algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a) := by
  classical
  obtain ⟨ι, _, ⟨P⟩⟩ := Etale.iff_exists_squareJacobianPresentation.1 ‹Etale (A ⧸ I) B›
  have := Fintype.ofFinite ι
  exact ⟨P.Lift I, inferInstance, inferInstance, inferInstance, P.reductionEquiv I,
    fun a ↦ P.reduction_algebraMap I a⟩
