/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Extension.ExtendScalars
import WeilConjectures.RingTheory.JacobiZariskiHomologySequence
import WeilConjectures.RingTheory.JacobiZariskiLeftTermVanishing

/-! # Jacobi–Zariski sequence for a quotient of a smooth algebra

Source: Stacks Project, Algebra, Lemma Tags 00S2, 07BP and 00RU
(blueprint: lem-weil-pbc-jacobi-zariski-quotient-smooth).
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/--
Source: Stacks Project, Algebra, Lemma Tag 00S2, with Tags 07BP and 00RU
(blueprint: lem-weil-pbc-jacobi-zariski-quotient-smooth).
Proof:
1. Apply lem-weil-pbc-jacobi-zariski-homology-sequence to A → B → C (Tag 00S2).
2. Use lem-weil-pbc-jacobi-zariski-surjection-h1 and
   lem-weil-pbc-jacobi-zariski-surjection-differentials (Tag 07BP) to identify
   the relative first homology with a.Cotangent and the relative differentials with zero.
3. Apply theorem-finite-etale-covers-proper-henselian--2: projectivity kills
   the two Tor groups, and the first homology vanishing kills the left endpoint.
4. Use lem-weil-pbc-jacobi-zariski-differential-maps (Tag 00RU) for the two
   displayed formulas. Truncate the sequence at its zero endpoints.
-/
theorem jacobiZariski_quotient_smooth
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton (H1Cotangent A B)] [Module.Projective B (KaehlerDifferential A B)]
    (a : Ideal B) :
    let C := B ⧸ a
    ∃ (i : H1Cotangent A C →ₗ[C] a.Cotangent)
      (δ : a.Cotangent →ₗ[C] C ⊗[B] KaehlerDifferential A B)
      (w : C ⊗[B] KaehlerDifferential A B →ₗ[C] KaehlerDifferential A C),
      Function.Injective i ∧ Function.Exact i δ ∧ Function.Exact δ w ∧
      Function.Surjective w ∧
      (∀ x : a, δ (a.toCotangent x) = 1 ⊗ₜ[B] KaehlerDifferential.D A B x) ∧
      (∀ (c : C) (b : B), w (c ⊗ₜ[B] KaehlerDifferential.D A B b) =
        c • KaehlerDifferential.D A C (Ideal.Quotient.mk a b)) := by
  classical
  dsimp only
  let C := B ⧸ a
  let P := Extension.ofSurjective (IsScalarTower.toAlgHom A B C)
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk a))
  have hp : P.ker = a := Ideal.mk_ker
  let q : P.Cotangent ≃ₗ[B] a.Cotangent := by
    let q₀ := P.cotangentEquivCotangentKer
    let q₁ := Ideal.Cotangent.equivOfEq P.ker a hp
    have q₂ := q₀.trans q₁
    exact q₂
  let qC : P.Cotangent ≃ₗ[C] a.Cotangent :=
    q.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective)
  let e : H1Cotangent B C ≃ₗ[C] a.Cotangent :=
    P.h1CotangentEquivCotangent.trans qC
  let d : a.Cotangent →ₗ[C] C ⊗[B] KaehlerDifferential A B :=
    P.cotangentComplex.comp qC.symm.toLinearMap
  let i := e.toLinearMap.comp (H1Cotangent.map A B C C)
  obtain ⟨u, _, _, _, _, huv, hvδ, hδw, _⟩ :=
    jacobiZariski_homology_sequence A B C
  let f := (Generators.self A B).toExtension.cotangentComplex
  have hk : Subsingleton (f.baseChange C).ker := by
    let := (jacobiZariski_leftTerm_vanishing A B a).2.2.2.2
    have hzero (x : (f.baseChange C).ker) : x = 0 := by
      let τ := _root_.TensorProduct.comm B C (Generators.self A B).toExtension.Cotangent
      have hx : τ x.val ∈ (f.rTensor C).ker := by
        dsimp only [τ]
        rw [LinearMap.mem_ker, LinearMap.rTensor_comm,
          ← LinearMap.baseChange_eq_lTensor]
        rw [x.prop, map_zero]
      have hz := congrArg Subtype.val
        (Subsingleton.elim (⟨_, hx⟩ : (f.rTensor C).ker) 0)
      apply Subtype.ext
      exact τ.injective (by simpa using hz)
    exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  have hi : Function.Injective (H1Cotangent.map A B C C) := by
    let := hk
    apply (LinearMap.injective_iff_eq_zero_of_exact huv).2
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hd : d.comp e.toLinearMap = H1Cotangent.δ A B C := by
    ext x
    change P.cotangentComplex (qC.symm (qC (P.h1CotangentEquivCotangent x))) = _
    rw [qC.symm_apply_apply]
    exact DFunLike.congr_fun P.cotangentComplex_comp_h1CotangentEquivCotangent x
  refine ⟨i, d, KaehlerDifferential.mapBaseChange A B C,
    e.injective.comp hi, ?_, ?_, ?_, ?_, ?_⟩
  · have hd' : (H1Cotangent.δ A B C).comp e.symm.toLinearMap = d := by
      ext x
      rw [LinearMap.comp_apply, ← hd, LinearMap.comp_apply]
      change d (e (e.symm x)) = d x
      rw [e.apply_symm_apply]
    simpa only [i, hd'] using
      (LinearEquiv.conj_exact_iff_exact _ _ e).2 hvδ
  · rw [← hd] at hδw
    exact e.surjective.comp_exact_iff_exact.mp hδw
  · exact KaehlerDifferential.mapBaseChange_surjective A B C Ideal.Quotient.mk_surjective
  · intro x
    let y : P.ker := ⟨x.val, by rw [hp]; exact x.prop⟩
    have hq : qC (Extension.Cotangent.mk y) = a.toCotangent x := by
      rfl
    rw [← hq]
    change P.cotangentComplex (qC.symm (qC (Extension.Cotangent.mk y))) = _
    rw [qC.symm_apply_apply]
    exact P.cotangentComplex_mk y
  · intro c b
    rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    rfl

end Algebra
