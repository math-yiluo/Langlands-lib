/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

import Mathlib.Algebra.Polynomial.Lifts

/-! Polynomial lifting step for surjectivity of the pointed étale colimit.
(blueprint: lem-weil-pbc-etale-triples-colimit-polynomial-lift). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every element of `K` admits a monic polynomial over the colimit whose image has
that element as a simple root. Source: the coefficient-lifting and separability step
of Stacks Project, Tags 04GW and 00UH.

Proof: Put `C = c.pt` and let `F` be the image of `ψ` in `K`. If `ψ(x)` is nonzero,
`hunit` represents `x` by a unit of `C`; mapping its inverse gives the inverse of
`ψ(x)`. Thus `F` is a subfield, including inverse closure at zero. The identity
triple `(R, p, algebraMap κ(p) K)` exists because the identity morphism is étale.
Applying `hψ` to this triple shows that `F` contains the canonical image of `R`.
The isomorphism `Spec.residueFieldIso` identifies `κ(p)` with the residue field of
`R_p` and commutes with the canonical maps from `R`. Every residue class lifts to
an element of `R_p`, represented by `r/s` with `s` outside `p`. The class of `s`
is a unit, hence nonzero; its image in `K` is nonzero since field homomorphisms are
injective. Inverse closure therefore puts the image of every such fraction in `F`.
Consequently every element of `κ(p)` has its image in `K` lifted by `ψ`.

For `a₀ : K`, let `g = minpoly κ(p) a₀`. The separable-closure hypothesis gives
algebraicity and separability, so `g` is monic and separable and evaluates to zero
at `a₀`. Choose preimages in `C` of the images of its finitely many coefficients
below `n = g.natDegree`. The polynomial `X^n + ∑ i < n, C(b_i) * X^i` is monic and
maps under `ψ` to `g.map (algebraMap κ(p) K)`. This is also the construction in
`Polynomial.lifts_and_natDegree_eq_and_monic`. Its evaluation at `a₀` is zero.
Separability supplies `U*g + V*g.derivative = 1`; evaluating at `a₀` shows that
`g.derivative` evaluates to a nonzero element. Derivative and evaluation commute
with coefficient mapping, giving the same nonzero value for the lifted polynomial.
This proves both required evaluation conditions without an injective map `R → C`.
(blueprint: lem-weil-pbc-etale-triples-colimit-polynomial-lift) -/
theorem etaleResidueTriples_polynomial_lift
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hunit : ∀ x : c.pt, ψ x ≠ 0 → IsUnit x) :
    ∀ a₀ : K, ∃ f : Polynomial c.pt, f.Monic ∧
      f.eval₂ ψ a₀ = 0 ∧ f.derivative.eval₂ ψ a₀ ≠ 0 := by
  classical
  have _colimit := hc
  let k := (Spec R).residueField p
  let χ : k →+* K := algebraMap k K
  let t : EtaleResidueTriple R p K (CommRingCat.ofHom χ) :=
    { B := R
      α := 𝟙 R
      etale := by rw [Spec.map_id]; infer_instance
      q := p
      over := by simp
      φ := CommRingCat.ofHom χ
      compatible := by simp }
  have hinv {y : K} (hy : y ∈ ψ.range) : y⁻¹ ∈ ψ.range := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, hv⟩ := hunit x hy0
    refine ⟨↑v⁻¹, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← hv, ← map_mul, Units.inv_mul, map_one]
  let η : p.asIdeal.ResidueField →+* K := χ.comp (Spec.residueFieldIso R p).inv.hom
  have hR (r : R) : η (algebraMap R p.asIdeal.ResidueField r) ∈ ψ.range := by
    refine ⟨(c.ι.app t).hom r, ?_⟩
    have ht := DFunLike.congr_fun (hψ t) r
    change ψ ((c.ι.app t).hom r) = _ at ht
    rw [ht]
    change (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫
      CommRingCat.ofHom χ).hom) r = _
    have he := Spec.algebraMap_residueFieldIso_inv R p
    have he' := congrArg (fun f ↦ (f ≫ CommRingCat.ofHom χ).hom r) he
    exact he'.symm
  have hres (b : p.asIdeal.ResidueField) : η b ∈ ψ.range := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (R ⧸ p.asIdeal) b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [map_div₀]
    simpa only [div_eq_mul_inv, Ideal.algebraMap_quotient_residueField_mk] using
      ψ.range.mul_mem (hR a) (hinv (hR b))
  have hcoeff (b : k) : χ b ∈ ψ.range := by
    have h := hres ((Spec.residueFieldIso R p).hom b)
    change χ ((Spec.residueFieldIso R p).inv
      ((Spec.residueFieldIso R p).hom b)) ∈ ψ.range at h
    have he : (Spec.residueFieldIso R p).inv
        ((Spec.residueFieldIso R p).hom b) = b :=
      CommRingCat.inv_hom_apply (Spec.residueFieldIso R p) b
    exact he ▸ h
  intro a₀
  let g := minpoly k a₀
  have hg : g.Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k a₀)
  have hroot : g.eval₂ χ a₀ = 0 := minpoly.aeval k a₀
  have hsep : g.Separable := Algebra.IsSeparable.isSeparable k a₀
  have hlift : g.map χ ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    exact hcoeff (g.coeff i)
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift (hg.map χ)
  refine ⟨f, hfm, ?_, ?_⟩
  · have he := congrArg (Polynomial.eval a₀) hf
    simp only [Polynomial.eval_map] at he
    exact he.trans hroot
  · have he := congrArg (fun q : Polynomial K ↦ q.derivative.eval a₀) hf
    have hd := hsep.eval₂_derivative_ne_zero χ hroot
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at he
    exact he ▸ hd

end AlgebraicGeometry.Scheme
