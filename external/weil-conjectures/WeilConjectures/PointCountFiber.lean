/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import WeilConjectures.PointCount

/-!
# Rational points over a given point

A `K`-rational point `p : Spec K ⟶ X` of a `k`-scheme `X` lying over a point `x` is determined by
the `k`-embedding `κ(x) ↪ K` it induces. Hence there are at most `[κ(x) : k]` of them.

## Main results

- `AlgebraicGeometry.Scheme.Hom.card_fieldPoints_base_eq_le`: at most `deg x` rational points lie
  over a point `x` with finite residue field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The rational points lying over a point `x` with finite residue field are at most
`[κ(x) : k]` many: the point is recovered from the `k`-embedding `κ(x) ↪ K` it induces. -/
theorem Hom.card_fieldPoints_base_eq_le (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] [Finite K] {x : X} (hx : x ∈ X.finitePoints) :
    Nat.card {p : f.fieldPoints K // p.1.base (IsLocalRing.closedPoint K) = x} ≤
      f.degreeOver x := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Finite (X.residueField x) := hx
  have : FiniteDimensional k (X.residueField x) := Module.Finite.of_finite
  -- the residue map of a rational point over `x`
  let φ : {p : f.fieldPoints K // p.1.base (IsLocalRing.closedPoint K) = x} →
      (X.residueField x ⟶ .of K) := fun p ↦
    (X.residueFieldCongr p.2).inv ≫ (SpecToEquivOfField K X p.1.1).2
  have hφ : ∀ p, (SpecToEquivOfField K X).symm ⟨x, φ p⟩ = p.1.1 := fun p ↦ by
    rw [← (SpecToEquivOfField K X).symm_apply_apply p.1.1]
    congr 1
    rw [SpecToEquivOfField_eq_iff]
    exact ⟨p.2.symm, by simp [φ]⟩
  -- it is a `k`-embedding
  let ψ : {p : f.fieldPoints K // p.1.base (IsLocalRing.closedPoint K) = x} →
      (X.residueField x →ₐ[k] K) := fun p ↦
    { toRingHom := (φ p).hom
      commutes' := fun c ↦ by
        have h := p.1.2
        rw [← hφ p] at h
        change (Spec.map (φ p) ≫ X.fromSpecResidueField x) ≫ f = _ at h
        rw [Category.assoc, ← f.specMap_residueFieldAlgebraMap x, ← Spec.map_comp,
          Spec.map_inj] at h
        exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) c }
  have hinj : Function.Injective ψ := fun p p' h ↦ by
    have h' : φ p = φ p' := CommRingCat.hom_ext (congrArg AlgHom.toRingHom h)
    have := (hφ p).symm.trans ((congrArg (fun g ↦ (SpecToEquivOfField K X).symm ⟨x, g⟩) h').trans
      (hφ p'))
    exact Subtype.ext (Subtype.ext this)
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_algHom_le_finrank k _ K)

end AlgebraicGeometry.Scheme
