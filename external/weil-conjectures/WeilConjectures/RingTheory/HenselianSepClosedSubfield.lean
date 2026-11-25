/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Separably closed subfields of strictly henselian local rings

Let `R` be a henselian local ring with separably closed residue field and `φ : F →+* R` a ring
homomorphism from a field. Then `φ` factors through a separably closed field `L ⊆ R`: take a
maximal subring of `R` which is a field and contains the image of `φ` (Zorn's lemma). A monic
irreducible separable polynomial over `L` has a simple root in the separably closed residue field,
which lifts to a root `r ∈ R` by Hensel's lemma; `L[r] ≅ L[X]/(p)` is again a field, so `r ∈ L`
by maximality.
-/

@[expose] public section

universe u v

open Polynomial

/-- The range of a ring homomorphism from a field to a nontrivial ring is a field. -/
lemma RingHom.isField_range {F R : Type*} [Field F] [CommRing R] [Nontrivial R] (φ : F →+* R) :
    IsField φ.range :=
  (RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun _ _ h ↦ φ.injective (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).symm
    |>.toMulEquiv.isField (Field.toIsField F)

/-- A subring which is maximal among the subrings that are fields and contain a given subring
`T₀` is separably closed, if `R` is henselian local with separably closed residue field. -/
lemma HenselianLocalRing.isSepClosed_of_maximal {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {T₀ M : Subring R}
    (hM : Maximal (fun T : Subring R ↦ T₀ ≤ T ∧ IsField T) M) :
    letI := hM.prop.2.toField
    IsSepClosed M := by
  let := hM.prop.2.toField
  refine IsSepClosed.of_exists_root _ fun p hpm hpi hps ↦ ?_
  let P : R[X] := p.map M.subtype
  have hPm : P.Monic := hpm.map _
  let ι : M →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp M.subtype
  obtain ⟨b, hb⟩ := IsSepClosed.exists_root (k := IsLocalRing.ResidueField R) (p.map ι)
    (by rw [hpm.degree_map]; exact (degree_pos_of_irreducible hpi).ne') (hps.map)
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have h₁ : P.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval₂_hom, Polynomial.eval₂_map]
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hb
  have h₂ : IsUnit (P.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← Polynomial.eval₂_hom, Polynomial.derivative_map,
      Polynomial.eval₂_map]
    exact hps.eval₂_derivative_ne_zero ι (by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hb)
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian P hPm a₀ h₁ h₂
  let : Algebra M R := M.subtype.toAlgebra
  have : Fact (Irreducible p) := ⟨hpi⟩
  have hr' : aeval r p = 0 := by
    rw [aeval_def]
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hr
    exact hr
  let g : AdjoinRoot p →ₐ[M] R := AdjoinRoot.liftAlgHom p (Algebra.ofId M R) r hr'
  let A : Subring R := g.toRingHom.range
  have hA : IsField A := g.toRingHom.isField_range
  have hMA : M ≤ A := by
    intro m hm
    exact ⟨AdjoinRoot.of p ⟨m, hm⟩, by simp [g]; rfl⟩
  have hAM : A ≤ M := hM.2 ⟨hM.prop.1.trans hMA, hA⟩ hMA
  have hrA : r ∈ A := ⟨AdjoinRoot.root p, by simp [g]⟩
  refine ⟨⟨r, hAM hrA⟩, M.subtype_injective ?_⟩
  rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  exact hr

/-- **A strictly henselian local ring contains a separably closed field over any given field.**
If `R` is a henselian local ring with separably closed residue field and `φ : F →+* R` is a ring
homomorphism from a field, then `φ` factors as `F →+* L →+* R` with `L` a separably closed
field. -/
theorem HenselianLocalRing.exists_isSepClosed_factor {F : Type v} {R : Type u} [Field F]
    [CommRing R] [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (φ : F →+* R) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L) (ψ : L →+* R) (ρ : F →+* L),
      ψ.comp ρ = φ := by
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {T : Subring R | φ.range ≤ T ∧ IsField T}
    (fun c hcs hc y hy ↦ by
      have hne : c.Nonempty := ⟨y, hy⟩
      have hd : DirectedOn (· ≤ ·) c := hc.directedOn
      refine ⟨sSup c, ⟨(hcs hy).1.trans (le_sSup hy), ?_⟩, fun z hz ↦ le_sSup hz⟩
      refine ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg Subtype.val h)⟩,
        fun a b ↦ Subtype.ext (mul_comm (a : R) b), fun {a} ha ↦ ?_⟩
      obtain ⟨T, hT, haT⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 a.2
      obtain ⟨b, hb⟩ := (hcs hT).2.mul_inv_cancel
        (a := ⟨a, haT⟩) (fun h ↦ ha (Subtype.ext (by simpa using congrArg Subtype.val h)))
      exact ⟨⟨b, le_sSup hT b.2⟩, Subtype.ext (by simpa using congrArg Subtype.val hb)⟩)
    φ.range ⟨le_rfl, φ.isField_range⟩
  exact ⟨M, hM.prop.2.toField, HenselianLocalRing.isSepClosed_of_maximal hM, M.subtype,
    φ.codRestrict M fun x ↦ hM.prop.1 ⟨x, rfl⟩, rfl⟩
