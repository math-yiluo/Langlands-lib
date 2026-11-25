/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Basic

/-!
# Essential finite presentation over an intermediate algebra

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph; Definition 00QM and
Lemma 00F4 (4) (blueprint: lemma-quasi-finite-coordinates--1).
-/

@[expose] public section

universe u v w p

namespace RingHom

/-- The finite equations identifying essential generators with their fractions and adjoining
inverses of their denominators. Source: the localized construction in the proof of Tag 00F4 (4)
(blueprint: lemma-quasi-finite-coordinates--1). -/
private noncomputable def finiteCompatibilityIdeal
    {R : Type u} {S : Type v} {P : Type p}
    [CommRing R] [CommRing S] [CommRing P] [Algebra R S] [Algebra R P]
    (U : Submonoid P) (s : Finset S) (a : s → P) (d : s → U) :
    Ideal (MvPolynomial s (TensorProduct R S P)) :=
  Ideal.span
    (Set.range (fun i : s ↦
      MvPolynomial.C (Algebra.TensorProduct.includeRight (d i : P)) * MvPolynomial.X i - 1) ∪
     Set.range (fun i : s ↦
      MvPolynomial.C (algebraMap S (TensorProduct R S P) (i : S)) -
        MvPolynomial.C (Algebra.TensorProduct.includeRight (a i)) * MvPolynomial.X i))

/-- The quotient by the finite compatibility equations. This is a concrete construction,
independent of any existence theorem. Source: the localized proof of Tag 00F4 (4)
(blueprint: lemma-quasi-finite-coordinates--1). -/
private abbrev FiniteCompatibilityQuotient
    {R : Type u} {S : Type v} {P : Type p}
    [CommRing R] [CommRing S] [CommRing P] [Algebra R S] [Algebra R P]
    (U : Submonoid P) (s : Finset S) (a : s → P) (d : s → U) :=
  MvPolynomial s (TensorProduct R S P) ⧸ finiteCompatibilityIdeal (R := R) U s a d

/-- The finite compatibility quotient recovers a localization of `P` after localizing further.
No finite-presentation assumption on `P` is needed here.

Source: Stacks Project, Algebra, the generator equations in the proof of Tag 00F4 (4),
and Proposition Tag 00CP (localization universal property); this is steps 3 and 4 of the
localized argument used in Tag 00R7
(blueprint: lemma-quasi-finite-coordinates--1).

Proof: Evaluate the tensor coefficients in `T` via `ψ` and `f`, and send each polynomial
variable to the inverse of `f (d i)`. The compatibility assumption annihilates the second
family of equations, and the inverse equation annihilates the first. Thus evaluation factors
through the displayed quotient `Q`. Let `j : P → Q` be the inclusion through the tensor,
polynomial, and quotient maps, and set `V = U.map j`. Evaluation sends `V` to units, hence
extends to `Localization V`. Conversely, `P → Localization V` inverts `U`, so the universal
property gives a map `T → Localization V`. Their composite on `T` fixes `P` and is the
identity by localization uniqueness. Their composite on `Localization V` fixes `P` and each
variable, since that variable is the inverse of its denominator in `Q`. The compatibility
equation then shows that it fixes every member of `s`. Essential generation of `S` says
that `S` is the localization of `R[s]` at elements mapping to units; agreement on `R` and
`s` therefore gives agreement on all of `S`, including its denominators. The composite
fixes both tensor factors, all polynomial variables, the quotient, and finally the inverted
elements of `V`. The two maps are inverse. Transport the canonical localization structure
along this equivalence; its structure map is exactly the quotient evaluation map.
-/
private theorem finiteCompatibilityQuotient_isLocalization
    {R : Type u} {S : Type v} {P : Type p}
    [CommRing R] [CommRing S] [CommRing P] [Algebra R S] [Algebra R P]
    {T : Type w} [CommRing T]
    (ψ : S →+* T) (U : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap R P) = ψ.comp (algebraMap R S))
    (hT : letI := f.toAlgebra; IsLocalization U T)
    (s : Finset S)
    (hs : IsLocalization
      ((IsUnit.submonoid S).comap (algebraMap (Algebra.adjoin R (s : Set S)) S)) S)
    (a : s → P) (d : s → U)
    (hd : ∀ i : s, ψ (i : S) * f (d i : P) = f (a i)) :
    ∃ (V : Submonoid (FiniteCompatibilityQuotient (R := R) U s a d))
      (g : FiniteCompatibilityQuotient (R := R) U s a d →+* T),
      g.comp (algebraMap S _) = ψ ∧ (letI := g.toAlgebra; IsLocalization V T) := by
  classical
  let : Algebra P T := f.toAlgebra
  have : IsLocalization U T := hT
  let : Algebra S T := ψ.toAlgebra
  let : Algebra R T := (ψ.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let fA : P →ₐ[R] T := ⟨f, fun r ↦ RingHom.congr_fun hf r⟩
  let c : TensorProduct R S P →ₐ[S] T := AlgHom.liftEquiv R S P T fA
  let x : s → T := fun i ↦ IsLocalization.mk' T 1 (d i)
  have hcP (z : P) : c (Algebra.TensorProduct.includeRight z) = f z := by
    change c (TensorProduct.tmul R 1 z) = f z
    simp [c, AlgHom.liftEquiv_tmul, fA]
  have hcS (z : S) : c (algebraMap S (TensorProduct R S P) z) = ψ z := c.commutes z
  let e := MvPolynomial.eval₂Hom c.toRingHom x
  let I := finiteCompatibilityIdeal (R := R) U s a d
  have he : I ≤ RingHom.ker e := by
    apply Ideal.span_le.mpr
    rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change e _ = 0
      simp only [e, map_sub, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', map_one, sub_eq_zero,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hcP]
      change f (d i : P) * IsLocalization.mk' T 1 (d i) = 1
      have hspec := IsLocalization.mk'_spec T 1 (d i)
      change IsLocalization.mk' T 1 (d i) * f (d i : P) = f 1 at hspec
      rw [map_one] at hspec
      exact (mul_comm _ _).trans hspec
    · change e _ = 0
      simp only [e, map_sub, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', sub_eq_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hcS, hcP]
      change ψ (i : S) = f (a i) * IsLocalization.mk' T 1 (d i)
      rw [← hd i, mul_assoc]
      have hunit : f (d i : P) * IsLocalization.mk' T 1 (d i) = 1 := by
        have hspec := IsLocalization.mk'_spec T 1 (d i)
        change IsLocalization.mk' T 1 (d i) * f (d i : P) = f 1 at hspec
        rw [map_one] at hspec
        exact (mul_comm _ _).trans hspec
      rw [hunit, mul_one]
  let Q := FiniteCompatibilityQuotient (R := R) U s a d
  let q : MvPolynomial s (TensorProduct R S P) →+* Q := Ideal.Quotient.mk I
  let g : Q →+* T := Ideal.Quotient.lift I e (fun z hz ↦ he hz)
  let j : P →+* Q := q.comp
    (MvPolynomial.C.comp Algebra.TensorProduct.includeRight.toRingHom)
  let V := U.map j
  let L := Localization V
  let l := algebraMap Q L
  have hgP (z : P) : g (j z) = f z := by
    change e (MvPolynomial.C (Algebra.TensorProduct.includeRight z)) = f z
    simpa only [e, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using hcP z
  have hgS (z : S) : g (algebraMap S Q z) = ψ z := by
    change e (MvPolynomial.C (algebraMap S (TensorProduct R S P) z)) = ψ z
    simpa only [e, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using hcS z
  have hjU (z : U) : IsUnit ((l.comp j) z) :=
    IsLocalization.map_units L (⟨j z, ⟨z, z.property, rfl⟩⟩ : V)
  let η : T →+* L := IsLocalization.lift hjU
  have hηP (z : P) : η (f z) = l (j z) := IsLocalization.lift_eq hjU z
  have hgU (z : V) : IsUnit (g z) := by
    obtain ⟨z, hz, heq⟩ := z.property
    rw [← heq, hgP]
    exact IsLocalization.map_units T ⟨z, hz⟩
  let γ : L →+* T := IsLocalization.lift hgU
  have hγη : γ.comp η = RingHom.id T := by
    apply IsLocalization.ringHom_ext U
    ext z
    change γ (η (f z)) = f z
    rw [hηP]
    rw [show γ (l (j z)) = g (j z) from IsLocalization.lift_eq hgU (j z), hgP]
  have hinv (i : s) : j (d i : P) * q (MvPolynomial.X i) = 1 := by
    apply sub_eq_zero.mp
    change q (MvPolynomial.C (Algebra.TensorProduct.includeRight (d i : P))) *
      q (MvPolynomial.X i) - 1 = 0
    rw [← map_mul, ← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
  have hcompat (i : s) : algebraMap S Q (i : S) = j (a i) * q (MvPolynomial.X i) := by
    apply sub_eq_zero.mp
    change q (MvPolynomial.C (algebraMap S (TensorProduct R S P) (i : S))) -
      q (MvPolynomial.C (Algebra.TensorProduct.includeRight (a i))) *
        q (MvPolynomial.X i) = 0
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
  have hηgen (i : s) : η (ψ (i : S)) = l (algebraMap S Q (i : S)) := by
    apply (hjU (d i)).mul_right_cancel
    change η (ψ (i : S)) * l (j (d i : P)) =
      l (algebraMap S Q (i : S)) * l (j (d i : P))
    calc
      _ = η (ψ (i : S) * f (d i : P)) := by rw [map_mul, hηP]
      _ = l (j (a i)) := by rw [hd, hηP]
      _ = _ := by
        rw [hcompat, map_mul, mul_assoc, ← map_mul, mul_comm (q _), hinv,
          map_one, mul_one]
  have hηR (r : R) : η (ψ (algebraMap R S r)) =
      l (algebraMap S Q (algebraMap R S r)) := by
    have hfr : f (algebraMap R P r) = ψ (algebraMap R S r) :=
      RingHom.congr_fun hf r
    rw [← hfr, hηP]
    change l (q (MvPolynomial.C
      (Algebra.TensorProduct.includeRight (algebraMap R P r)))) =
      l (q (MvPolynomial.C (algebraMap S (TensorProduct R S P) (algebraMap R S r))))
    rw [Algebra.TensorProduct.includeRight.commutes,
      IsScalarTower.algebraMap_apply R S (TensorProduct R S P)]
  have hηS : η.comp ψ = l.comp (algebraMap S Q) := by
    let M := (IsUnit.submonoid S).comap (algebraMap (Algebra.adjoin R (s : Set S)) S)
    have : IsLocalization M S := hs
    apply IsLocalization.ringHom_ext M
    ext z
    change η (ψ (z : S)) = l (algebraMap S Q (z : S))
    refine Algebra.adjoin_induction (fun z hz ↦ hηgen ⟨z, hz⟩) hηR ?_ ?_ z.property
    · intro z z' hz hz' he he'
      simp only [map_add, he, he']
    · intro z z' hz hz' he he'
      simp only [map_mul, he, he']
  have hηγQ : η.comp g = l := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · have hcoeff : (η.comp g).comp (q.comp MvPolynomial.C) =
          l.comp (q.comp MvPolynomial.C) := by
        apply Algebra.TensorProduct.ringHom_ext
        · ext z
          change η (g (algebraMap S Q z)) = l (algebraMap S Q z)
          rw [hgS]
          exact RingHom.congr_fun hηS z
        · ext z
          change η (g (j z)) = l (j z)
          rw [hgP, hηP]
      exact fun z ↦ RingHom.congr_fun hcoeff z
    · intro i
      change η (g (q (MvPolynomial.X i))) = l (q (MvPolynomial.X i))
      apply (hjU (d i)).mul_right_cancel
      change η (g (q (MvPolynomial.X i))) * l (j (d i : P)) =
        l (q (MvPolynomial.X i)) * l (j (d i : P))
      calc
        _ = η (g (q (MvPolynomial.X i) * j (d i : P))) := by
          rw [map_mul, map_mul, hgP, hηP]
        _ = 1 := by rw [mul_comm, hinv, map_one, map_one]
        _ = _ := by rw [← map_mul, mul_comm, hinv, map_one]
  have hηγ : η.comp γ = RingHom.id L := by
    apply IsLocalization.ringHom_ext V
    apply RingHom.ext
    intro z
    change η (γ (l z)) = l z
    rw [show γ (l z) = g z from IsLocalization.lift_eq hgU z]
    exact RingHom.congr_fun hηγQ z
  let equiv : L ≃+* T := RingEquiv.ofRingHom γ η hγη hηγ
  refine ⟨V, g, RingHom.ext hgS, ?_⟩
  let : Algebra Q T := g.toAlgebra
  have eqv : L ≃ₐ[Q] T :=
    { equiv with commutes' := fun z ↦ IsLocalization.lift_eq hgU z }
  exact IsLocalization.isLocalization_of_algEquiv V eqv



/-- Essential finite presentation descends to an essentially finite type intermediate algebra.
The input `P`, `U`, and `f` give a localization presentation of `T` over `R`; `hf` says that
its `R`-algebra structure is the one induced by `ψ.comp φ`. The output gives a localization
presentation over `S` with its original structure map `ψ`.

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph, using Definition 00QM
and the localized analogue of Lemma 00F4 (4)
(blueprint: lemma-quasi-finite-coordinates--1).

Proof:
1. Choose `S = W⁻¹B` with `B` a finite type `R`-algebra, and generators `b₁, …, bₙ`
   [def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra].
   The given presentation is `T = U⁻¹P` [def-weil-pbc-finitely-presented-algebra].
   Write the image of each `bᵢ` in `T` as `pᵢ/uᵢ` with `uᵢ ∈ U`.
2. Base change `P` to `A = TensorProduct R S P`, adjoin variables `tᵢ`, and quotient by the finitely
   many relations `uᵢtᵢ = 1` and `bᵢ ⊗ 1 = (1 ⊗ pᵢ)tᵢ`, obtaining `Q`.
   Base change and composition preserve finite presentation
   [lem-weil-pbc-finite-presentation-base-change-composition]; adjoining finitely many
   variables does too [def-weil-pbc-finitely-presented-algebra], as does quotienting by
   a finitely generated ideal [lem-weil-pbc-finite-presentation-quotient-fg-ideal].
   Thus `Q` is a finitely presented `S`-algebra.
3. Map `Q` to `T` by the given maps on `S` and `P`, and `tᵢ ↦ 1/uᵢ`. The relations
   hold. The image `V` of `U` in `Q` maps to units, giving `V⁻¹Q → T`
   [lem-weil-pbc-ring-localization-universal-property].
4. Conversely `P → V⁻¹Q` inverts `U`, giving `T → V⁻¹Q` by the same universal property.
   The composite on `T` fixes `P` and its inverted denominators. The other composite
   fixes `P`, each `tᵢ = uᵢ⁻¹`, and each `bᵢ` by the compatibility relation. It therefore
   fixes `B`, the inverses of `W`, all of `S`, then `A`, `Q`, and the inverses of `V`
   [def-weil-pbc-finite-type-algebra, def-weil-pbc-essentially-finite-type-algebra,
   lem-weil-pbc-ring-localization-universal-property]. These are inverse maps over `S`.
-/
theorem essentially_finite_presentation_over_intermediate
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (hS : φ.EssFiniteType)
    (P : Type p) [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P]
    (U : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap R P) = ψ.comp φ)
    (hT : letI := f.toAlgebra; IsLocalization U T) :
    ∃ (Q : Type (max v p)) (_ : CommRing Q) (_ : Algebra S Q),
      Algebra.FinitePresentation S Q ∧
        ∃ (V : Submonoid Q) (g : Q →+* T),
          g.comp (algebraMap S Q) = ψ ∧ (letI := g.toAlgebra; IsLocalization V T) := by
  classical
  let : Algebra R S := φ.toAlgebra
  have : Algebra.EssFiniteType R S := hS
  let : Algebra P T := f.toAlgebra
  have : IsLocalization U T := hT
  let s := Algebra.EssFiniteType.finset R S
  obtain ⟨a, d, hd⟩ : ∃ (a : s → P) (d : s → U),
      ∀ i : s, ψ (i : S) * f (d i : P) = f (a i) := by
    have h := fun i : s ↦ IsLocalization.surj U (ψ (i : S))
    choose ad had using h
    exact ⟨fun i ↦ (ad i).1, fun i ↦ (ad i).2, had⟩
  let Q := FiniteCompatibilityQuotient (R := R) U s a d
  have hI : (finiteCompatibilityIdeal (R := R) U s a d).FG := by
    apply Submodule.fg_def.mpr
    exact ⟨_, (Set.finite_range _).union (Set.finite_range _), rfl⟩
  have : Algebra.FinitePresentation S (TensorProduct R S P) := inferInstance
  have : Algebra.FinitePresentation S (MvPolynomial s (TensorProduct R S P)) := inferInstance
  have : Algebra.FinitePresentation S Q := Algebra.FinitePresentation.quotient hI
  obtain ⟨V, g, hg, hloc⟩ := finiteCompatibilityQuotient_isLocalization
    ψ U f hf hT s (Algebra.EssFiniteType.isLocalization R S) a d hd
  exact ⟨Q, inferInstance, inferInstance, inferInstance, V, g, hg, hloc⟩

end RingHom
