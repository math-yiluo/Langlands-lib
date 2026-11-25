/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Algebra.Equiv
import WeilConjectures.RingTheory.SmoothAtPrimeFreeConormalBasis
import WeilConjectures.RingTheory.PopescuClearConormalChart
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Prepared polynomial data for Popescu lifting

Source: Stacks Project, Tag 07CP, preparation (1)--(4).
(blueprint: lem-weil-pbc-popescu-lift-preparation).
-/

@[expose] public section

noncomputable section

universe a c

namespace Algebra

/-- Finite polynomial data; no algebra is chosen from an existence theorem. -/
structure PopescuLiftPresentation (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar] where
  n : ℕ
  m : ℕ
  r : ℕ
  f : Fin m → MvPolynomial (Fin n) R
  a : Fin r → MvPolynomial (Fin n) R
  E : Fin r → Finset (Fin m)
  h : Fin r → Fin m → Fin m → MvPolynomial (Fin n) R
  g : Fin r → Fin m → MvPolynomial (Fin n) R
  ε : MvPolynomial (Fin n) (R ⧸ Ideal.span ({π ^ 2} : Set R)) →ₐ[
    R ⧸ Ideal.span ({π ^ 2} : Set R)] Cbar

namespace PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

abbrev reduced (d : PopescuLiftPresentation R Cbar π) (u : MvPolynomial (Fin d.n) R) :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))) u

abbrev reducedIdeal (d : PopescuLiftPresentation R Cbar π) :=
  Ideal.span (Set.range (fun j ↦ d.reduced (d.f j)))

abbrev reducedQuotient (d : PopescuLiftPresentation R Cbar π) :=
  MvPolynomial (Fin d.n) (R ⧸ Ideal.span ({π ^ 2} : Set R)) ⧸ d.reducedIdeal

abbrev reducedElement (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  Ideal.Quotient.mk d.reducedIdeal (d.reduced (d.a k))

/-- The presentation, cover, conormal bases and cleared relations of (1)--(4). -/
structure Prepared [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) : Prop where
  surjective : Function.Surjective d.ε
  kernel : RingHom.ker d.ε.toRingHom = d.reducedIdeal
  cover : ∀ q : PrimeSpectrum Cbar,
    IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R)) q →
    ∃ k : Fin d.r, d.ε (d.reduced (d.a k)) ∉ q.asIdeal
  smooth : ∀ k : Fin d.r,
    Smooth (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (d.reducedElement k))
  card_le : ∀ k : Fin d.r, (d.E k).card ≤ d.n
  conormal : ∀ k : Fin d.r,
    ∃ b : Module.Basis (d.E k) (Localization.Away (d.reducedElement k))
        (LocalizedModule.Away (d.reducedElement k) d.reducedIdeal.Cotangent),
      ∀ j : d.E k, b j =
        LocalizedModule.mkLinearMap (Submonoid.powers (d.reducedElement k))
          d.reducedIdeal.Cotangent
          (d.reducedIdeal.toCotangent ⟨d.reduced (d.f j),
            Ideal.subset_span ⟨j, rfl⟩⟩)
  differentials : ∀ k : Fin d.r,
    Nonempty (Module.Basis (Fin (d.n - (d.E k).card))
      (Localization.Away (d.reducedElement k))
      (KaehlerDifferential (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (Localization.Away (d.reducedElement k))))
  relation : ∀ (k : Fin d.r) (l : Fin d.m),
    d.a k * d.f l = ∑ j ∈ d.E k, d.h k l j * d.f j +
      MvPolynomial.C (π ^ 2) * d.g k l
  normalized_h : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k →
    ∀ j : Fin d.m, d.h k l j = if l = j then d.a k else 0
  normalized_g : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k → d.g k l = 0

abbrev polynomial (d : PopescuLiftPresentation R Cbar π) :=
  MvPolynomial (Fin d.n ⊕ Fin d.m) R

/-- The inclusion of the original polynomial variables. -/
def includeX (d : PopescuLiftPresentation R Cbar π) :
    MvPolynomial (Fin d.n) R →ₐ[R] d.polynomial :=
  MvPolynomial.rename Sum.inl

/-- The equations defining the lifting algebra, with original and auxiliary variables. -/
def equation (d : PopescuLiftPresentation R Cbar π) :
    Fin d.m ⊕ (Fin d.r × Fin d.m) → d.polynomial
  | .inl j => d.includeX (d.f j) - MvPolynomial.C π * MvPolynomial.X (.inr j)
  | .inr (k, l) => d.includeX (d.a k) * MvPolynomial.X (.inr l) -
      (∑ j ∈ d.E k, d.includeX (d.h k l j) * MvPolynomial.X (.inr j)) -
      MvPolynomial.C π * d.includeX (d.g k l)

abbrev definingIdeal (d : PopescuLiftPresentation R Cbar π) :=
  Ideal.span (Set.range d.equation)

/-- Explicit quotient; `ULift` gives the universe required by the original theorem. -/
abbrev liftingAlgebra (d : PopescuLiftPresentation R Cbar π) :=
  ULift.{c} (d.polynomial ⧸ d.definingIdeal)

/-- Original generators in the explicitly constructed lifting algebra. -/
def x (d : PopescuLiftPresentation R Cbar π) (i : Fin d.n) : d.liftingAlgebra :=
  ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inl i)))

/-- The displayed quotient has finitely many variables and finitely many equations. -/
theorem finitePresentation (d : PopescuLiftPresentation R Cbar π) :
    FinitePresentation R d.liftingAlgebra := by
  let : FinitePresentation R (d.polynomial ⧸ d.definingIdeal) :=
    FinitePresentation.quotient (Submodule.fg_span (Set.finite_range d.equation))
  exact FinitePresentation.equiv (ULift.algEquiv (R := R)).symm

end PopescuLiftPresentation

private theorem smoothAtPrime_of_algEquiv
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (e : A ≃ₐ[S] B) (q : PrimeSpectrum B)
    (hs : IsSmoothAtPrime S q) :
    IsSmoothAtPrime S (PrimeSpectrum.comap e.toRingHom q) := by
  obtain ⟨g, hg, hsm⟩ := hs
  refine ⟨e.symm g, ?_, ?_⟩
  · simpa using hg
  · have : Smooth S (Localization.Away g) := hsm
    let el := IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers (e.symm g)) (T := Submonoid.powers g)
      (Localization.Away (e.symm g)) (Localization.Away g) e
      (by simp only [Submonoid.map_powers, e.apply_symm_apply])
    exact Smooth.of_equiv el.symm

/-- Prepare the finite presentation and smooth charts used in the lifting construction.

Source: Stacks Project, Tag 07CP, proof through equations (1)--(4); Tag 07C6.
(blueprint: lem-weil-pbc-popescu-lift-preparation).

Proof: Choose a finite polynomial presentation over R/π² and lift its finitely many
relations to R[x]. Let ε be its surjective presentation map. The quotient Cbar is
Noetherian, since it is finite type over the Noetherian quotient R/π². At each smooth
prime apply Tag 07C6 to select a principal neighbourhood, a subset E of the given
relations forming a conormal basis, and a differential basis of complementary rank.
Select finitely many such neighbourhoods covering the smooth locus using Noetherianity.
For each chart, the selected relations generate I/I² after localization. Nakayama
applied to I/I_E gives an annihilator 1+b/a^N with b in I. Replace a by a(a^N+b);
in Cbar its image is a power of the old image, so the cover and bases persist, while
I and I_E now agree after localization. Clear denominators in the expressions for
all f_l in I_E modulo π², replacing a by a common positive power. Lift the coefficients
and the π² remainders to R[x]. For l in E choose h_{klj}=a_k δ_{lj} and g_{kl}=0.
These choices satisfy the displayed relations exactly and preserve every chart condition.
-/
theorem exists_popescu_lift_preparation (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [FinitePresentation (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar] :
    ∃ d : PopescuLiftPresentation R Cbar π, d.Prepared := by
  classical
  let Rbar := R ⧸ Ideal.span ({π ^ 2} : Set R)
  obtain ⟨n, ε, hε, hfg⟩ := FinitePresentation.out (R := Rbar) (A := Cbar)
  obtain ⟨m, fbar, hfbar⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hlift := MvPolynomial.map_surjective (σ := Fin n)
    (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))) Ideal.Quotient.mk_surjective
  choose f hf using fun j : Fin m ↦ hlift (fbar j)
  have hker : RingHom.ker ε.toRingHom = Ideal.span
      (Set.range (fun j ↦ MvPolynomial.map (Ideal.Quotient.mk
        (Ideal.span ({π ^ 2} : Set R))) (f j))) := by
    simpa only [hf] using hfbar.symm
  let red : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) Rbar :=
    MvPolynomial.map (Ideal.Quotient.mk _)
  let I := Ideal.span (Set.range (fun j ↦ red (f j)))
  let e : (MvPolynomial (Fin n) Rbar ⧸ I) ≃ₐ[Rbar] Cbar :=
    (Ideal.quotientEquivAlgOfEq Rbar hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hε)
  have he (p : MvPolynomial (Fin n) Rbar) :
      e (Ideal.Quotient.mk I p) = ε p := by
    dsimp only [e, AlgEquiv.trans_apply]
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hε p
  let Q := {q : PrimeSpectrum Cbar // IsSmoothAtPrime Rbar q}
  have hchart (q : Q) := exists_smoothAtPrime_free_conormal_basis Rbar n m
    (fun j ↦ red (f j)) (PrimeSpectrum.comap e.toRingHom q.1)
    (smoothAtPrime_of_algEquiv e q.1 q.2)
  have hlocal (q : Q) : ∃ (a : MvPolynomial (Fin n) R) (E : Finset (Fin m)),
      ε (red a) ∉ q.1.asIdeal ∧ E.card ≤ n ∧
      Smooth Rbar (Localization.Away (Ideal.Quotient.mk I (red a))) ∧
      (∃ b : Module.Basis E (Localization.Away (Ideal.Quotient.mk I (red a)))
          (LocalizedModule.Away (Ideal.Quotient.mk I (red a)) I.Cotangent),
        ∀ j : E, b j = LocalizedModule.mkLinearMap
          (Submonoid.powers (Ideal.Quotient.mk I (red a))) I.Cotangent
          (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩)) ∧
      Nonempty (Module.Basis (Fin (n - E.card))
        (Localization.Away (Ideal.Quotient.mk I (red a)))
        (KaehlerDifferential Rbar (Localization.Away (Ideal.Quotient.mk I (red a))))) := by
    obtain ⟨abar, ha, E, c, hc, hcn, hsm, ⟨ei, b, hb⟩, hd⟩ := hchart q
    obtain ⟨a, rfl⟩ := hlift abar
    refine ⟨a, E, ?_, hc ▸ (hcn.trans (min_le_left _ _)), hsm, ?_, ?_⟩
    · change e (Ideal.Quotient.mk I (red a)) ∉ q.1.asIdeal at ha
      rwa [he] at ha
    · refine ⟨b.reindex ei, ?_⟩
      intro j
      rw [Module.Basis.reindex_apply]
      simpa only [ei.apply_symm_apply] using hb (ei.symm j)
    · simpa only [hc] using hd
  have hcleared (q : Q) : ∃ (a : MvPolynomial (Fin n) R) (E : Finset (Fin m))
      (h : Fin m → Fin m → MvPolynomial (Fin n) R)
      (g : Fin m → MvPolynomial (Fin n) R),
      ε (red a) ∉ q.1.asIdeal ∧ E.card ≤ n ∧
      Smooth Rbar (Localization.Away (Ideal.Quotient.mk I (red a))) ∧
      (∃ b : Module.Basis E (Localization.Away (Ideal.Quotient.mk I (red a)))
          (LocalizedModule.Away (Ideal.Quotient.mk I (red a)) I.Cotangent),
        ∀ j : E, b j = LocalizedModule.mkLinearMap
          (Submonoid.powers (Ideal.Quotient.mk I (red a))) I.Cotangent
          (I.toCotangent ⟨red (f j), Ideal.subset_span ⟨j, rfl⟩⟩)) ∧
      Nonempty (Module.Basis (Fin (n - E.card))
        (Localization.Away (Ideal.Quotient.mk I (red a)))
        (KaehlerDifferential Rbar (Localization.Away (Ideal.Quotient.mk I (red a))))) ∧
      ∀ l : Fin m, a * f l = ∑ j ∈ E, h l j * f j + MvPolynomial.C (π ^ 2) * g l := by
    obtain ⟨a0, E, ha0, hc, hsm, hb, hd⟩ := hlocal q
    obtain ⟨a, h, g, s, hs, hval, hsm', hb', hd', hrel⟩ :=
      exists_popescu_cleared_conormal_chart π n m f a0 E hsm hb hd
    refine ⟨a, E, h, g, ?_, hc, hsm', hb', hd', hrel⟩
    intro ha
    apply ha0
    change Ideal.Quotient.mk I (red a) = Ideal.Quotient.mk I (red a0) ^ s at hval
    have hpower : ε (red a) = ε (red a0) ^ s := by
      rw [← he, hval, map_pow, he]
    exact q.1.isPrime.mem_of_pow_mem s (hpower ▸ ha)
  choose a E h g ha hcard hsm hb hd hrel using hcleared
  have : IsNoetherianRing Cbar := FiniteType.isNoetherianRing Rbar Cbar
  let W := {q : PrimeSpectrum Cbar | IsSmoothAtPrime Rbar q}
  let U : Q → Set (PrimeSpectrum Cbar) := fun q ↦ PrimeSpectrum.basicOpen (ε (red (a q)))
  have hcover : W ⊆ ⋃ q : Q, U q := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ha ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact W).elim_finite_subcover
    U (fun q ↦ (PrimeSpectrum.basicOpen (ε (red (a q)))).isOpen) hcover
  let idx : Fin t.card ≃ t := t.equivFin.symm
  let pick : Fin t.card → Q := fun k ↦ (idx k).1
  let d : PopescuLiftPresentation R Cbar π :=
    { n := n
      m := m
      r := t.card
      f := f
      a := fun k ↦ a (pick k)
      E := fun k ↦ E (pick k)
      h := fun k l j ↦ if l ∈ E (pick k) then
        (if l = j then a (pick k) else 0) else h (pick k) l j
      g := fun k l ↦ if l ∈ E (pick k) then 0 else g (pick k) l
      ε := ε }
  refine ⟨d, ?_⟩
  refine
    { surjective := hε
      kernel := hker
      cover := ?_
      smooth := fun k ↦ hsm (pick k)
      card_le := fun k ↦ hcard (pick k)
      conormal := fun k ↦ hb (pick k)
      differentials := fun k ↦ hd (pick k)
      relation := ?_
      normalized_h := ?_
      normalized_g := ?_ }
  · intro q hq
    obtain ⟨q0, hq0⟩ := Set.mem_iUnion.mp (ht hq)
    obtain ⟨hq0t, hU⟩ := Set.mem_iUnion.mp hq0
    refine ⟨idx.symm ⟨q0, hq0t⟩, ?_⟩
    change ε (red (a (pick (idx.symm ⟨q0, hq0t⟩)))) ∉ q.asIdeal
    change ε (red (a q0)) ∉ q.asIdeal at hU
    simpa only [pick, Equiv.apply_symm_apply] using hU
  · intro k l
    by_cases hl : l ∈ E (pick k)
    · simp [d, hl]
    · simpa only [d, ite_eq_right hl] using hrel (pick k) l
  · intro k l hl j
    exact ite_eq_left hl
  · intro k l hl
    exact ite_eq_left hl

end Algebra
