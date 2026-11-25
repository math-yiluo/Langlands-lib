/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis

/-!
# The profinite tower of the integers in a finite p-adic extension

Stacks Project, Tags 08ZU, 0ET8, 08ZY and 08ZZ
(auxiliary; not a blueprint node).

## Main definitions and statements

* `Padic.coefficientExtensionPositiveLimit`: compatible families at exponents `n + 1`.
* `Padic.coefficientExtensionIntegersTopology`: the absolute-value subspace topology.
* `Padic.coefficientExtensionPositiveLimitTopology`: the discrete-product subspace topology.
* `Padic.coefficientExtension_integers_profinite_tower`: the canonical ring and topological
  identification, profiniteness, and eventual unique factorization through finite levels.
-/

@[expose] public section

universe u v

namespace Padic

/-- The compatible-family subring of the positive coefficient levels. Coordinate `n` is
the quotient at exponent `n + 1`; equalizers impose precisely the successive reductions.
Ring operations are inherited coordinatewise from the product.

Stacks Tag 08ZY
(auxiliary; not a blueprint node). -/
noncomputable def coefficientExtensionPositiveLimit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Subring (∀ n : ℕ, coefficientExtensionRing l E (n + 1)) :=
  ⨅ n : ℕ, RingHom.eqLocus
    ((coefficientExtensionTransition l E (n + 1)).comp
      (Pi.evalRingHom (fun k : ℕ ↦ coefficientExtensionRing l E (k + 1)) (n + 1)))
    (Pi.evalRingHom (fun k : ℕ ↦ coefficientExtensionRing l E (k + 1)) n)

/-- The topology on the integers induced from the spectral absolute value on `E`.
This is the extending absolute value recorded by the coefficient-extension dependency.

(auxiliary; not a blueprint node). -/
@[instance_reducible]
noncomputable def coefficientExtensionIntegersTopology (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    TopologicalSpace (coefficientExtensionIntegers l E) :=
  letI := spectralNorm.normedField (Padic l) E
  TopologicalSpace.induced (fun x : coefficientExtensionIntegers l E ↦ (x : E))
    inferInstance

/-- The subspace topology from the product of the discrete positive coefficient rings.

Stacks Tag 08ZY
(auxiliary; not a blueprint node). -/
@[instance_reducible]
noncomputable def coefficientExtensionPositiveLimitTopology (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    TopologicalSpace (coefficientExtensionPositiveLimit l E) :=
  TopologicalSpace.induced
    (fun b : coefficientExtensionPositiveLimit l E ↦ b.val)
    (@Pi.topologicalSpace ℕ (fun n ↦ coefficientExtensionRing l E (n + 1)) (fun _ ↦ ⊥))

/-- The reductions identify the integers with their profinite tower as rings and spaces.
They are compact, Hausdorff and totally disconnected. Every continuous surjection to
a finite discrete set factors uniquely through every sufficiently high positive level.

Stacks Tags 08ZU, 0ET8, 08ZY and 08ZZ
(auxiliary; not a blueprint node).

Proof: (1) By lem-weil-l-adic-extension-integers-dvr the uniformizer has absolute value
`r` with `0 < r < 1`, and units have value one. Nonarchimedeanness from
lem-weil-l-adic-extension-absolute-value gives membership in its nth ideal power exactly
when the absolute value is at most `r ^ n`. These cosets are clopen and form a neighbourhood
basis. Lem-weil-valued-dvr-finite-quotients supplies finite quotients and surjective
transitions. (2) Compatible reductions define a ring homomorphism. If two elements have
the same reductions, their difference has value at most every `r ^ n`, hence is zero.
(3) Representatives of a compatible family are Cauchy by the same estimate. Completeness
from lem-weil-l-adic-extension-complete gives a limit in the closed unit ball. Each of
its reductions is the specified coordinate. This proves surjectivity and hence the ring
isomorphism. (4) Coordinate cylinders form a basis on the inverse limit: dominate the
finitely many restricted coordinates by their maximum. Their inverse images are exactly
the coset basis, proving continuity in both directions. (5) Properness from
lem-weil-l-adic-extension-proper makes the closed unit ball compact. (6) The metric is
Hausdorff; distinct points have distinct reductions, so a clopen coset separates them.
Thus every connected subset has at most one point. (7) The open fibres of the finite discrete
map contain coset neighbourhoods. Compactness gives finitely many of them covering the
integers. Their maximum exponent ensures that the map is constant on every coset at
that level, defining its factorization. The cover is nonempty since it covers zero.
(8) Surjectivity of reduction makes the factor unique. Composing with reduction from
any higher level gives its factorization there, again unique by surjectivity.
-/
theorem coefficientExtension_integers_profinite_tower (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∃ e : coefficientExtensionIntegers l E ≃+* coefficientExtensionPositiveLimit l E,
      (∀ (x : coefficientExtensionIntegers l E) (n : ℕ),
        (e x).val n = Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) x) ∧
      @IsHomeomorph _ _ (coefficientExtensionIntegersTopology l E)
        (coefficientExtensionPositiveLimitTopology l E) e) ∧
    @CompactSpace _ (coefficientExtensionIntegersTopology l E) ∧
    @T2Space _ (coefficientExtensionIntegersTopology l E) ∧
    @TotallyDisconnectedSpace _ (coefficientExtensionIntegersTopology l E) ∧
    (∀ (Q : Type v) [Finite Q] (g : coefficientExtensionIntegers l E → Q),
      @Continuous _ _ (coefficientExtensionIntegersTopology l E) ⊥ g →
      Function.Surjective g →
      ∃ n : ℕ, 1 ≤ n ∧ ∀ m : ℕ, n ≤ m →
        ∃! h : coefficientExtensionRing l E m → Q,
          g = h ∘ Ideal.Quotient.mk (coefficientExtensionIdeal l E m)) := by
  classical
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let : NormedSpace (Padic l) E := spectralNorm.normedSpace (Padic l) E
  let : ProperSpace E := FiniteDimensional.proper (Padic l) E
  let R := coefficientExtensionIntegers l E
  let A := fun n : ℕ ↦ coefficientExtensionRing l E (n + 1)
  let q := fun n : ℕ ↦ Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1))
  have hb := coefficientExtension_integers_coset_basis l E
  have hO : ∀ x : E, x ∈ R ↔ ‖x‖ ≤ 1 :=
    (coefficientExtensionIntegers_dvr l E).choose_spec.1
  have hc : CompactSpace R := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    have he : (R : Set E) = Metric.closedBall 0 1 := by
      ext x
      change x ∈ R ↔ _
      rw [hO]
      simp only [Metric.mem_closedBall, dist_zero_right]
    change IsCompact (R : Set E)
    rw [he]
    exact isCompact_closedBall (0 : E) 1
  let : CompactSpace R := hc
  let : ∀ n, TopologicalSpace (A n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (A n) := fun _ ↦ ⟨rfl⟩
  have hq : ∀ n, IsLocallyConstant (q n) := by
    intro n
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    exact (hb x).mem_of_mem (i := n) trivial
  have hcont : ∀ n, Continuous (q n) := fun n ↦ (hq n).continuous
  let f : R →+* coefficientExtensionPositiveLimit l E :=
    { toFun := fun x ↦ ⟨fun n ↦ q n x, by
        simp only [coefficientExtensionPositiveLimit, Subring.mem_iInf,
          RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]
        intro n
        rfl⟩
      map_one' := by apply Subtype.ext; funext n; exact map_one (q n)
      map_mul' := fun x y ↦ by apply Subtype.ext; funext n; exact map_mul (q n) x y
      map_zero' := by apply Subtype.ext; funext n; exact map_zero (q n)
      map_add' := fun x y ↦ by apply Subtype.ext; funext n; exact map_add (q n) x y }
  have hfinj : Function.Injective f := by
    intro x y he
    apply (pure_le_nhds_iff.mp ?_ : x = y)
    intro U hU
    obtain ⟨n, _, hn⟩ := (hb y).mem_iff.mp hU
    exact hn (congrArg (fun a : coefficientExtensionPositiveLimit l E ↦ a.val n) he)
  have hfsurj : Function.Surjective f := by
    intro b
    let S : ℕ → Set R := fun n ↦ {x | q n x = b.val n}
    have hcl n : IsClosed (S n) := (hq n).isClosed_fiber _
    have hnon n : (S n).Nonempty := Ideal.Quotient.mk_surjective (b.val n)
    have hbcompat n : coefficientExtensionTransition l E (n + 1) (b.val (n + 1)) =
        b.val n :=
      (Subring.mem_iInf.mp b.property n : _)
    have hstep n : S (n + 1) ⊆ S n := by
      intro x hx
      have he := congrArg (coefficientExtensionTransition l E (n + 1)) hx
      exact he.trans (hbcompat n)
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hstep hnon
        (hcl 0).isCompact hcl
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext n
    exact Set.mem_iInter.mp hx n
  let : TopologicalSpace (coefficientExtensionPositiveLimit l E) :=
    coefficientExtensionPositiveLimitTopology l E
  have hfcont : Continuous f := by
    apply continuous_induced_rng.mpr
    exact continuous_pi hcont
  have hpi : @T2Space (∀ n, A n)
      (@Pi.topologicalSpace ℕ A (fun _ ↦ ⊥)) :=
    @Pi.t2Space ℕ A (fun _ ↦ ⊥)
      (fun n ↦ @DiscreteTopology.toT2Space (A n) ⊥ ⟨rfl⟩)
  have hemb : @Topology.IsEmbedding (coefficientExtensionPositiveLimit l E) (∀ n, A n)
      (coefficientExtensionPositiveLimitTopology l E)
      (@Pi.topologicalSpace ℕ A (fun _ ↦ ⊥)) (fun b ↦ b.val) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  have : T2Space (coefficientExtensionPositiveLimit l E) := hemb.t2Space
  have hhome : IsHomeomorph f :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hfcont, hfinj, hfsurj⟩
  have htd : TotallyDisconnectedSpace R := by
    constructor
    intro t _ ht x hx y hy
    apply hfinj
    apply Subtype.ext
    funext n
    exact (hq n).apply_eq_of_isPreconnected ht hx hy
  let e := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨⟨e, fun _ _ ↦ rfl, hhome⟩, hc, inferInstance, htd, ?_⟩
  intro Q _ g hg _
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  have hg' : Continuous g := hg
  have hlocal (x : R) : ∃ n : ℕ, ∀ y : R, q n y = q n x → g y = g x := by
    have hU : {y | g y = g x} ∈ nhds x :=
      ((IsLocallyConstant.iff_continuous g).mpr hg').eventually_eq x
    obtain ⟨n, _, hn⟩ := (hb x).mem_iff.mp hU
    exact ⟨n, fun y hy ↦ hn hy⟩
  choose n hn using hlocal
  let U : R → Set R := fun x ↦ {y | q (n x) y = q (n x) x}
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x ↦ (hq (n x)).isOpen_fiber _) (by intro x _; exact Set.mem_iUnion.mpr ⟨x, rfl⟩)
  let N := t.sup n
  refine ⟨N + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  intro m hm
  let qm := Ideal.Quotient.mk (coefficientExtensionIdeal l E m)
  have hconstant {x y : R} (hxy : qm x = qm y) : g x = g y := by
    obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hnm : n z + 1 ≤ m :=
      (Nat.add_le_add_right (Finset.le_sup hzt) 1).trans hm
    have hqxy : q (n z) x = q (n z) y := by
      apply Ideal.Quotient.eq.mpr
      exact Ideal.pow_le_pow_right hnm (Ideal.Quotient.eq.mp hxy)
    exact (hn z x hz).trans (hn z y (hqxy.symm.trans hz)).symm
  let h : coefficientExtensionRing l E m → Q := fun a ↦ g (Quotient.out a)
  have hh : g = h ∘ qm := by
    funext x
    apply hconstant
    exact (Ideal.Quotient.mk_out (qm x)).symm
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  funext a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (congrFun hh' x).symm.trans (congrFun hh x)

end Padic
