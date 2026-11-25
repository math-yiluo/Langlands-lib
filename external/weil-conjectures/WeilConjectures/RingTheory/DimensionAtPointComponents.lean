/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

universe u v

open scoped BigOperators
namespace AlgebraicGeometry

/-!
# Dimension at a point from irreducible components

Source: Stacks Project, Algebra, Lemma Tag 00OT
(blueprint: lem-weil-pbc-dimension-at-point-components).
-/

private theorem zeroLocus_dimension {S : Type v} [CommRing S] (q : Ideal S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (q : Set S)) = ringKrullDim (S ⧸ q) := by
  let h := PrimeSpectrum.isClosedEmbedding_comap_of_surjective
    (S ⧸ q) (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q)) =
      PrimeSpectrum.zeroLocus (q : Set S) := by
    simpa using range_comap_of_surjective
      (S ⧸ q) (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  rw [← hr, ← h.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (S ⧸ q)

private theorem quotient_dimension_le_localization
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q m : Ideal S) [q.IsPrime] [m.IsMaximal]
    (hqm : q ≤ m) : ringKrullDim (S ⧸ q) ≤
      ringKrullDim (Localization.AtPrime m) := by
  let M := m.map (Ideal.Quotient.mk q)
  have hker : RingHom.ker (Ideal.Quotient.mk q) ≤ m := by simpa using hqm
  let : M.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective hker
  have hcomap : M.comap (Ideal.Quotient.mk q) = m := by
    dsimp [M]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  have hd := (finiteTypeDomain_ringKrullDim_localizationAtMaximal
    (k := k) (S := S ⧸ q)).1 M
  rw [← hd, IsLocalization.AtPrime.ringKrullDim_eq_height M,
    IsLocalization.AtPrime.ringKrullDim_eq_height m]
  let f : PrimeSpectrum (S ⧸ q) → PrimeSpectrum S :=
    PrimeSpectrum.comap (Ideal.Quotient.mk q)
  have hf : StrictMono f := Monotone.strictMono_of_injective
    (fun _ _ h ↦ Ideal.comap_mono h)
    (fun _ _ h ↦ PrimeSpectrum.ext_iff.mpr <|
      Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective <| by
        simpa [f] using congrArg PrimeSpectrum.asIdeal h)
  have hh := Order.height_le_height_apply_of_strictMono f hf
    (⟨M, inferInstance⟩ : PrimeSpectrum (S ⧸ q))
  have hh' : M.height ≤ m.height := by
    simpa only [← PrimeSpectrum.height_eq_orderHeight, f, PrimeSpectrum.comap_asIdeal,
      hcomap] using hh
  exact WithBot.coe_mono hh'

private theorem localization_dimension_le_open
    {S : Type v} [CommRing S] (m : Ideal S) [m.IsPrime]
    (U : TopologicalSpace.Opens (PrimeSpectrum S))
    (hmU : (⟨m, inferInstance⟩ : PrimeSpectrum S) ∈ U) :
    ringKrullDim (Localization.AtPrime m) ≤ topologicalKrullDim U := by
  let x : U := ⟨⟨m, inferInstance⟩, hmU⟩
  let Z : TopologicalSpace.IrreducibleCloseds U :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hmap : TopologicalSpace.IrreducibleCloseds.map
      (Subtype.val : U → PrimeSpectrum S) U.isOpenEmbedding'.continuous Z =
      PrimeSpectrum.pointsEquivIrreducibleCloseds S (⟨m, inferInstance⟩ : PrimeSpectrum S) := by
    apply SetLike.coe_injective
    change closure (Subtype.val '' closure {x}) =
      closure {(⟨m, inferInstance⟩ : PrimeSpectrum S)}
    rw [closure_image_closure continuous_subtype_val]
    simp [x]
  have hco := U.isOpenEmbedding'.coheight_map Z
  rw [hmap] at hco
  have he := Order.height_orderIso (PrimeSpectrum.pointsEquivIrreducibleCloseds S)
    (⟨m, inferInstance⟩ : PrimeSpectrum S)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m]
  have hheight : m.height = Order.coheight Z := by
    rw [PrimeSpectrum.height_eq_orderHeight (⟨m, inferInstance⟩ : PrimeSpectrum S)]
    exact he.symm.trans hco
  rw [hheight]
  exact Order.coheight_le_krullDim Z

private theorem exists_maximal_in_open
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (U : TopologicalSpace.Opens (PrimeSpectrum S))
    (hpU : (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ U) :
    ∃ (m : Ideal S) (hm : m.IsMaximal), p ≤ m ∧
      (⟨m, hm.isPrime⟩ : PrimeSpectrum S) ∈ U := by
  obtain ⟨V, ⟨f, rfl⟩, hpf, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU U.isOpen
  have hJ := (isJacobsonRing_iff_prime_eq.mp
    (isJacobsonRing_of_finiteType (A := k) (B := S))) p inferInstance
  have hnot : f ∉ p.jacobson := by
    rw [hJ]
    exact hpf
  rw [Ideal.jacobson, Ideal.mem_sInf] at hnot
  push Not at hnot
  obtain ⟨m, ⟨hpm, hm⟩, hfm⟩ := hnot
  exact ⟨m, hm, hpm, hVU hfm⟩

private theorem exists_open_dimension_le_quotient_bound
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime]
    (qs : Finset (Ideal S))
    (hqs : ∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
      ∀ r : Ideal S, r.IsPrime → r ≤ q → r = q)
    (n : ℕ)
    (hbound : ∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ n) :
    ∃ U : TopologicalSpace.Opens (PrimeSpectrum S),
      (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ U ∧ topologicalKrullDim U ≤ n := by
  classical
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let A : Set (Ideal S) := {q | q ∈ minimalPrimes S ∧ ¬q ≤ p}
  have hA : A.Finite := (minimalPrimes.finite_of_isNoetherianRing S).subset
    (fun _ h ↦ h.1)
  let T : Set (PrimeSpectrum S) := ⋃ q ∈ A, PrimeSpectrum.zeroLocus (q : Set S)
  have hT : IsClosed T := hA.isClosed_biUnion (fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _)
  let U : TopologicalSpace.Opens (PrimeSpectrum S) := ⟨Tᶜ, hT.isOpen_compl⟩
  have hpU : (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ U := by
    intro hpT
    obtain ⟨q, hq, hqp⟩ := Set.mem_iUnion₂.mp hpT
    exact hq.2 hqp
  refine ⟨U, hpU, ?_⟩
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun c ↦ ?_
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds S
  let g : TopologicalSpace.IrreducibleCloseds U →
      TopologicalSpace.IrreducibleCloseds (PrimeSpectrum S) :=
    TopologicalSpace.IrreducibleCloseds.map Subtype.val continuous_subtype_val
  have hg : StrictMono g :=
    TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing
      Topology.IsInducing.subtypeVal
  let f : TopologicalSpace.IrreducibleCloseds U → (PrimeSpectrum S)ᵒᵈ :=
    e.symm.dual ∘ g
  have hf : StrictMono f := e.symm.dual.strictMono.comp hg
  let d := c.map f hf
  let r : PrimeSpectrum S := d.last
  obtain ⟨q, hq, hqr⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal S)) (J := r.asIdeal) bot_le
  have hlast : (g c.last : Set (PrimeSpectrum S)) =
      PrimeSpectrum.zeroLocus (r.asIdeal : Set S) := by
    have he : e r = g c.last := by
      exact e.apply_symm_apply (g c.last)
    have he' : closure {r} = (g c.last : Set (PrimeSpectrum S)) :=
      congrArg (fun Z : (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum S))ᵒᵈ ↦
        ((OrderDual.ofDual Z : TopologicalSpace.IrreducibleCloseds
          (PrimeSpectrum S)) : Set (PrimeSpectrum S))) he
    exact he'.symm.trans (PrimeSpectrum.closure_singleton r)
  obtain ⟨y, hy⟩ := c.last.isIrreducible.nonempty
  have hyq : y.val ∈ PrimeSpectrum.zeroLocus (q : Set S) := by
    have hyr : y.val ∈ PrimeSpectrum.zeroLocus (r.asIdeal : Set S) := by
      rw [← hlast]
      exact subset_closure ⟨y, hy, rfl⟩
    exact hqr.trans hyr
  have hqp : q ≤ p := by
    by_contra hnot
    exact y.property (Set.mem_iUnion₂.mpr ⟨q, ⟨hq, hnot⟩, hyq⟩)
  have hqmem : q ∈ qs := (hqs q).mpr ⟨hq.isPrime, hqp,
    fun t ht htq ↦ le_antisymm htq (hq.2 ⟨ht, bot_le⟩ htq)⟩
  have hqi : ∀ i : Fin (d.length + 1), q ≤ (d i : PrimeSpectrum S).asIdeal := by
    intro i
    exact hqr.trans (d.monotone (Fin.le_last i))
  let z : LTSeries (PrimeSpectrum.zeroLocus (q : Set S))ᵒᵈ :=
    LTSeries.mk d.length (fun i ↦ ⟨d i, hqi i⟩)
      (fun i j hij ↦ d.strictMono hij)
  have hz := Order.LTSeries.length_le_krullDim z
  have hdim : Order.krullDim (PrimeSpectrum.zeroLocus (q : Set S))ᵒᵈ =
      ringKrullDim (S ⧸ q) := by
    rw [Order.krullDim_orderDual, ringKrullDim_quotient]
  rw [hdim] at hz
  exact hz.trans (hbound q hqmem)

/-- Source: Stacks Project, Algebra, Lemma Tag 00OT
(blueprint: lem-weil-pbc-dimension-at-point-components).
The local Krull dimension of a finite type affine scheme over a field is the maximum of the
 dimensions of the irreducible components through the point, equivalently the maximum of the
 dimensions of the quotients by the minimal primes contained in the point, and is the minimum of
 the dimensions of the localizations at maximal ideals above the point.

Proof (Stacks 00OT): the components of `Spec S` are the `V(q_j)` for the finitely many minimal
primes, and `dim V(q_j) = dim S/q_j`; chains through `S/q_j` (00OS) give `dim S_m ≥ N` for every
maximal `m ⊇ p`, where `N = max dim S/q_i` over the minimal primes `q_i ⊆ p`; every open
neighbourhood of `p` contains a maximal ideal over `p` (Jacobson), so every neighbourhood has
dimension `≥ N`; the open `U` obtained by removing the components not through `x` has dimension
`≤ N`, so `dim_x X = N`, and a maximal `m₀ ⊇ p` in `U` has `dim S_{m₀} = N`. -/
theorem dimension_at_point_components
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] :
    let X := Spec (CommRingCat.of S)
    let x : X := ⟨p, inferInstance⟩
    ∃ qs : Finset (Ideal S),
      (∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
        ∀ r : Ideal S, r.IsPrime → r ≤ q → r = q) ∧
      qs.Nonempty ∧
      ∃ n : ℕ,
        topologicalKrullDimAt x = n ∧
        (∀ Z : Set X, Z ∈ irreducibleComponents X → x ∈ Z →
          topologicalKrullDim Z ≤ n) ∧
        (∃ Z : Set X, Z ∈ irreducibleComponents X ∧ x ∈ Z ∧
          topologicalKrullDim Z = n) ∧
        (∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ n) ∧
        (∃ q ∈ qs, ringKrullDim (S ⧸ q) = n) ∧
        (∀ (m : Ideal S) [m.IsMaximal], p ≤ m →
          (n : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m)) ∧
        (∃ (m : Ideal S) (_ : m.IsMaximal), p ≤ m ∧
          ringKrullDim (Localization.AtPrime m) = n)
    := by
  classical
  dsimp
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let T : Set (Ideal S) := {q | q ∈ minimalPrimes S ∧ q ≤ p}
  have hT : T.Finite := (minimalPrimes.finite_of_isNoetherianRing S).subset
    (fun _ h ↦ h.1)
  let qs := hT.toFinset
  have hqs : ∀ q : Ideal S, q ∈ qs ↔ q.IsPrime ∧ q ≤ p ∧
      ∀ r : Ideal S, r.IsPrime → r ≤ q → r = q := by
    intro q
    simp only [qs, Set.Finite.mem_toFinset, T, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hqp⟩
      exact ⟨hq.isPrime, hqp, fun r hr hrq ↦
        le_antisymm hrq (hq.2 ⟨hr, bot_le⟩ hrq)⟩
    · rintro ⟨hq, hqp, hmin⟩
      exact ⟨⟨⟨hq, bot_le⟩, fun r hr hrq ↦ (hmin r hr.1 hrq).ge⟩, hqp⟩
  have hne : qs.Nonempty := by
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S))
      (J := p) bot_le
    exact ⟨q, hT.mem_toFinset.mpr ⟨hq, hqp⟩⟩
  have hfinite : ∀ q ∈ qs, ∃ d : ℕ, ringKrullDim (S ⧸ q) = (d : WithBot ℕ∞) := by
    intro q hq
    let : q.IsPrime := ((hqs q).mp hq).1
    exact (finiteTypeDomain_ringKrullDim_localizationAtMaximal
      (k := k) (S := S ⧸ q)).2.imp (fun d hd ↦ hd.1)
  choose d hd using hfinite
  let f : Ideal S → ℕ := fun q ↦ if h : q ∈ qs then d q h else 0
  have hf : ∀ q ∈ qs, ringKrullDim (S ⧸ q) = (f q : WithBot ℕ∞) := by
    intro q hq
    simpa [f, hq] using hd q hq
  obtain ⟨q₀, hq₀, hmax⟩ := qs.exists_max_image f hne
  let n := f q₀
  have hbound : ∀ q ∈ qs, ringKrullDim (S ⧸ q) ≤ (n : WithBot ℕ∞) := by
    intro q hq
    rw [hf q hq]
    exact_mod_cast hmax q hq
  have hattain : ∃ q ∈ qs, ringKrullDim (S ⧸ q) = (n : WithBot ℕ∞) :=
    ⟨q₀, hq₀, hf q₀ hq₀⟩
  have hlower : ∀ (m : Ideal S) [m.IsMaximal], p ≤ m →
      (n : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
    intro m hm hpm
    obtain ⟨q, hq, heq⟩ := hattain
    obtain ⟨hpq, hqp, _⟩ := (hqs q).mp hq
    let : q.IsPrime := hpq
    rw [← heq]
    exact quotient_dimension_le_localization (k := k) q m (hqp.trans hpm)
  obtain ⟨U, hpU, hUdim⟩ :=
    exists_open_dimension_le_quotient_bound (k := k) p qs hqs n hbound
  have hdim : topologicalKrullDimAt
      (⟨p, inferInstance⟩ : PrimeSpectrum S) = (n : WithBot ℕ∞) := by
    unfold topologicalKrullDimAt
    refine le_antisymm ((iInf₂_le U hpU).trans hUdim) (le_iInf₂ fun W hpW ↦ ?_)
    obtain ⟨m, hm, hpm, hmW⟩ := exists_maximal_in_open (k := k) p W hpW
    let : m.IsMaximal := hm
    exact (hlower m hpm).trans (localization_dimension_le_open m W hmW)
  have hm : ∃ (m : Ideal S) (_ : m.IsMaximal), p ≤ m ∧
      ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
    obtain ⟨m, hm, hpm, hmU⟩ := exists_maximal_in_open (k := k) p U hpU
    let : m.IsMaximal := hm
    exact ⟨m, hm, hpm, le_antisymm
      ((localization_dimension_le_open m U hmU).trans hUdim) (hlower m hpm)⟩
  have hcomponents : ∀ Z : Set (PrimeSpectrum S),
      Z ∈ irreducibleComponents (PrimeSpectrum S) →
      (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ Z → topologicalKrullDim Z ≤ n := by
    intro Z hZ hxZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ
    obtain ⟨q, hq, rfl⟩ := hZ
    have hqp : q ≤ p := hxZ
    have hmem : q ∈ qs := (hqs q).mpr ⟨hq.isPrime, hqp,
      fun r hr hrq ↦ le_antisymm hrq (hq.2 ⟨hr, bot_le⟩ hrq)⟩
    simpa only [Function.comp_apply, zeroLocus_dimension] using hbound q hmem
  have hcomponent : ∃ Z : Set (PrimeSpectrum S),
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧
      (⟨p, inferInstance⟩ : PrimeSpectrum S) ∈ Z ∧ topologicalKrullDim Z = n := by
    obtain ⟨q, hq, hdimq⟩ := hattain
    obtain ⟨hpq, hqp, hmin⟩ := (hqs q).mp hq
    refine ⟨PrimeSpectrum.zeroLocus (q : Set S), ?_, hqp, ?_⟩
    · rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact ⟨q, ⟨⟨hpq, bot_le⟩, fun r hr hrq ↦ (hmin r hr.1 hrq).ge⟩, rfl⟩
    · rw [zeroLocus_dimension]
      exact hdimq
  exact ⟨qs, hqs, hne, n, hdim, hcomponents, hcomponent, hbound, hattain,
    hlower, hm⟩

end AlgebraicGeometry
