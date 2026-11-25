/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import WeilConjectures.RingTheory.FactorsThroughLocalization
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.FilteredColimitOfFactorization

/-! # Local-ring identifications with w-local target

Source: blueprint, proper base change, `theorem-proper-base-change-classical-pro`, lemma
`theorem-pro-etale-refinements-weakly-etale`
(blueprint: theorem-pro-etale-refinements-weakly-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

open scoped BigOperators

/-- Descend the inverse stalk map to a principal neighbourhood, then clear the finitely
many generator equalities. Source: blueprint theorem-pro-etale-refinements-weakly-etale,
proof paragraphs 1--2 (blueprint: theorem-pro-etale-refinements-weakly-etale). -/
private theorem local_factorization
    (A B P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P] [FinitePresentation A P]
    (q : Ideal B) [q.IsPrime]
    (hq : Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl))
    (α : P →ₐ[A] B) :
    ∃ (f : A) (g : B), g ∉ q ∧
      ∃ (β : P →ₐ[A] Localization.Away f)
        (γ : Localization.Away f →ₐ[A] Localization.Away g),
        γ.comp β = (IsScalarTower.toAlgHom A B (Localization.Away g)).comp α := by
  classical
  let p := q.comap (algebraMap A B)
  let l : Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    { Localization.localRingHom p q (algebraMap A B) rfl with
      commutes' := fun a ↦ by
        change Localization.localRingHom p q (algebraMap A B) rfl
          (algebraMap A (Localization.AtPrime p) a) = _
        rw [Localization.localRingHom_to_map]
        exact (IsScalarTower.algebraMap_apply A B (Localization.AtPrime q) a).symm }
  let e : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime q := AlgEquiv.ofBijective l hq
  let αq := (IsScalarTower.toAlgHom A B (Localization.AtPrime q)).comp α
  obtain ⟨f, β, k, hk⟩ := factors_through_principal_localization A P A p.primeCompl
    (e.symm.toAlgHom.comp αq)
  have hf : algebraMap A B (f : A) ∈ q.primeCompl := f.property
  let g₀ := algebraMap A B (f : A)
  let γ₀ : Localization.Away (f : A) →ₐ[A] Localization.Away g₀ :=
    IsLocalization.Away.liftAlgHom (f : A)
      (f := Algebra.ofId A (Localization.Away g₀))
      (IsLocalization.Away.algebraMap_isUnit g₀)
  let kq : Localization.Away g₀ →ₐ[A] Localization.AtPrime q :=
    IsLocalization.Away.liftAlgHom g₀
      (f := IsScalarTower.toAlgHom A B (Localization.AtPrime q))
      (IsLocalization.map_units _ ⟨g₀, hf⟩)
  have hkq (b : B) : kq (algebraMap B _ b) = algebraMap B _ b := by
    simp only [kq, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  have hmaps : kq.comp γ₀ = e.toAlgHom.comp k := by
    apply IsLocalization.algHom_ext (Submonoid.powers (f : A))
    ext
  have heq : kq.comp (γ₀.comp β) = αq := by
    rw [← AlgHom.comp_assoc, hmaps, AlgHom.comp_assoc, hk]
    ext x
    exact e.apply_symm_apply _
  obtain ⟨n, t, ht, _⟩ := FinitePresentation.out (R := A) (A := P)
  have kill (i : Fin n) : ∃ b : q.primeCompl,
      algebraMap B (Localization.Away g₀) b *
        ((γ₀.comp β) (t (MvPolynomial.X i)) -
          algebraMap B _ (α (t (MvPolynomial.X i)))) = 0 := by
    let x := (γ₀.comp β) (t (MvPolynomial.X i)) -
      algebraMap B (Localization.Away g₀) (α (t (MvPolynomial.X i)))
    obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj g₀ x
    have hx : kq x = 0 := by
      simp only [x, map_sub, hkq]
      exact sub_eq_zero.mpr (AlgHom.congr_fun heq _)
    have hczero : algebraMap B (Localization.AtPrime q) c = 0 := by
      have h := congrArg kq hc
      simpa only [map_mul, map_pow, hkq, hx, zero_mul] using h.symm
    obtain ⟨b, hb⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ c).mp hczero
    refine ⟨b, ?_⟩
    apply ((IsLocalization.Away.algebraMap_isUnit g₀).pow m).mul_right_cancel
    change (algebraMap B _ b * x) * algebraMap B _ g₀ ^ m = _
    rw [mul_assoc, hc, ← map_mul, hb, map_zero, zero_mul]
  choose b hb using kill
  let g : q.primeCompl := ⟨g₀, hf⟩ * ∏ i, b i
  let j : Localization.Away g₀ →ₐ[A] Localization.Away (g : B) :=
    IsLocalization.Away.liftAlgHom g₀
      (f := Algebra.algHom A B (Localization.Away (g : B)))
      (IsLocalization.Away.isUnit_of_dvd (g : B)
        (show g₀ ∣ (g : B) from ⟨_, rfl⟩))
  have hj (c : B) : j (algebraMap B _ c) = algebraMap B _ c := by
    simp only [j, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  refine ⟨f, g, g.property, β, j.comp γ₀, ?_⟩
  have hgen : (j.comp (γ₀.comp β)).comp t =
      ((IsScalarTower.toAlgHom A B (Localization.Away (g : B))).comp α).comp t := by
    apply MvPolynomial.algHom_ext
    intro i
    have hdvd : (b i : B) ∣ (g : B) := by
      exact (Finset.dvd_prod_of_mem (fun i ↦ (b i : B)) (Finset.mem_univ i)).trans
        (by
          change (∏ i, (b i : B)) ∣ g₀ * ↑(∏ i, b i)
          simpa only [Submonoid.coe_finsetProd] using dvd_mul_left (∏ i, (b i : B)) g₀)
    have h := congrArg j (hb i)
    simp only [map_mul, map_sub, hj, map_zero] at h
    exact sub_eq_zero.mp
      ((IsLocalization.Away.isUnit_of_dvd (g : B) hdvd).mul_left_cancel
        (h.trans (mul_zero _).symm))
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := ht x
  exact AlgHom.congr_fun hgen y

/-- Pull a disjoint clopen refinement on the closed points back along the continuous
closed-specialization map. Source: blueprint theorem-pro-etale-refinements-weakly-etale,
proof paragraph 2 (blueprint: theorem-pro-etale-refinements-weakly-etale). -/
private theorem clopen_refinement
    (B : Type u) [CommRing B] [IsWLocalRing B]
    (ι : Type u) (O : ι → TopologicalSpace.Opens (PrimeSpectrum B))
    (hO : ∀ c : closedPoints (PrimeSpectrum B), ∃ i, (c : PrimeSpectrum B) ∈ O i) :
    ∃ (n : ℕ) (Q : Fin n → Set (PrimeSpectrum B)) (r : Fin n → ι),
      (∀ i, IsClopen (Q i)) ∧ Pairwise (fun i j ↦ Disjoint (Q i) (Q j)) ∧
      (⋃ i, Q i) = Set.univ ∧ ∀ i, Q i ⊆ O (r i) := by
  classical
  let H := WLocalSpace.closedPointsHomeomorph (X := PrimeSpectrum B)
  let π : PrimeSpectrum B → closedPoints (PrimeSpectrum B) :=
    fun x ↦ H.symm (ConnectedComponents.mk x)
  have hπ : Continuous π := H.symm.continuous.comp ConnectedComponents.continuous_coe
  have : T2Space (closedPoints (PrimeSpectrum B)) := H.symm.t2Space
  have : TotallyDisconnectedSpace (closedPoints (PrimeSpectrum B)) :=
    H.symm.totallyDisconnectedSpace
  let U : ι → TopologicalSpace.Opens (closedPoints (PrimeSpectrum B)) :=
    fun i ↦ (O i).comap ⟨Subtype.val, continuous_subtype_val⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.mk
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    exact Set.eq_univ_of_forall fun c ↦ Set.mem_iUnion.mpr (hO c)
  obtain ⟨n, V, hV, hcover, hdisj⟩ :=
    hU.exists_finite_nonempty_disjoint_clopen_cover
  choose r hr using fun i ↦ (hV i).2
  let Q := fun i ↦ π ⁻¹' (V i : Set (closedPoints (PrimeSpectrum B)))
  have hQ (i : Fin n) : IsClopen (Q i) := (V i).isClopen.preimage hπ
  refine ⟨n, Q, r, hQ, ?_, ?_, fun i x hx ↦ ?_⟩
  · intro i j hij
    exact (TopologicalSpace.Clopens.coe_disjoint.mpr (hdisj hij)).preimage π
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (π x)))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
    have hπx : π x = ⟨c, mem_closedPoints_iff.mpr hc⟩ := by
      apply H.injective
      change H (H.symm (ConnectedComponents.mk x)) = ConnectedComponents.mk c
      rw [H.apply_symm_apply]
      exact hxc.connectedComponents_mk_eq
    have hcV : (⟨c, mem_closedPoints_iff.mpr hc⟩ : closedPoints (PrimeSpectrum B)) ∈ V i := by
      change π x ∈ V i at hx
      rwa [hπx] at hx
    exact hxc.mem_open (O (r i)).isOpen (hr i hcV)

/-- Patch neighbourhood factorizations using the Chinese remainder isomorphism associated
with a finite clopen partition. Source: blueprint theorem-pro-etale-refinements-weakly-etale,
proof paragraph 2 (blueprint: theorem-pro-etale-refinements-weakly-etale). -/
private theorem patch_factorization
    (A B P : Type u) [CommRing A] [CommRing B] [CommRing P]
    [Algebra A B] [Algebra A P]
    (α : P →ₐ[A] B) (n : ℕ) (f : Fin n → A) (g : Fin n → B)
    (β : ∀ i, P →ₐ[A] Localization.Away (f i))
    (γ : ∀ i, Localization.Away (f i) →ₐ[A] Localization.Away (g i))
    (hfactor : ∀ i, (γ i).comp (β i) =
      (IsScalarTower.toAlgHom A B (Localization.Away (g i))).comp α)
    (Q : Fin n → Set (PrimeSpectrum B)) (hQ : ∀ i, IsClopen (Q i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i) (Q j)))
    (hcover : (⋃ i, Q i) = Set.univ)
    (hsub : ∀ i, Q i ⊆ PrimeSpectrum.basicOpen (g i)) :
    ∃ δ : ((i : Fin n) → Localization.Away (f i)) →ₐ[A] B,
      δ.comp (AlgHom.pi β) = α := by
  classical
  choose e he heQ using fun i ↦
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hQ i)
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij ↦ ?_⟩
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) .zero
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_zero]
    apply TopologicalSpace.Opens.ext
    change (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B)) ∩
      (PrimeSpectrum.basicOpen (e j) : Set (PrimeSpectrum B)) = ∅
    rw [← heQ i, ← heQ j]
    exact Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)
  have hcomplete : CompleteOrthogonalIdempotents e := by
    refine ⟨hortho, ?_⟩
    have hs : IsIdempotentElem (∑ i, e i) := by
      simpa using hortho.isIdempotentElem_sum (s := Finset.univ)
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs .one
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    change (∑ i, e i) ∉ x.asIdeal ↔ (1 : B) ∉ x.asIdeal
    refine ⟨fun _ ↦ x.isPrime.one_notMem, fun _ ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
    have hei : e i ∉ x.asIdeal := by
      have := hi
      rw [heQ i] at this
      exact this
    intro hsum
    apply hei
    have h := x.asIdeal.mul_mem_left (e i) hsum
    rwa [hortho.mul_sum_of_mem (Finset.mem_univ i)] at h
  let J : Fin n → Ideal B := fun i ↦ Ideal.span {1 - e i}
  let C := fun i ↦ B ⧸ J i
  let π : B →ₐ[A] ((i : Fin n) → C i) := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ A (J i)
  let E : B ≃ₐ[A] ((i : Fin n) → C i) := AlgEquiv.ofBijective π hcomplete.bijective_pi
  have hg (i : Fin n) : IsUnit (algebraMap B (C i) (g i)) := by
    apply Ideal.span_singleton_eq_top.mp
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let q : PrimeSpectrum B :=
      PrimeSpectrum.comap (algebraMap B (C i)) ⟨m, hm.isPrime⟩
    have h1e : 1 - e i ∈ q.asIdeal := by
      change algebraMap B (C i) (1 - e i) ∈ m
      have hz : algebraMap B (C i) (1 - e i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [hz]
      exact m.zero_mem
    have heq : e i ∉ q.asIdeal := by
      intro h
      apply q.isPrime.ne_top
      apply (Ideal.eq_top_iff_one q.asIdeal).mpr
      simpa using q.asIdeal.add_mem h1e h
    have hqQ : q ∈ Q i := by rw [heQ i]; exact heq
    exact hsub i hqQ (hle (Ideal.subset_span (Set.mem_singleton _)))
  let ρ : ∀ i, Localization.Away (g i) →ₐ[A] C i := fun i ↦
    IsLocalization.Away.liftAlgHom (g i)
      (f := IsScalarTower.toAlgHom A B (C i)) (hg i)
  have hρ (i : Fin n) (b : B) : ρ i (algebraMap B _ b) = algebraMap B (C i) b := by
    simp only [ρ, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
    rfl
  let δ₀ : ((i : Fin n) → Localization.Away (f i)) →ₐ[A] ((i : Fin n) → C i) :=
    AlgHom.pi fun i ↦ ((ρ i).comp (γ i)).comp (Pi.evalAlgHom A _ i)
  refine ⟨E.symm.toAlgHom.comp δ₀, ?_⟩
  apply AlgHom.ext
  intro x
  apply E.injective
  change E (E.symm (δ₀ (AlgHom.pi β x))) = E (α x)
  rw [E.apply_symm_apply]
  funext i
  change ρ i (γ i (β i x)) = algebraMap B (C i) (α x)
  change ρ i (((γ i).comp (β i)) x) = _
  rw [AlgHom.congr_fun (hfactor i) x]
  exact hρ i (α x)

/-- A ring map identifying all prime localizations and having w-local target presents that
 target as a filtered colimit of finite products of principal localizations of the source.
 No w-locality of the source or of the map is assumed.

Source: blueprint, proper base change, `theorem-proper-base-change-classical-pro`, lemma
`theorem-pro-etale-refinements-weakly-etale`
(blueprint: theorem-pro-etale-refinements-weakly-etale).

Proof:
1. Given a finitely presented algebra `P` and `α : P → B`, invert the stalk isomorphism
   at each prime `q`. Apply `factors_through_principal_localization` to descend the resulting
   map `P → A_p` to `β : P → A_f`, with `f` outside the contracted prime `p`.
2. Map `A_f` canonically to `B` localized at `g₀ = algebraMap A B f`. Its composite with
   `β` agrees with `α` in `B_q`, by localization extensionality. Choose a finite polynomial
   presentation of `P`. For each generator, write the difference as a fraction in `B_g₀`;
   its numerator vanishes in `B_q`, hence has an annihilator outside `q`. Multiply these
   annihilators with `g₀` to obtain `g` outside `q`. After mapping to `B_g`, all differences
   vanish by unit cancellation. Equality on generators and surjectivity give the desired
   factorization `P → A_f → B_g`.
3. The proved homeomorphism `WLocalSpace.closedPointsHomeomorph` makes the closed points
   profinite. Mathlib's finite disjoint clopen refinement theorem gives a finite partition
   subordinate to the neighbourhoods `D(g)`. Pull it back to the spectrum along the
   continuous map sending a point to the closed point of its connected component.
   A point specializes to that closed point, so each pulled-back part stays inside its
   selected open. This includes the empty partition of the empty spectrum.
4. Associate idempotents `e_i` to the clopen parts. Disjointness and injectivity of the
   idempotent/basic-open correspondence give orthogonality. The sum is idempotent and
   belongs to no prime, so its basic open is `D(1)` and the same injectivity gives sum one.
   `CompleteOrthogonalIdempotents.bijective_pi` identifies `B` with `∏ B/(1-e_i)`.
5. Each selected `g_i` becomes a unit in `B/(1-e_i)`: otherwise a maximal ideal containing
   it contracts to a prime in `D(e_i)`, contradicting `D(e_i) ⊆ D(g_i)`. Extend the local
   maps by the localization universal property and compose their product with the inverse
   Chinese remainder isomorphism. This gives `P → ∏ A_fᵢ → B` with composite `α`.
6. Principal localizations are finitely presented by
   `IsLocalization.Away.finitePresentation`; their finite products are finitely presented
   by `Algebra.FinitePresentation.pi`, including the empty product. Transport along algebra
   equivalences, and let `E` be the set of all algebras equivalent to these products.
7. Apply `CommAlgCat.exists_filtered_colimit_of_factorization` to `E` and step 5. Its small
   filtered diagram and colimit cocone give exactly `IsIndPrincipalZariski A B`. -/
theorem isIndPrincipalZariski_of_bijective_localRingHom
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsWLocalRing B]
    (hlocal : ∀ (q : Ideal B) [q.IsPrime],
      Function.Bijective
        (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl)) :
    IsIndPrincipalZariski A B := by
  classical
  let E : Set (CommAlgCat.{u} A) := fun C ↦
    ∃ (n : ℕ) (f : Fin n → A),
      Nonempty (C ≃ₐ[A] ((i : Fin n) → Localization.Away (f i)))
  have hfp : ∀ C ∈ E, FinitePresentation A C := by
    rintro C ⟨n, f, ⟨e⟩⟩
    exact FinitePresentation.equiv e.symm
  have hfact : ∀ (P : CommAlgCat.{u} A), FinitePresentation A P →
      ∀ α : P ⟶ CommAlgCat.of A B,
      ∃ C ∈ E, ∃ (β : P ⟶ C) (γ : C ⟶ CommAlgCat.of A B), β ≫ γ = α := by
    intro P hP α
    have := hP
    have hloc (q : PrimeSpectrum B) :=
      local_factorization A B P q.asIdeal (hlocal q.asIdeal) α.hom
    choose f g hg β γ hγ using hloc
    obtain ⟨n, Q, r, hQ, hdisj, hcover, hsub⟩ :=
      clopen_refinement B (PrimeSpectrum B) (fun q ↦ PrimeSpectrum.basicOpen (g q))
        (fun c ↦ ⟨c.val, hg c.val⟩)
    obtain ⟨δ, hδ⟩ := patch_factorization A B P α.hom n
      (f ∘ r) (g ∘ r) (fun i ↦ β (r i)) (fun i ↦ γ (r i))
      (fun i ↦ hγ (r i)) Q hQ hdisj hcover hsub
    refine ⟨CommAlgCat.of A ((i : Fin n) → Localization.Away (f (r i))),
      ⟨n, f ∘ r, ⟨AlgEquiv.refl⟩⟩, CommAlgCat.ofHom (AlgHom.pi (fun i ↦ β (r i))),
      CommAlgCat.ofHom δ, ?_⟩
    exact CommAlgCat.hom_ext hδ
  obtain ⟨I, hI, hfiltered, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization A (CommAlgCat.of A B) E hfp hfact
  exact ⟨I, hI, hfiltered, ⟨D, ι, hc⟩, hD⟩

end Algebra
