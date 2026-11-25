/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Algebras spanned by idempotents

Let `K` be a field and `R` a `K`-algebra which is spanned over `K` by a set `E` of idempotents
(e.g. `R = LocallyConstant T K`, or a filtered colimit of finite products of copies of `K`).
Then every element of `R` is congruent to a scalar modulo every prime, every prime of `R` is
maximal and is determined by the elements of `E` it contains, and the local rings of `R` are
copies of `K`. In particular, if `K` is separably closed, `R` is w-strictly local, and it is
w-contractible as soon as its space of connected components is extremally disconnected.

We also give a criterion for a continuous map to induce a homeomorphism on spaces of connected
components, and its incarnation for ring maps in terms of idempotents.

## Main statements

- `IsWStrictlyLocalRing.of_forall_mem_span_isIdempotentElem`
- `IsWContractibleRing.of_forall_mem_span_isIdempotentElem`
- `Continuous.isHomeomorph_connectedComponentsMap`
- `PrimeSpectrum.isHomeomorph_connectedComponentsMap_comap`
-/

@[expose] public section

open PrimeSpectrum TopologicalSpace

section Span

variable {K R : Type*} [CommRing R]

/-- If `x` is a `K`-linear combination of the idempotents of a set `E`, then for every prime
`P` there is an idempotent `s ∉ P` on which `x` acts as a scalar `k`. -/
theorem exists_isIdempotentElem_mul_eq_algebraMap_mul [CommRing K] [Algebra K R] {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (P : Ideal R) [P.IsPrime] {x : R}
    (hx : x ∈ Submodule.span K E) :
    ∃ (s : R) (k : K), IsIdempotentElem s ∧ s ∉ P ∧ s * x = algebraMap K R k * s := by
  induction hx using Submodule.span_induction with
  | mem e he =>
    by_cases heP : e ∈ P
    · refine ⟨1 - e, 0, (hE e he).one_sub, fun h ↦ ?_, ?_⟩
      · exact Ideal.IsPrime.one_notMem ‹_› (by simpa using add_mem h heP)
      · rw [sub_mul, one_mul, (hE e he).eq, sub_self, map_zero, zero_mul]
    · exact ⟨e, 1, hE e he, heP, by rw [(hE e he).eq, map_one, one_mul]⟩
  | zero => exact ⟨1, 0, .one, Ideal.IsPrime.one_notMem ‹_›, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, k, hs, hsP, hsx⟩ := hx
    obtain ⟨s', k', hs', hs'P, hs'y⟩ := hy
    refine ⟨s * s', k + k', hs.mul hs', fun h ↦ (Ideal.IsPrime.mem_or_mem ‹_› h).elim hsP hs'P,
      ?_⟩
    rw [map_add]
    linear_combination s' * hsx + s * hs'y
  | smul c x _ hx =>
    obtain ⟨s, k, hs, hsP, hsx⟩ := hx
    refine ⟨s, c * k, hs, hsP, ?_⟩
    rw [Algebra.smul_def, mul_left_comm, hsx, map_mul]
    ring

/-- If `x` is a `K`-linear combination of the idempotents of a set `E` and two primes `P`, `Q`
contain the same elements of `E`, then `x` is congruent to the same scalar modulo `P` and `Q`. -/
theorem exists_sub_algebraMap_mem_and_mem [CommRing K] [Algebra K R] {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : ∀ e ∈ E, e ∈ P ↔ e ∈ Q) {x : R} (hx : x ∈ Submodule.span K E) :
    ∃ k : K, x - algebraMap K R k ∈ P ∧ x - algebraMap K R k ∈ Q := by
  have hmem (I : Ideal R) [I.IsPrime] (e : R) (he : IsIdempotentElem e) (heI : e ∉ I) :
      e - 1 ∈ I := by
    refine (Ideal.IsPrime.mem_or_mem ‹_› (?_ : e * (e - 1) ∈ I)).resolve_left heI
    rw [mul_sub, mul_one, he.eq, sub_self]
    exact I.zero_mem
  induction hx using Submodule.span_induction with
  | mem e he =>
    by_cases heP : e ∈ P
    · exact ⟨0, by simpa using heP, by simpa using (hPQ e he).mp heP⟩
    · exact ⟨1, by simpa using hmem P e (hE e he) heP,
        by simpa using hmem Q e (hE e he) (fun h ↦ heP ((hPQ e he).mpr h))⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hkP, hkQ⟩ := hx
    obtain ⟨k', hk'P, hk'Q⟩ := hy
    refine ⟨k + k', ?_, ?_⟩
    · convert add_mem hkP hk'P using 1
      rw [map_add]
      ring
    · convert add_mem hkQ hk'Q using 1
      rw [map_add]
      ring
  | smul c x _ hx =>
    obtain ⟨k, hkP, hkQ⟩ := hx
    refine ⟨c * k, ?_, ?_⟩
    · convert P.mul_mem_left (algebraMap K R c) hkP using 1
      rw [Algebra.smul_def, map_mul]
      ring
    · convert Q.mul_mem_left (algebraMap K R c) hkQ using 1
      rw [Algebra.smul_def, map_mul]
      ring

variable [Field K] [Algebra K R]

/-- A scalar of a field lies in a prime only if it vanishes. -/
lemma algebraMap_mem_iff_eq_zero (P : Ideal R) [P.IsPrime] (k : K) :
    algebraMap K R k ∈ P ↔ k = 0 := by
  refine ⟨fun h ↦ by_contra fun hk ↦ Ideal.IsPrime.ne_top ‹_› ?_, fun h ↦ by simp [h]⟩
  exact Ideal.eq_top_of_isUnit_mem _ h ((IsUnit.mk0 k hk).map _)

/-- In a `K`-algebra spanned by a set `E` of idempotents, a prime is determined by the elements
of `E` it contains. -/
theorem Ideal.eq_of_forall_mem_span_isIdempotentElem {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (hR : ∀ x : R, x ∈ Submodule.span K E)
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (hPQ : ∀ e ∈ E, e ∈ P ↔ e ∈ Q) : P = Q := by
  have key (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : ∀ e ∈ E, e ∈ P ↔ e ∈ Q) :
      P ≤ Q := by
    intro x hx
    obtain ⟨k, hkP, hkQ⟩ := exists_sub_algebraMap_mem_and_mem hE P Q hPQ (hR x)
    have hk : k = 0 := by
      rw [← algebraMap_mem_iff_eq_zero P k]
      simpa using sub_mem hx hkP
    simpa [hk] using hkQ
  exact le_antisymm (key P Q hPQ) (key Q P fun e he ↦ (hPQ e he).symm)

/-- In a `K`-algebra spanned by idempotents, every prime is maximal. -/
theorem Ideal.IsPrime.isMaximal_of_forall_mem_span_isIdempotentElem {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (hR : ∀ x : R, x ∈ Submodule.span K E)
    (P : Ideal R) [P.IsPrime] : P.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨Ideal.IsPrime.one_notMem ‹_›, fun J x hPJ hxP hxJ ↦ ?_⟩
  obtain ⟨k, hkP, -⟩ := exists_sub_algebraMap_mem_and_mem hE P P (fun _ _ ↦ Iff.rfl) (hR x)
  have hk : k ≠ 0 := by
    rintro rfl
    exact hxP (by simpa using hkP)
  have h1 : (1 : R) = algebraMap K R k⁻¹ * x - algebraMap K R k⁻¹ * (x - algebraMap K R k) := by
    rw [mul_sub, sub_sub_cancel, ← map_mul, inv_mul_cancel₀ hk, map_one]
  rw [h1]
  exact sub_mem (J.mul_mem_left _ hxJ) (hPJ (P.mul_mem_left _ hkP))

/-- In a `K`-algebra spanned by idempotents, every localization at a prime is a copy of `K`. -/
theorem bijective_algebraMap_localization_of_forall_mem_span_isIdempotentElem {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (hR : ∀ x : R, x ∈ Submodule.span K E)
    (P : Ideal R) [P.IsPrime] :
    Function.Bijective (algebraMap K (Localization.AtPrime P)) := by
  refine ⟨(algebraMap K _).injective, fun y ↦ ?_⟩
  have hval (x : R) : ∃ k : K, algebraMap R (Localization.AtPrime P) x =
      algebraMap K (Localization.AtPrime P) k := by
    obtain ⟨s, k, -, hsP, hs⟩ := exists_isIdempotentElem_mul_eq_algebraMap_mul hE P (hR x)
    refine ⟨k, ?_⟩
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P s).mpr hsP
    refine hu.mul_right_injective ?_
    dsimp only
    rw [← map_mul, hs, map_mul, IsScalarTower.algebraMap_apply K R (Localization.AtPrime P),
      mul_comm]
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  obtain ⟨kx, hkx⟩ := hval x
  obtain ⟨kt, hkt⟩ := hval t
  have hu := IsLocalization.map_units (Localization.AtPrime P) t
  have hkt0 : kt ≠ 0 := by
    rintro rfl
    rw [hkt, map_zero] at hu
    exact not_isUnit_zero hu
  refine ⟨kx / kt, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hkt, hkx, ← map_mul, div_mul_cancel₀ _ hkt0]

/-- A `K`-algebra spanned by idempotents over a separably closed field `K` is w-strictly local:
all its primes are maximal and all its local rings are copies of `K`. -/
theorem IsWStrictlyLocalRing.of_forall_mem_span_isIdempotentElem [IsSepClosed K] {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (hR : ∀ x : R, x ∈ Submodule.span K E) :
    IsWStrictlyLocalRing R := by
  have hmax (p : PrimeSpectrum R) : p.asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal_of_forall_mem_span_isIdempotentElem hE hR p.asIdeal
  have hcl (p : PrimeSpectrum R) : IsClosed ({p} : Set (PrimeSpectrum R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr (hmax p)
  have hspec {p q : PrimeSpectrum R} (h : p ⤳ q) : p = q :=
    PrimeSpectrum.ext ((hmax p).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((PrimeSpectrum.le_iff_specializes p q).mpr h))
  have : IsStrictlyHenselianLocalRing K :=
    ⟨IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue K)
      ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩)⟩
  refine
    { wLocalSpace_primeSepectrum :=
        { eq_of_specializes := fun _ _ hxc hxc' ↦ (hspec hxc).symm.trans (hspec hxc')
          isClosed_closedPoints := by
            convert isClosed_univ
            exact Set.eq_univ_of_forall fun p ↦ mem_closedPoints_iff.mpr (hcl p) }
      isStrictlyHenselianLocalRing_localization := fun m _ ↦ .of_ringEquiv
        (RingEquiv.ofBijective _
          (bijective_algebraMap_localization_of_forall_mem_span_isIdempotentElem hE hR m)) }

/-- A `K`-algebra spanned by idempotents over a separably closed field `K`, whose space of
connected components is extremally disconnected, is w-contractible. -/
theorem IsWContractibleRing.of_forall_mem_span_isIdempotentElem [IsSepClosed K] {E : Set R}
    (hE : ∀ e ∈ E, IsIdempotentElem e) (hR : ∀ x : R, x ∈ Submodule.span K E)
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))] : IsWContractibleRing R :=
  have := IsWStrictlyLocalRing.of_forall_mem_span_isIdempotentElem hE hR
  { extremallyDisconnected_connectedComponents := inferInstance }

end Span

section ConnectedComponents

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` of compact spaces induces a bijection on spaces of connected
components if any two points of `X` in different components are separated by the preimage of a
clopen subset of `Y`, and every nonempty clopen subset of `Y` meets the image of `f`
(the latter requires `π₀(Y)` to be Hausdorff). -/
theorem Continuous.bijective_connectedComponentsMap [CompactSpace X] [CompactSpace Y]
    [T2Space (ConnectedComponents Y)] {f : X → Y} (hf : Continuous f)
    (hsep : ∀ x₁ x₂ : X, ConnectedComponents.mk x₁ ≠ ConnectedComponents.mk x₂ →
      ∃ U : Set Y, IsClopen U ∧ f x₁ ∈ U ∧ f x₂ ∉ U)
    (hmeet : ∀ U : Set Y, IsClopen U → U.Nonempty → ∃ x, f x ∈ U) :
    Function.Bijective hf.connectedComponentsMap := by
  refine ⟨fun a b hab ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨x₁, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨x₂, rfl⟩ := ConnectedComponents.surjective_coe b
    by_contra hne
    obtain ⟨U, hU, h₁, h₂⟩ := hsep x₁ x₂ hne
    rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
      ConnectedComponents.coe_eq_coe'] at hab
    have h : f x₂ ∈ connectedComponent (f x₁) := by
      rw [← connectedComponent_eq hab]
      exact mem_connectedComponent
    exact h₂ (hU.connectedComponent_subset h₁ h)
  · by_contra hc
    have hcl : IsClosed (Set.range hf.connectedComponentsMap) :=
      (isCompact_range hf.connectedComponentsMap_continuous).isClosed
    obtain ⟨V, hV, hcV, hVsub⟩ := exists_isClopen_mem_of_isOpen hcl.isOpen_compl
      (fun h ↦ hc (by simpa using h))
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨x, hx⟩ := hmeet _ (hV.preimage ConnectedComponents.continuous_coe) ⟨y, hcV⟩
    exact hVsub hx ⟨ConnectedComponents.mk x, rfl⟩

/-- Under the hypotheses of `Continuous.bijective_connectedComponentsMap`, `f` induces a
homeomorphism on spaces of connected components. -/
theorem Continuous.isHomeomorph_connectedComponentsMap [CompactSpace X] [CompactSpace Y]
    [T2Space (ConnectedComponents Y)] {f : X → Y} (hf : Continuous f)
    (hsep : ∀ x₁ x₂ : X, ConnectedComponents.mk x₁ ≠ ConnectedComponents.mk x₂ →
      ∃ U : Set Y, IsClopen U ∧ f x₁ ∈ U ∧ f x₂ ∉ U)
    (hmeet : ∀ U : Set Y, IsClopen U → U.Nonempty → ∃ x, f x ∈ U) :
    IsHomeomorph hf.connectedComponentsMap :=
  isHomeomorph_iff_continuous_bijective.mpr
    ⟨hf.connectedComponentsMap_continuous, hf.bijective_connectedComponentsMap hsep hmeet⟩

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Two points of `Spec T` in different connected components are separated by an idempotent. -/
theorem PrimeSpectrum.exists_isIdempotentElem_of_connectedComponents_mk_ne
    {p₁ p₂ : PrimeSpectrum T} (h : ConnectedComponents.mk p₁ ≠ ConnectedComponents.mk p₂) :
    ∃ c : T, IsIdempotentElem c ∧ c ∉ p₁.asIdeal ∧ c ∈ p₂.asIdeal := by
  obtain ⟨V, hV, h₁, h₂⟩ := exists_isClopen_mem_of_isOpen
    (isClosed_singleton (x := ConnectedComponents.mk p₂)).isOpen_compl h
  obtain ⟨c, hc, hcV⟩ := PrimeSpectrum.isClopen_iff.mp
    (hV.preimage ConnectedComponents.continuous_coe)
  refine ⟨c, hc, ?_, ?_⟩
  · have : p₁ ∈ ConnectedComponents.mk ⁻¹' V := h₁
    rwa [hcV, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at this
  · have : p₂ ∉ ConnectedComponents.mk ⁻¹' V := fun h ↦ h₂ h rfl
    rwa [hcV, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_not] at this

/-- A ring map `φ : S →+* T` induces a homeomorphism `π₀(Spec T) ≃ π₀(Spec S)` if any two
points of `Spec T` in different components are separated by the image of an idempotent of `S`,
and `φ` is injective on idempotents. -/
theorem PrimeSpectrum.isHomeomorph_connectedComponentsMap_comap (φ : S →+* T)
    (hsep : ∀ p₁ p₂ : PrimeSpectrum T, ConnectedComponents.mk p₁ ≠ ConnectedComponents.mk p₂ →
      ∃ e : S, IsIdempotentElem e ∧ φ e ∉ p₁.asIdeal ∧ φ e ∈ p₂.asIdeal)
    (hinj : ∀ e : S, IsIdempotentElem e → φ e = 0 → e = 0) :
    IsHomeomorph (PrimeSpectrum.continuous_comap φ).connectedComponentsMap := by
  refine (PrimeSpectrum.continuous_comap φ).isHomeomorph_connectedComponentsMap
    (fun p₁ p₂ h ↦ ?_) (fun U hU hne ↦ ?_)
  · obtain ⟨e, he, h₁, h₂⟩ := hsep p₁ p₂ h
    exact ⟨basicOpen e, PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩, h₁, not_not.mpr h₂⟩
  · obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hU
    have hφe : ¬ IsNilpotent (φ e) := by
      intro hn
      have h0 := hinj e he ((he.map φ).eq_zero_of_isNilpotent hn)
      obtain ⟨p, hp⟩ := hne
      simp [h0] at hp
    have : basicOpen (φ e) ≠ ⊥ := by
      rwa [Ne, PrimeSpectrum.basicOpen_eq_bot_iff]
    obtain ⟨q, hq⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp this
    exact ⟨q, hq⟩

end ConnectedComponents
