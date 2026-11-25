/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.FiniteWStrictlyLocal
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Finite algebras over w-contractible rings

A module-finite, finitely presented algebra `B` over a w-contractible ring `A` is again
w-contractible.

By `IsWStrictlyLocalRing.of_finite`, `B` is w-strictly local, so it remains to show that the
space `π₀(Spec B)` of connected components is extremally disconnected. Identify `π₀` with the
spaces of closed points `E_B` and `E_A`. We show that `E_B ⟶ E_A` is a local homeomorphism,
so that extremal disconnectedness passes from `E_A` to `E_B`
(`IsLocalHomeomorph.extremallyDisconnected`).

The local homeomorphism property is where finite presentation enters. Constructible subsets
of `Spec A` meet `E_A` in clopen subsets. By Chevalley's theorem, for a clopen `Q ⊆ Spec B`,
the locus of points of `Spec A` over which `Q` has two distinct points is constructible: up to
the points of `Spec A` with non separably closed residue fields, it is the image of the
complement of the diagonal in `Spec (B ⊗_A B)` restricted to `Q × Q`. At closed points of
`Spec A` the residue fields are separably closed (the local rings are strictly henselian), so
that a point of `Spec (B ⊗_A B)` over a pair `(q, q)` lies on the diagonal, the residue field
of `q` being purely inseparable.

## Main results

- `IsLocalHomeomorph.extremallyDisconnected`
- `IsWContractibleRing.of_finite`
-/

@[expose] public section

universe u

open Topology TensorProduct

/-- A space admitting a local homeomorphism to an extremally disconnected space is extremally
disconnected. -/
theorem IsLocalHomeomorph.extremallyDisconnected {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ExtremallyDisconnected Y] {f : X → Y} (hf : IsLocalHomeomorph f) :
    ExtremallyDisconnected X := by
  refine ⟨fun U hU ↦ isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_⟩
  obtain ⟨e, hxe, rfl⟩ := hf x
  have hxW : x ∈ closure (e.source ∩ U) := e.open_source.inter_closure ⟨hxe, hx⟩
  have hopen : IsOpen (e '' (e.source ∩ U)) :=
    e.isOpen_image_of_subset_source (e.open_source.inter hU) Set.inter_subset_left
  refine ⟨e.source ∩ e ⁻¹' closure (e '' (e.source ∩ U)), ?_,
    e.isOpen_inter_preimage (ExtremallyDisconnected.open_closure _ hopen), hxe, ?_⟩
  · rintro z ⟨hzW, hz⟩
    have hcont : ContinuousWithinAt e.symm (e '' (e.source ∩ U)) (e z) :=
      (e.continuousOn_symm.continuousWithinAt (e.map_source hzW)).mono (by
        rintro _ ⟨y, hy, rfl⟩
        exact e.map_source hy.1)
    have := hcont.mem_closure_image hz
    rw [e.left_inv hzW] at this
    refine closure_mono ?_ this
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [e.left_inv hy.1]
    exact hy.2
  · exact ((e.continuousOn.continuousWithinAt hxe).mono Set.inter_subset_left).mem_closure_image
      hxW

/-- In a compact space, a constructible set meets a closed Hausdorff subspace in a clopen
subset. -/
theorem Topology.IsConstructible.isClopen_preimage_val {X : Type*} [TopologicalSpace X]
    [CompactSpace X]
    {Z : Set X} (hZ : IsClosed Z) [T2Space Z] {s : Set X} (hs : IsConstructible s) :
    IsClopen (((↑) : Z → X) ⁻¹' s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    refine ⟨IsCompact.isClosed ?_, hUopen.preimage continuous_subtype_val⟩
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    exact hUcomp.isCompact.inter_left hZ
  | union s _ t _ hs ht => exact hs.union ht
  | compl s _ hs => exact hs.compl

namespace FiniteWContractible

open Algebra.TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The left inclusion `B → B ⊗_A B` as a ring homomorphism. -/
noncomputable abbrev inl : B →+* B ⊗[A] B := (includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom

/-- The right inclusion `B → B ⊗_A B` as a ring homomorphism. -/
noncomputable abbrev inr : B →+* B ⊗[A] B := (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom

lemma tmul_one_sub_one_tmul_algebraMap (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : B) - 1 ⊗ₜ algebraMap A B a = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul, sub_self]

/-- If an ideal of `B ⊗_A B` contains `b ⊗ 1 - 1 ⊗ b` for a generating set of `B`, then its
preimages under the two inclusions agree. -/
lemma comap_inl_eq_comap_inr (r : Ideal (B ⊗[A] B)) {s : Set B}
    (hs : Algebra.adjoin A s = ⊤) (h : ∀ b ∈ s, b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ r) :
    r.comap (inl (A := A)) = r.comap (inr (A := A)) := by
  have hall : ∀ b : B, b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ r := by
    intro b
    have hb : b ∈ Algebra.adjoin A s := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact h x hx
    | algebraMap a => rw [tmul_one_sub_one_tmul_algebraMap]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (x + y) ⊗ₜ[A] (1 : B) - 1 ⊗ₜ (x + y) =
          (x ⊗ₜ[A] (1 : B) - 1 ⊗ₜ x) + (y ⊗ₜ[A] (1 : B) - 1 ⊗ₜ y) := by
        rw [add_tmul, tmul_add]
        abel
      rw [this]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      have : (x * y) ⊗ₜ[A] (1 : B) - 1 ⊗ₜ (x * y) =
          (x ⊗ₜ[A] (1 : B)) * (y ⊗ₜ[A] (1 : B) - 1 ⊗ₜ y) +
            ((1 : B) ⊗ₜ[A] y) * (x ⊗ₜ[A] (1 : B) - 1 ⊗ₜ x) := by
        simp only [mul_sub, tmul_mul_tmul, mul_one, one_mul, mul_comm y x]
        abel
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
  ext b
  simp only [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, includeLeft_apply,
    includeRight_apply]
  constructor
  · intro hb
    simpa using sub_mem hb (hall b)
  · intro hb
    simpa using add_mem (hall b) hb

lemma algebraMap_eq_inl_comp : algebraMap A (B ⊗[A] B) = (inl (A := A)).comp (algebraMap A B) := by
  ext a
  simp [Algebra.TensorProduct.algebraMap_apply]

lemma algebraMap_eq_inr_comp : algebraMap A (B ⊗[A] B) = (inr (A := A)).comp (algebraMap A B) := by
  ext a
  simp [Algebra.algebraMap_eq_smul_one]

variable [Algebra.IsIntegral A B]

/-- Two maximal ideals of `B` over the same ideal of `A` are the two images of a prime of
`B ⊗_A B`. -/
lemma exists_isPrime_comap_eq (q₁ q₂ : Ideal B) [q₁.IsMaximal] [q₂.IsMaximal]
    (h : q₁.comap (algebraMap A B) = q₂.comap (algebraMap A B)) :
    ∃ r : Ideal (B ⊗[A] B), r.IsPrime ∧ r.comap (inl (A := A)) = q₁ ∧
      r.comap (inr (A := A)) = q₂ := by
  set e := q₁.comap (algebraMap A B)
  have : e.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal q₁
  have : q₁.LiesOver e := ⟨rfl⟩
  have : q₂.LiesOver e := ⟨h⟩
  let := Ideal.Quotient.field e
  let σ₁ : B ⧸ q₁ →ₐ[A ⧸ e] AlgebraicClosure (A ⧸ e) := IsAlgClosed.lift
  let σ₂ : B ⧸ q₂ →ₐ[A ⧸ e] AlgebraicClosure (A ⧸ e) := IsAlgClosed.lift
  let f₁ : B →ₐ[A] AlgebraicClosure (A ⧸ e) :=
    (σ₁.restrictScalars A).comp (Ideal.Quotient.mkₐ A q₁)
  let f₂ : B →ₐ[A] AlgebraicClosure (A ⧸ e) :=
    (σ₂.restrictScalars A).comp (Ideal.Quotient.mkₐ A q₂)
  let ψ : B ⊗[A] B →ₐ[A] AlgebraicClosure (A ⧸ e) :=
    Algebra.TensorProduct.lift f₁ f₂ fun _ _ ↦ Commute.all _ _
  have hprime : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime _
  refine ⟨RingHom.ker ψ.toRingHom, hprime, ?_, ?_⟩
  · have hle : q₁ ≤ (RingHom.ker ψ.toRingHom).comap (inl (A := A)) := fun b hb ↦ by
      simp [RingHom.mem_ker, ψ, f₁, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) hle).symm
  · have hle : q₂ ≤ (RingHom.ker ψ.toRingHom).comap (inr (A := A)) := fun b hb ↦ by
      simp [RingHom.mem_ker, ψ, f₂, Ideal.Quotient.eq_zero_iff_mem.2 hb]
    exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) hle).symm

/-- A prime of `B ⊗_A B` over a pair `(q, q)`, where `q` lies over a point of `Spec A` with
strictly henselian local ring, contains every `b ⊗ 1 - 1 ⊗ b`: the residue field of `q` is
purely inseparable over the separably closed residue field of `A`. -/
lemma tmul_one_sub_one_tmul_mem (r : Ideal (B ⊗[A] B)) [r.IsPrime] (q : Ideal B) [q.IsMaximal]
    (hl : r.comap (inl (A := A)) = q) (hr : r.comap (inr (A := A)) = q)
    [IsStrictlyHenselianLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))] (b : B) :
    b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ r := by
  set e := q.comap (algebraMap A B)
  have : e.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal q
  have : q.LiesOver e := ⟨rfl⟩
  let := Ideal.Quotient.field e
  have : IsSepClosed (A ⧸ e) :=
    IsSepClosed.of_ringEquiv (k := IsLocalRing.ResidueField (Localization.AtPrime e))
    (IsLocalization.AtPrime.equivQuotMaximalIdeal e (Localization.AtPrime e)).symm.toRingEquiv
  have hrl : r.LiesOver e := ⟨by
    rw [Ideal.under_def, algebraMap_eq_inl_comp, ← Ideal.comap_comap, hl]⟩
  set p := ringExpChar (A ⧸ e)
  obtain ⟨n, a', ha'⟩ := IsPurelyInseparable.pow_mem (A ⧸ e) p (Ideal.Quotient.mk q b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hq : b ^ p ^ n - algebraMap A B a ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← ha',
      Ideal.Quotient.algebraMap_mk_of_liesOver, sub_self]
  have hql : inl (A := A) (b ^ p ^ n - algebraMap A B a) ∈ r := by
    rw [← Ideal.mem_comap, hl]; exact hq
  have hqr : inr (A := A) (b ^ p ^ n - algebraMap A B a) ∈ r := by
    rw [← Ideal.mem_comap, hr]; exact hq
  have hinj : Function.Injective (algebraMap (A ⧸ e) ((B ⊗[A] B) ⧸ r)) :=
    FaithfulSMul.algebraMap_injective _ _
  have : ExpChar ((B ⊗[A] B) ⧸ r) p := expChar_of_injective_algebraMap hinj p
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine pow_eq_zero_iff (n := p ^ n) (pow_ne_zero _ (expChar_pos (A ⧸ e) p).ne') |>.1 ?_
  rw [map_sub, sub_pow_expChar_pow, ← map_pow, ← map_pow, sub_eq_zero, Ideal.Quotient.eq]
  have h1 : (b ^ p ^ n) ⊗ₜ[A] (1 : B) - 1 ⊗ₜ (b ^ p ^ n) =
      inl (A := A) (b ^ p ^ n - algebraMap A B a) -
        inr (A := A) (b ^ p ^ n - algebraMap A B a) := by
    simp only [map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, includeLeft_apply,
      includeRight_apply]
    rw [sub_eq_zero.1 (tmul_one_sub_one_tmul_algebraMap (B := B) a)]
    abel
  simp only [tmul_pow, one_pow]
  rw [h1]
  exact sub_mem hql hqr

end FiniteWContractible

section Main

open PrimeSpectrum FiniteWContractible

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A module-finite and finitely presented algebra over a w-contractible ring is
w-contractible. -/
theorem IsWContractibleRing.of_finite [IsWContractibleRing A] [Module.Finite A B]
    [Algebra.FinitePresentation A B] : IsWContractibleRing B := by
  classical
  have hB : IsWStrictlyLocalRing B := .of_finite (A := A)
  refine { toIsWStrictlyLocalRing := hB, extremallyDisconnected_connectedComponents := ?_ }
  let φ := PrimeSpectrum.comap (algebraMap A B)
  have hφE : ∀ y : PrimeSpectrum B, y ∈ closedPoints (PrimeSpectrum B) ↔
      φ y ∈ closedPoints (PrimeSpectrum A) := fun y ↦ by
    simp only [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact ⟨fun _ ↦ Ideal.isMaximal_under_of_isIntegral_of_isMaximal y.asIdeal,
      fun h ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_under y.asIdeal h⟩
  let p : closedPoints (PrimeSpectrum B) → closedPoints (PrimeSpectrum A) :=
    fun y ↦ ⟨φ y.1, (hφE y.1).1 y.2⟩
  have hp : Continuous p :=
    ((PrimeSpectrum.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
    IsWContractibleRing.extremallyDisconnected_connectedComponents
  have : ExtremallyDisconnected (closedPoints (PrimeSpectrum A)) :=
    extremallyDisconnected_of_homeo WLocalSpace.closedPointsHomeomorph.symm
  suffices ExtremallyDisconnected (closedPoints (PrimeSpectrum B)) from
    extremallyDisconnected_of_homeo WLocalSpace.closedPointsHomeomorph
  refine IsLocalHomeomorph.extremallyDisconnected (f := p)
    (isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun x ↦ ?_)
  -- A clopen neighbourhood `U₀` of `x` containing no other point of the fibre of `x`.
  have hfin : (((↑) : closedPoints (PrimeSpectrum B) → PrimeSpectrum B) ⁻¹'
      (φ ⁻¹' {φ x.1})).Finite :=
    (Algebra.QuasiFinite.finite_comap_preimage_singleton (R := A) (S := B) (φ x.1)).preimage
      Subtype.val_injective.injOn
  have hO : IsOpen ((((↑) : closedPoints (PrimeSpectrum B) → PrimeSpectrum B) ⁻¹'
      (φ ⁻¹' {φ x.1})) \ {x})ᶜ :=
    ((hfin.subset Set.sdiff_subset).isClosed).isOpen_compl
  obtain ⟨U₀, hU₀, hxU₀, hU₀O⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1
    (hO.mem_nhds (fun h ↦ h.2 rfl))
  -- The corresponding clopen subset `Q` of `Spec B`.
  let h := (WLocalSpace.closedPointsHomeomorph (X := PrimeSpectrum B))
  let Q : Set (PrimeSpectrum B) := ConnectedComponents.mk ⁻¹' (h '' U₀)
  have hQ : IsClopen Q :=
    IsClopen.preimage (⟨h.isClosedMap _ hU₀.1, h.isOpenMap _ hU₀.2⟩ : IsClopen (h '' U₀))
      ConnectedComponents.continuous_coe
  have hQE : ∀ y : closedPoints (PrimeSpectrum B), y.1 ∈ Q ↔ y ∈ U₀ := fun y ↦
    h.injective.mem_set_image
  have hQc : IsConstructible Q := hQ.isClosed.isCompact.isConstructible hQ.isOpen
  -- The image of `Q`, and the locus where `Q` has two distinct points.
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  let D : Set (PrimeSpectrum (B ⊗[A] B)) :=
    (⋃ b ∈ s, (PrimeSpectrum.basicOpen (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b) : Set _)) ∩
      (PrimeSpectrum.comap (inl (A := A)) ⁻¹' Q ∩ PrimeSpectrum.comap (inr (A := A)) ⁻¹' Q)
  have hDc : IsConstructible D := by
    refine IsConstructible.inter (IsConstructible.biUnion s.finite_toSet fun b _ ↦
      isConstructible_basicOpen) (IsConstructible.inter ?_ ?_)
    · have h' := hQ.preimage (PrimeSpectrum.continuous_comap (inl (A := A)))
      exact h'.isClosed.isCompact.isConstructible h'.isOpen
    · have h' := hQ.preimage (PrimeSpectrum.continuous_comap (inr (A := A)))
      exact h'.isClosed.isCompact.isConstructible h'.isOpen
  have : Algebra.FinitePresentation A (B ⊗[A] B) := Algebra.FinitePresentation.trans A B _
  let S₁ := φ '' Q
  let S₂ := PrimeSpectrum.comap (algebraMap A (B ⊗[A] B)) '' D
  have hS₁ : IsConstructible S₁ :=
    isConstructible_comap_image (RingHom.finitePresentation_algebraMap.2 inferInstance) hQc
  have hS₂ : IsConstructible S₂ :=
    isConstructible_comap_image (RingHom.finitePresentation_algebraMap.2 inferInstance) hDc
  -- Characterization of `S₂` at closed points.
  have hφinl : ∀ r : PrimeSpectrum (B ⊗[A] B),
      φ (PrimeSpectrum.comap (inl (A := A)) r) =
        PrimeSpectrum.comap (algebraMap A (B ⊗[A] B)) r := fun r ↦ by
    rw [algebraMap_eq_inl_comp, PrimeSpectrum.comap_comp_apply]
  have hφinr : ∀ r : PrimeSpectrum (B ⊗[A] B),
      φ (PrimeSpectrum.comap (inr (A := A)) r) =
        PrimeSpectrum.comap (algebraMap A (B ⊗[A] B)) r := fun r ↦ by
    rw [algebraMap_eq_inr_comp, PrimeSpectrum.comap_comp_apply]
  have hchar : ∀ e' ∈ S₂, e' ∈ closedPoints (PrimeSpectrum A) → ∃ y₁ y₂ : PrimeSpectrum B,
      y₁ ∈ Q ∧ y₂ ∈ Q ∧ y₁ ≠ y₂ ∧ φ y₁ = e' ∧ φ y₂ = e' := by
    rintro _ ⟨r, ⟨hrs, hrl, hrr⟩, rfl⟩ he'
    refine ⟨_, _, hrl, hrr, fun heq ↦ ?_, hφinl r, hφinr r⟩
    obtain ⟨b, hb, hbr⟩ := Set.mem_iUnion₂.1 hrs
    rw [← hφinl r, ← hφE] at he'
    have hmax : (r.asIdeal.comap (inl (A := A))).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 (mem_closedPoints_iff.1 he')
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization (R := A)
      ((r.asIdeal.comap (inl (A := A))).comap (algebraMap A B))
    exact hbr (tmul_one_sub_one_tmul_mem r.asIdeal _ rfl
      (congrArg PrimeSpectrum.asIdeal heq.symm) b)
  have hchar' : ∀ y₁ y₂ : PrimeSpectrum B, y₁ ∈ Q → y₂ ∈ Q → y₁ ≠ y₂ → φ y₁ = φ y₂ →
      y₁ ∈ closedPoints (PrimeSpectrum B) → y₂ ∈ closedPoints (PrimeSpectrum B) →
      φ y₁ ∈ S₂ := by
    intro y₁ y₂ hy₁ hy₂ hne heq hc₁ hc₂
    have : y₁.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 (mem_closedPoints_iff.1 hc₁)
    have : y₂.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 (mem_closedPoints_iff.1 hc₂)
    obtain ⟨r, hr, hrl, hrr⟩ := exists_isPrime_comap_eq (A := A) y₁.asIdeal y₂.asIdeal
      (congrArg PrimeSpectrum.asIdeal heq)
    have hrl' : PrimeSpectrum.comap (inl (A := A)) ⟨r, hr⟩ = y₁ := PrimeSpectrum.ext hrl
    have hrr' : PrimeSpectrum.comap (inr (A := A)) ⟨r, hr⟩ = y₂ := PrimeSpectrum.ext hrr
    refine ⟨⟨r, hr⟩, ⟨?_, by rwa [Set.mem_preimage, hrl'], by rwa [Set.mem_preimage, hrr']⟩,
      by rw [← hφinl, hrl']⟩
    by_contra hall
    simp only [Set.mem_iUnion, not_exists] at hall
    apply hne
    have := comap_inl_eq_comap_inr r hs fun b hb ↦ by
      have h' := hall b hb
      rwa [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_not] at h'
    rw [hrl, hrr] at this
    exact PrimeSpectrum.ext this
  -- The clopen subset `C` of closed points of `Spec A`.
  let C : Set (closedPoints (PrimeSpectrum A)) := (↑) ⁻¹' S₁ ∩ ((↑) ⁻¹' S₂)ᶜ
  have hC : IsClopen C :=
    (hS₁.isClopen_preimage_val WLocalSpace.isClosed_closedPoints).inter
      (hS₂.isClopen_preimage_val WLocalSpace.isClosed_closedPoints).compl
  let U : Set (closedPoints (PrimeSpectrum B)) := U₀ ∩ p ⁻¹' C
  have hU : IsClopen U := hU₀.inter (hC.preimage hp)
  have hinj : Set.InjOn p U := by
    intro y₁ hy₁ y₂ hy₂ heq
    by_contra hne
    have hne' : y₁.1 ≠ y₂.1 := fun h ↦ hne (Subtype.ext h)
    exact hy₁.2.2 (hchar' y₁.1 y₂.1 ((hQE y₁).2 hy₁.1) ((hQE y₂).2 hy₂.1) hne'
      (congrArg Subtype.val heq) y₁.2 y₂.2)
  have hxC : p x ∈ C := by
    refine ⟨⟨x.1, (hQE x).2 hxU₀, rfl⟩, fun hS ↦ ?_⟩
    obtain ⟨y₁, y₂, hy₁, hy₂, hne, h₁, h₂⟩ := hchar _ hS (p x).2
    have hc₁ : y₁ ∈ closedPoints (PrimeSpectrum B) := (hφE y₁).2 (h₁ ▸ (p x).2)
    have hc₂ : y₂ ∈ closedPoints (PrimeSpectrum B) := (hφE y₂).2 (h₂ ▸ (p x).2)
    -- one of the two points differs from `x`
    have key : ∀ y : closedPoints (PrimeSpectrum B), y.1 ∈ Q → φ y.1 = φ x.1 → y = x := by
      intro y hyQ hyφ
      by_contra hyx
      exact hU₀O ((hQE y).1 hyQ) ⟨hyφ, hyx⟩
    have e₁ := key ⟨y₁, hc₁⟩ hy₁ h₁
    have e₂ := key ⟨y₂, hc₂⟩ hy₂ h₂
    exact hne (congrArg Subtype.val (e₁.trans e₂.symm))
  have hrange : Set.range (U.domRestrict p) = C := by
    ext e'
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy.2
    · intro he'
      obtain ⟨y, hyQ, hy⟩ := he'.1
      have hyc : y ∈ closedPoints (PrimeSpectrum B) := (hφE y).2 (hy ▸ e'.2)
      have hpy : p ⟨y, hyc⟩ = e' := Subtype.ext hy
      exact ⟨⟨⟨y, hyc⟩, (hQE ⟨y, hyc⟩).1 hyQ, by rw [Set.mem_preimage, hpy]; exact he'⟩, hpy⟩
  refine ⟨U, hU.isOpen.mem_nhds ⟨hxU₀, hxC⟩, ?_⟩
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU.isClosed.isCompact
  have hemb : IsClosedEmbedding (U.domRestrict p) :=
    (hp.comp continuous_subtype_val).isClosedEmbedding (Set.injOn_iff_injective.1 hinj)
  exact ⟨hemb.isEmbedding, hrange ▸ hC.isOpen⟩

end Main
