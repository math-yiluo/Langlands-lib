/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.RelativeComponentConstructible
public import WeilConjectures.RingTheory.DiscreteValuationRing.Dominating
public import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.RelativeComponentFlatApprox
public import WeilConjectures.Mathlib.Topology.Connected.Basic

/-!
# The relative connected component of a section is stable under generalization

Let `B` be a flat, finitely presented `A`-algebra whose fibres are geometrically reduced, and
`s : B →ₐ[A] A` a section. The relative connected component of `s` (the primes `q` of `B` lying in
the connected component of `s⁻¹ (q ∩ A)` in their fibre) is stable under generalization
(Stacks `055Q`).

The proof follows Stacks. Over a discrete valuation ring, an idempotent of the generic fibre of a
flat algebra with reduced special fibre extends to the algebra (Stacks `055J`,
`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`), so two sections meeting the
same connected component of the special fibre meet the same connected component of the generic
fibre. Over a noetherian base, a specialisation is traced by a discrete valuation ring
(`Ideal.exists_isDiscreteValuationRing_of_lt`) and the relative component is compatible with base
change (Stacks `055M`). The general case reduces to the noetherian one by noetherian approximation,
flatness descending at the finitely many points needed to cover the relative component of a fibre
(Stacks `00R6`).

## Main statements

- `PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing`: the discrete valuation ring
  case.
- `PrimeSpectrum.mem_relativeComponent_of_le_of_isNoetherianRing`: the noetherian case.
- `PrimeSpectrum.stableUnderGeneralization_relativeComponent`: the general case (Stacks `055Q`).

## References

- Stacks Project, Tags `055J`, `055Q`
-/

@[expose] public section

universe u

open TensorProduct Topology IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace PrimeSpectrum

/-- **The relative component over a discrete valuation ring** (Stacks `055J`). Let `R` be a
discrete valuation ring, `C` a finite type `R`-algebra with reduced special fibre, and `σ, τ` two
sections of `C`. Assume that `C` is flat over `R` at the points of the relative component of `σ`
in the special fibre. If the special point of `τ` lies in the relative component of `σ`, then so
does its generic point.

Let `Z` be the connected component of the special point of `σ` in the special fibre; it is closed
in `Spec C`. Inverting the elements lying in no prime of `Z` gives a flat `R`-algebra `D` with
reduced special fibre. If the generic points of `σ` and `τ` lay in different connected components
of the noetherian generic fibre, an idempotent of `D[1/ϖ]` would separate them. It comes from an
idempotent of `D` (`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`), which
would separate the special points of `σ` and `τ` in the connected set `Z`. -/
theorem mem_relativeComponent_of_isDiscreteValuationRing {R C : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
    (σ τ : C →ₐ[R] R) (hred : IsReduced (ResidueField R ⊗[R] C))
    (hflat : ∀ q ∈ relativeComponent σ, comap (algebraMap R C) q = closedPoint R →
      Module.Flat R (Localization.AtPrime q.asIdeal))
    (hτ : comap (τ : C →+* R) (closedPoint R) ∈ relativeComponent σ) :
    comap (τ : C →+* R) ⟨⊥, Ideal.isPrime_bot⟩ ∈ relativeComponent σ := by
  classical
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hsec (φ : C →ₐ[R] R) (p : PrimeSpectrum R) :
      comap (algebraMap R C) (comap (φ : C →+* R) p) = p := by
    rw [← comap_comp_apply, φ.comp_algebraMap]
    simp
  simp only [relativeComponent, Set.mem_ofPred_eq, hsec] at hτ ⊢
  set F := comap (algebraMap R C) ⁻¹' {closedPoint R}
  set Z := connectedComponentIn F (comap (σ : C →+* R) (closedPoint R))
  have hZF : Z ⊆ F := connectedComponentIn_subset _ _
  have hZ : IsClosed Z := ((isClosed_singleton_iff_isMaximal _).2
    (inferInstanceAs (maximalIdeal R).IsMaximal)).preimage (continuous_comap _)
    |>.isClosed_connectedComponentIn _
  have hσZ : comap (σ : C →+* R) (closedPoint R) ∈ Z := mem_connectedComponentIn (hsec σ _)
  -- the localization `D` of `C` at the elements avoiding `Z`
  let T : Submonoid C := ⨅ q ∈ Z, q.asIdeal.primeCompl
  have hT (c : C) : c ∈ T ↔ ∀ q ∈ Z, c ∉ q.asIdeal := by
    simp [T, Submonoid.mem_iInf, Ideal.primeCompl]
  let D := Localization T
  have hDflat : Module.Flat R D := by
    refine Module.Flat.localization_of_forall_mem_isClosed hZ (fun q hq ↦ hflat q ?_ (hZF hq)) T
      fun c hc ↦ (hT c).2 hc
    have hq' : comap (algebraMap R C) q = closedPoint R := hZF hq
    rw [relativeComponent, Set.mem_ofPred_eq, hq']
    exact hq
  have hDred : IsReduced (D ⧸ Ideal.span {algebraMap R D ϖ}) := by
    let eSp : ResidueField R ⊗[R] C ≃ₐ[R] C ⧸ (maximalIdeal R).map (algebraMap R C) :=
      (Algebra.TensorProduct.comm _ _ _).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal R)).symm.restrictScalars
          _)
    have : IsReduced (C ⧸ (maximalIdeal R).map (algebraMap R C)) :=
      isReduced_of_injective eSp.symm.toRingHom eSp.symm.injective
    have := isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (C ⧸ (maximalIdeal R).map (algebraMap R C)) T)
      (D ⧸ ((maximalIdeal R).map (algebraMap R C)).map (algebraMap C D)) this
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.map_span, Set.image_singleton] at this
  -- the extensions of the sections to `D` and to `D[1/ϖ]`
  let E := Localization.Away (algebraMap R D ϖ)
  let K := FractionRing R
  have hext (φ : C →ₐ[R] R) (hφ : comap (φ : C →+* R) (closedPoint R) ∈ Z) :
      ∃ (φD : D →+* R) (φE : E →+* K), φD.comp (algebraMap C D) = φ ∧
        φE.comp (algebraMap D E) = (algebraMap R K).comp φD := by
    have hu (y : T) : IsUnit (φ y) := notMem_maximalIdeal.1 ((hT _).1 y.2 _ hφ)
    let φD : D →+* R := IsLocalization.lift hu
    have hφD : φD.comp (algebraMap C D) = φ := IsLocalization.lift_comp hu
    have hϖ' : IsUnit (((algebraMap R K).comp φD) (algebraMap R D ϖ)) := by
      rw [IsScalarTower.algebraMap_apply R C D, RingHom.comp_apply, ← RingHom.comp_apply φD,
        hφD, AlgHom.coe_toRingHom, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero)
    exact ⟨φD, IsLocalization.Away.lift _ hϖ', hφD, IsLocalization.Away.lift_comp _ hϖ'⟩
  obtain ⟨σD, σE, hσD, hσE⟩ := hext σ hσZ
  obtain ⟨τD, τE, hτD, hτE⟩ := hext τ hτ
  -- `D` embeds in `D[1/ϖ]`, since `ϖ` is regular on the flat `R`-module `D`
  have hinj : Function.Injective (algebraMap D E) := by
    refine IsLocalization.injective E (M := Submonoid.powers (algebraMap R D ϖ))
      (Submonoid.powers_le.2 (mem_nonZeroDivisors_iff_right.2 fun z hz ↦ ?_))
    refine (isSMulRegular_algebraMap_iff D).2 (Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)) ?_
    simpa [smul_eq_mul, mul_comm] using hz
  -- `Spec D[1/ϖ]` maps to the generic fibre
  set ηR : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  set Fη := comap (algebraMap R C) ⁻¹' {ηR}
  let ι : C →+* E := (algebraMap D E).comp (algebraMap C D)
  have hι : ι.comp (algebraMap R C) = algebraMap R E := by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hιF (P : PrimeSpectrum E) : comap ι P ∈ Fη := by
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← comap_comp_apply, hι]
    ext1
    by_contra hne
    have hϖm : ϖ ∈ (comap (algebraMap R E) P).asIdeal := by
      rw [IsLocalRing.eq_maximalIdeal ((comap (algebraMap R E) P).isPrime.isMaximal hne)]
      exact hϖ.not_isUnit
    refine P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hϖm ?_)
    rw [IsScalarTower.algebraMap_apply R D E]
    exact IsLocalization.Away.algebraMap_isUnit _
  by_contra hW
  obtain ⟨e, he, hUe⟩ := isClopen_iff.1
    (TopologicalSpace.NoetherianSpace.isClopen_preimage_connectedComponentIn
      (continuous_comap ι) hιF (comap (σ : C →+* R) ηR))
  obtain ⟨b, rfl⟩ :=
    IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem hϖ hDred he
  have hb : IsIdempotentElem b := hinj ((map_mul _ b b).trans he)
  -- the generic points of the sections, seen in `Spec D[1/ϖ]`
  let ηK : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hpt (φ : C →ₐ[R] R) (φD : D →+* R) (φE : E →+* K)
      (hφD : φD.comp (algebraMap C D) = φ)
      (hφE : φE.comp (algebraMap D E) = (algebraMap R K).comp φD) :
      comap ι (comap φE ηK) = comap (φ : C →+* R) ηR := by
    have : φE.comp ι = (algebraMap R K).comp φ := by
      rw [← hφD, ← RingHom.comp_assoc, hφE, RingHom.comp_assoc]
    rw [← comap_comp_apply, this, comap_comp_apply]
    congr 1
    ext1
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  have hσb : σD b = 1 := by
    have hmem : comap σE ηK ∈ (basicOpen (algebraMap D E b) : Set (PrimeSpectrum E)) := by
      rw [← hUe, Set.mem_preimage, hpt σ σD σE hσD hσE]
      exact mem_connectedComponentIn (hsec σ ηR)
    rw [SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap, ← RingHom.comp_apply,
      hσE] at hmem
    refine (IsIdempotentElem.iff_eq_zero_or_one.1 (hb.map σD)).resolve_left fun h ↦ hmem ?_
    rw [RingHom.comp_apply, h, map_zero]
    exact zero_mem _
  have hτb : τD b = 0 := by
    have hmem : comap τE ηK ∉ (basicOpen (algebraMap D E b) : Set (PrimeSpectrum E)) := by
      rw [← hUe, Set.mem_preimage, hpt τ τD τE hτD hτE]
      exact hW
    rw [SetLike.mem_coe, mem_basicOpen, not_not, comap_asIdeal, Ideal.mem_comap,
      ← RingHom.comp_apply, hτE] at hmem
    exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 hmem
  -- the clopen subset `D(b)` of `Spec D` separates the special points of `σ` and `τ` in `Z`
  have hY : IsPreconnected (comap (algebraMap C D) ⁻¹' Z) := by
    rw [← (localization_comap_isInducing D T).isPreconnected_image,
      Set.image_preimage_eq_of_subset]
    · exact isPreconnected_connectedComponentIn
    · rw [localization_comap_range D T]
      exact fun q hq ↦ Set.disjoint_left.2 fun c hc hcq ↦ (hT c).1 hc q hq hcq
  have hY' (φ : C →ₐ[R] R) (φD : D →+* R) (hφD : φD.comp (algebraMap C D) = φ)
      (hφ : comap (φ : C →+* R) (closedPoint R) ∈ Z) :
      comap φD (closedPoint R) ∈ comap (algebraMap C D) ⁻¹' Z := by
    rw [Set.mem_preimage, ← comap_comp_apply, hφD]
    exact hφ
  have hsub := hY.subset_isClopen (isClopen_iff.2 ⟨b, hb, rfl⟩)
    ⟨_, hY' σ σD hσD hσZ, ?_⟩ (hY' τ τD hτD hτ)
  · rw [SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap, hτb] at hsub
    exact hsub (zero_mem _)
  · rw [SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap, hσb]
    exact fun h ↦ (closedPoint R).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

/-- **The relative component is stable under generalization over a noetherian base.** Let `A` be
noetherian, `B` a finite type `A`-algebra with a section `s`, and `x' ≤ x` primes of `B` with `x`
in the relative component of `s`, lying over `y`. Assume that the fibre over `y` is geometrically
reduced and that `B` is flat over `A` at the points of the relative component lying over `y`.
Then `x'` lies in the relative component of `s`.

A discrete valuation ring `R` traces the specialisation `x' ⤳ x`, giving a second section `τ` of
`R ⊗[A] B` over `R`, and we conclude by
`PrimeSpectrum.mem_relativeComponent_of_isDiscreteValuationRing` and the compatibility of the
relative component with base change. -/
theorem mem_relativeComponent_of_le_of_isNoetherianRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] (s : B →ₐ[A] A)
    {x x' : PrimeSpectrum B} (hle : x' ≤ x) (hx : x ∈ relativeComponent s)
    (hred : ∀ (L : Type u) [Field L] [Algebra A L],
      RingHom.ker (algebraMap A L) = (comap (algebraMap A B) x).asIdeal → IsReduced (L ⊗[A] B))
    (hflat : ∀ q ∈ relativeComponent s, comap (algebraMap A B) q = comap (algebraMap A B) x →
      Module.Flat A (Localization.AtPrime q.asIdeal)) :
    x' ∈ relativeComponent s := by
  classical
  rcases eq_or_ne x' x with rfl | hxx
  · exact hx
  have hlt : x'.asIdeal < x.asIdeal :=
    lt_of_le_of_ne hle fun h ↦ hxx (PrimeSpectrum.ext h)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  obtain ⟨R, _, _, _, φ, hker, hmax⟩ := Ideal.exists_isDiscreteValuationRing_of_lt hlt
  let : Algebra A R := (φ.comp (algebraMap A B)).toAlgebra
  let φA : B →ₐ[A] R := { φ with commutes' := fun _ ↦ rfl }
  let C := R ⊗[A] B
  let σ : C →ₐ[R] R := Algebra.TensorProduct.lift (Algebra.ofId R R)
    ((Algebra.ofId A R).comp s) fun _ _ ↦ Commute.all _ _
  let τ : C →ₐ[R] R := Algebra.TensorProduct.lift (Algebra.ofId R R) φA
    fun _ _ ↦ Commute.all _ _
  have hσ (b : B) : algebraMap A R (s b) = σ (algebraMap B C b) := by
    change _ = σ ((1 : R) ⊗ₜ[A] b)
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hrel := relativeComponent_eq_preimage_of_isPushout σ s hσ
  have hτφ (b : B) : τ (algebraMap B C b) = φ b := by
    change τ ((1 : R) ⊗ₜ[A] b) = φ b
    rw [Algebra.TensorProduct.lift_tmul]
    simp [φA]
  have hτB : (τ : C →+* R).comp (algebraMap B C) = φ := RingHom.ext hτφ
  have h₁ : comap (algebraMap B C) (comap (τ : C →+* R) (closedPoint R)) = x := by
    ext1
    rw [← comap_comp_apply, hτB]
    exact hmax
  have h₂ : comap (algebraMap B C) (comap (τ : C →+* R) ⟨⊥, Ideal.isPrime_bot⟩) = x' := by
    ext1
    rw [← comap_comp_apply, hτB]
    exact hker
  have hAR : comap (algebraMap A R) (closedPoint R) = comap (algebraMap A B) x := by
    ext1
    change Ideal.comap ((φ.comp (algebraMap A B))) (maximalIdeal R) = _
    rw [← Ideal.comap_comap, hmax]
    rfl
  have hCB (q : PrimeSpectrum C) : comap (algebraMap A B) (comap (algebraMap B C) q) =
      comap (algebraMap A R) (comap (algebraMap R C) q) := by
    rw [← comap_comp_apply, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have key := mem_relativeComponent_of_isDiscreteValuationRing σ τ ?_ ?_
    (by rw [hrel, Set.mem_preimage, h₁]; exact hx)
  · rwa [hrel, Set.mem_preimage, h₂] at key
  · -- the special fibre `κ ⊗[R] (R ⊗[A] B) = κ ⊗[A] B` is reduced
    let : Algebra A (ResidueField R) :=
      ((algebraMap R (ResidueField R)).comp (algebraMap A R)).toAlgebra
    have : IsScalarTower A R (ResidueField R) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have := hred (ResidueField R) (by
      rw [← congrArg PrimeSpectrum.asIdeal hAR]
      change RingHom.ker ((residue R).comp (algebraMap A R)) = _
      rw [← RingHom.comap_ker, IsLocalRing.ker_residue]
      rfl)
    exact isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange A R R (ResidueField R) B).toRingHom
      (Algebra.TensorProduct.cancelBaseChange A R R (ResidueField R) B).injective
  · intro q hq hqc
    have hq₁ : comap (algebraMap B C) q ∈ relativeComponent s := by
      rw [hrel] at hq
      exact hq
    have := hflat _ hq₁ (by rw [hCB, hqc, hAR])
    exact Module.Flat.localization_of_isPushout (R := A) (S := B) q.asIdeal this

/-- **Geometrically reduced fibres descend along base change.** Let `B = A ⊗[A₁] B₁` and let `y` be
a prime of `A`. If `L ⊗[A] B` is reduced for every field `L` over `A`, then `L ⊗[A₁] B₁` is reduced
for every field `L` over `A₁` whose kernel is `y ∩ A₁`: a field `Ω` containing both `L` and `κ(y)`
gives an embedding of `L ⊗[A₁] B₁` into `Ω ⊗[A₁] B₁ = Ω ⊗[A] B`. -/
theorem isReduced_tensorProduct_of_isPushout {A₁ A B₁ B : Type u} [CommRing A₁] [CommRing A]
    [CommRing B₁] [CommRing B] [Algebra A₁ A] [Algebra A₁ B₁] [Algebra A B] [Algebra B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B] [Algebra.IsPushout A₁ A B₁ B]
    (hred : ∀ (L : Type u) [Field L] [Algebra A L], IsReduced (L ⊗[A] B)) (y : PrimeSpectrum A)
    (L : Type u) [Field L] [Algebra A₁ L]
    (hL : RingHom.ker (algebraMap A₁ L) = (comap (algebraMap A₁ A) y).asIdeal) :
    IsReduced (L ⊗[A₁] B₁) := by
  classical
  obtain ⟨P, hP, -⟩ := Algebra.exists_isPrime_comap_includeLeft_eq (A := A₁) (B := A) (K := L)
    (Field.toIsField L) y.asIdeal hL
  let Ω := P.ResidueField
  have := hred Ω
  let e₁ : Ω ⊗[A₁] B₁ ≃+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₁ A Ω Ω B₁).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[A] Ω)
        (Algebra.IsPushout.equiv A₁ A B₁ B)).toRingEquiv
  let e₂ : Ω ⊗[L] (L ⊗[A₁] B₁) ≃+* Ω ⊗[A₁] B₁ :=
    (Algebra.TensorProduct.cancelBaseChange A₁ L Ω Ω B₁).toRingEquiv
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : L ⊗[A₁] B₁ →ₐ[L] Ω ⊗[L] (L ⊗[A₁] B₁)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap L Ω).injective
  exact isReduced_of_injective
    ((e₁.toRingHom.comp e₂.toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom)
    ((e₁.injective.comp e₂.injective).comp hinj)

/-- **The relative component of a section is stable under generalization** (Stacks `055Q`). Let
`B` be a flat, finitely presented `A`-algebra with geometrically reduced fibres, and `s` a section
of `B`. Then the relative component of `s` is stable under generalization. -/
theorem stableUnderGeneralization_relativeComponent {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [Algebra.FinitePresentation A B]
    (hred : ∀ (L : Type u) [Field L] [Algebra A L], IsReduced (L ⊗[A] B)) (s : B →ₐ[A] A) :
    StableUnderGeneralization (relativeComponent s) := by
  intro x x' hspec hx
  set y := comap (algebraMap A B) x
  obtain ⟨A₁, B₁, _, _, _, _, _, _, _, _, _, _, _, s₁, hs₁, hflat⟩ :=
    exists_isPushout_forall_flat A B s y
  have hy (q : PrimeSpectrum B) : comap (algebraMap A₁ B₁) (comap (algebraMap B₁ B) q) =
      comap (algebraMap A₁ A) (comap (algebraMap A B) q) := by
    rw [← comap_comp_apply, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hrel := relativeComponent_eq_preimage_of_isPushout s s₁ hs₁
  have hx₁ : comap (algebraMap B₁ B) x ∈ relativeComponent s₁ := by
    rw [hrel] at hx
    exact hx
  have hle : comap (algebraMap B₁ B) x' ≤ comap (algebraMap B₁ B) x := by
    rw [← asIdeal_le_asIdeal]
    exact Ideal.comap_mono ((le_iff_specializes x' x).mpr hspec)
  have key := mem_relativeComponent_of_le_of_isNoetherianRing s₁ hle hx₁
    (fun L _ _ hL ↦ isReduced_tensorProduct_of_isPushout hred y L (hL.trans (by rw [hy])))
    (fun q _ hqx ↦ hflat q (hqx.trans (hy x)))
  rw [hrel]
  exact key

end PrimeSpectrum
