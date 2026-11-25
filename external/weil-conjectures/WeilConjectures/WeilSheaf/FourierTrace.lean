/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.FourierTransform.Classical
public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.FourierTraceAux
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.TraceFunctionTensor
public import WeilConjectures.ZetaSeries
import WeilConjectures.ZetaFunction.WeilObjectComparison

/-!
# The trace function of the Fourier–Deligne transform

Let `k₀` be a finite field with `q` elements, `ψ` an additive character of `k₀` with values in
`ℚ̄_ℓ` and `ι` a finite index type with `r` elements. The `𝔽_{qⁿ}`-rational points of the affine
space `𝔸^ι` are the vectors `ι → 𝔽_{qⁿ}` (`AlgebraicGeometry.AffineSpace.fieldPointsEquivPi`),
so the trace function `t_K` of a Weil complex `K` on `𝔸^ι` at level `n` is a function on
`𝔽_{qⁿ}^ι`. The *Fourier trace formula* says that the trace function of the Fourier–Deligne
transform `FT_ψ(K)` (`AlgebraicGeometry.affineSpaceFourierTransform`) is, up to the sign `(-1)^r`
coming from the shift `[r]`, the classical Fourier transform of the trace function of `K`
(`FiniteField.fourierTransformPi`):

`t_{FT_ψ(K)}(y) = (-1)^r ∑_{x ∈ 𝔽_{qⁿ}^ι} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}⟨x, y⟩)`.

The proof is base change of `Rpr₂!` along the point `y`, the Grothendieck–Lefschetz formula on
the fibre of `pr₂` over `y`, whose `𝔽_{qⁿ}`-points are the pairs `(φ, x)` of a `k₀`-embedding
`φ` of `𝔽_{qⁿ}` and a vector `x`, and the trace function of the Artin–Schreier sheaf pulled back
along the pairing.

On the affine line `𝔸¹ = 𝔸^PUnit` (`ι = PUnit`, `r = 1`) the rational points are the elements of
`𝔽_{qⁿ}` (`AlgebraicGeometry.AffineSpace.fieldPointsEquiv`) and the formula reads

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`

(`FiniteField.fourierTransform`). The two numerical identities of the transform follow from the
corresponding identities of the classical transform: *Plancherel* (deduced in
`WeilConjectures.WeilSheaf.FourierPlancherel`), `∑_y |j t_{FT_ψ(K)}(y)|² = q^{nr} ∑_x |j t_K(x)|²`,
and *trace-level inversion*, `t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = q^{nr} t_K(y)`.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`: the Fourier trace
  formula on `𝔸^ι`, and `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform`, its case
  `ι = PUnit`.
- `AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform_inv`: trace-level
  Fourier inversion on `𝔸^ι`, and
  `AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform_inv_fourierTransform`, its case
  `ι = PUnit`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The Grothendieck–Lefschetz formula, relative form: for a morphism `f : P ⟶ T` of separated
`k₀`-schemes of finite type and a Weil complex `M` on `P`, the sums of the trace functions of
`Rf₀! M` over `T(𝔽_{qᵐ})` and of `M` over `P(𝔽_{qᵐ})` agree. Both are the alternating trace of
the Frobenius on `H_c(P ⊗ k̄, M) = H_c(T ⊗ k̄, Rf₀! M)`. -/
theorem finsum_traceFunction_derivedLowerShriek {P T : Scheme.{u}}
    [P.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))] (f : P ⟶ T)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated (P ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (P ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (P ↘ Spec (CommRingCat.of k₀))] [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] (M : WeilComplex k₀ l P) {m : ℕ}
    (hm : m ≠ 0) :
    ∑ᶠ t, ((derivedLowerShriek k₀ l f).obj M).traceFunction m t =
      ∑ᶠ w, M.traceFunction m w := by
  rw [← sum_trace_compactlySupportedCohomology_eq_sum_traceFunction _ hm,
    ← sum_trace_compactlySupportedCohomology_eq_sum_traceFunction _ hm]
  refine finsum_congr fun i ↦ ?_
  obtain ⟨e₁⟩ := nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (comp_over f (Spec (CommRingCat.of k₀)))
  obtain ⟨e₂⟩ := nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l) f
    (T ↘ Spec (CommRingCat.of k₀))
  congr 1
  exact (cohomologyFrobeniusModuleEquivOfIso ((e₁.symm ≪≫ e₂).app M) i).trace_frobenius_pow m

section AffineSpace

variable {ι : Type u}

/-- The trace function of a Weil complex on the affine space `𝔸^ι` at level `n`, as a function
on `𝔽_{qⁿ}^ι`, through the identification `𝔸^ι(𝔽_{qⁿ}) ≃ 𝔽_{qⁿ}^ι`. -/
noncomputable def affineSpaceTraceFunction (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    (n : ℕ) (x : ι → FiniteField.galoisExtension k₀ n) : PadicAlgCl l :=
  K.traceFunction n ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm x)

/-- The trace function of a Weil complex on `𝔸^ι` is invariant under the `k₀`-automorphisms of
`𝔽_{qⁿ}`, acting on the coordinates. -/
theorem affineSpaceTraceFunction_algEquiv (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    (n : ℕ) (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : ι → FiniteField.galoisExtension k₀ n) :
    K.affineSpaceTraceFunction n (fun i ↦ σ (x i)) = K.affineSpaceTraceFunction n x := by
  rw [affineSpaceTraceFunction, affineSpaceTraceFunction,
    ← traceFunction_fieldPointsCongr K n σ ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm x)]
  congr 1
  rw [Equiv.symm_apply_eq, AffineSpace.fieldPointsEquivPi_fieldPointsCongr,
    Equiv.apply_symm_apply]

variable [Fintype ι]

/-- The Weil complex `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` on `𝔸^ι ×_{k₀} 𝔸^ι`, whose direct image with
compact support along `pr₂` is the Fourier–Deligne transform of `K` up to the shift `[r]`. -/
noncomputable abbrev affineSpaceFourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) :
    WeilComplex k₀ l (affineSpacePair ι k₀) :=
  (tensorLisse (affineSpaceFourierKernel ι ψ) (isLisse_affineSpaceFourierKernel ι ψ)).obj
    ((upperStar (affineSpacePair.fst ι k₀)).obj K)

/-- The trace function of `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` at the point `(x, φ(y))` of the fibre of
`pr₂` over `y` is `ψ(Tr⟨x, φ(y)⟩) t_K(x)`. -/
theorem traceFunction_upperStar_affineSpaceFourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n))
    (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : ι → FiniteField.galoisExtension k₀ n) :
    ((upperStar (affineSpacePair.sndFiber.fst y)).obj
        (affineSpaceFourierIntegrand ψ K)).traceFunction n
        (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x)) =
      ψ (Algebra.trace k₀ _ (∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ _ y i))) *
        K.affineSpaceTraceFunction n x := by
  rw [traceFunction_upperStar, traceFunction_tensorLisse, affineSpaceFourierKernel,
    WeilSheaf.traceFunction_upperStar, WeilSheaf.traceFunction_artinSchreier ψ 1 hn,
    traceFunction_upperStar, map_one, one_mul, affineSpaceTraceFunction]
  have hK : Scheme.Hom.mapFieldPoints (affineSpacePair.fst ι k₀) _
      (Scheme.Hom.mapFieldPoints (affineSpacePair.sndFiber.fst y) _
        (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x))) =
      (AffineSpace.fieldPointsEquivPi ι k₀ _).symm x :=
    Subtype.ext ((Category.assoc _ _ _).trans (affineSpacePair.sndFiber.lift_fst_fst φ x))
  have hμ : (Scheme.ΓSpecIso (.of _)).hom.hom
      ((Scheme.Hom.mapFieldPoints (affineSpacePair.pairing ι k₀) _
        (Scheme.Hom.mapFieldPoints (affineSpacePair.sndFiber.fst y) _
          (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x)))).1.appTop
            (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ _ y i) := by
    rw [← affineSpacePair.sndFiber.ΓSpecIso_hom_appTop_lift_pairing φ x, ← Category.assoc]
    rfl
  rw [hK, hμ]

variable [DecidableEq ι]

/-- Summing the trace function of `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` over the `𝔽_{qⁿ}`-rational points
`(x, φ(y))` of the fibre of `pr₂` over `y` gives `n` times the classical Fourier transform of
`t_K` at `y`: by Galois invariance the `n` embeddings `φ` contribute the same sum. -/
theorem finsum_traceFunction_upperStar_affineSpaceFourierIntegrand
    (ψ : AddChar k₀ (PadicAlgCl l)) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    {n : ℕ} (hn : n ≠ 0) [Fintype (FiniteField.galoisExtension k₀ n)]
    (y : ι → FiniteField.galoisExtension k₀ n) :
    ∑ᶠ w, ((upperStar (affineSpacePair.sndFiber.fst
        ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm y))).obj
        (affineSpaceFourierIntegrand ψ K)).traceFunction n w =
      n • FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
  have : Fintype (FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :=
    Fintype.ofFinite _
  rw [← finsum_comp_equiv (affineSpacePair.sndFiber.fieldPointsEquiv _ _),
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp_rw [traceFunction_upperStar_affineSpaceFourierIntegrand ψ K hn, Equiv.apply_symm_apply]
  have h (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :
      ∑ x : ι → FiniteField.galoisExtension k₀ n,
          ψ (Algebra.trace k₀ _ (∑ i, x i * φ (y i))) * K.affineSpaceTraceFunction n x =
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
    rw [← MulEquiv.apply_symm_apply (algEquivEquivAlgHom k₀ _) φ,
      ← Equiv.sum_comp (Equiv.piCongrRight fun _ ↦
        ((algEquivEquivAlgHom k₀ _).symm φ).toEquiv)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    set σ := (algEquivEquivAlgHom k₀ _).symm φ
    have hσ (i : ι) : algEquivEquivAlgHom k₀ _ σ (y i) = σ (y i) := rfl
    have hx : (Equiv.piCongrRight fun _ ↦ σ.toEquiv) x = fun i ↦ σ (x i) := rfl
    simp_rw [hx, hσ, ← map_mul, ← map_sum, Algebra.trace_eq_of_algEquiv,
      affineSpaceTraceFunction_algEquiv]
    exact mul_comm _ _
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteField.nat_card_algHom_galoisExtension k₀ hn]

/-- **The Fourier trace formula on `𝔸^ι`.** For an additive character `ψ` of `k₀`, a Weil complex
`K` on the affine space `𝔸^ι` with `r = #ι`, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}^ι`,

`t_{FT_ψ(K)}(y) = (-1)^r ∑_{x ∈ 𝔽_{qⁿ}^ι} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}⟨x, y⟩)`:

up to the sign coming from the shift `[r]`, the trace function of the transform is the
classical Fourier transform of the trace function of `K`.
(sketch blueprint: `sec-The-Plancherel-formula`; blueprint: `sec-The-Plancherel-formula`) -/
theorem traceFunction_affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] (y : ι → FiniteField.galoisExtension k₀ n) :
    ((affineSpaceFourierTransform ι ψ).obj K).affineSpaceTraceFunction n y =
      (-1) ^ Fintype.card ι *
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
  set yp := (AffineSpace.fieldPointsEquivPi ι k₀ _).symm y
  -- base change of `Rpr₂!` along the point `y : Spec 𝔽_{qⁿ} ⟶ 𝔸^ι`
  obtain ⟨e⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint yp) (affineSpacePair.sndFiber.snd yp)
    (affineSpacePair.sndFiber.fst yp) (affineSpacePair.sndFiber.isPullback yp)
  have he := e.app (affineSpaceFourierIntegrand ψ K)
  dsimp only [Functor.comp_obj] at he
  have hτ : (specOver.homOfFieldPoint yp).mapFieldPoints _ (specOver.tautPoint k₀ _) = yp :=
    Subtype.ext (Category.id_comp _)
  -- `n t_{Rpr₂! M}(y)` is the sum of `t_{Rpr₂! M}` over the Galois conjugates of `y`, hence by
  -- Grothendieck–Lefschetz the sum of `t_M` over the fibre of `pr₂` over `y`
  have key : n • ((derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀)).obj
      (affineSpaceFourierIntegrand ψ K)).traceFunction n yp =
      n • FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
    rw [← hτ, ← traceFunction_upperStar, traceFunction_congr he,
      ← specOver.finsum_fieldPoints_eq_nsmul k₀ hn _
        fun σ x ↦ traceFunction_fieldPointsCongr _ n σ x,
      finsum_traceFunction_derivedLowerShriek _ _ hn,
      finsum_traceFunction_upperStar_affineSpaceFourierIntegrand ψ K hn]
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have h := traceFunction_shift ((derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀)).obj
    (affineSpaceFourierIntegrand ψ K)) (Fintype.card ι) n yp
  rw [Int.coe_negOnePow_natCast, mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) key, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  exact h

/-- The `qⁿ` elements of `𝔽_{qⁿ}`, as a scalar. -/
private lemma card_galoisExtension_eq {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] :
    (Fintype.card (FiniteField.galoisExtension k₀ n) : ℕ) = Nat.card k₀ ^ n := by
  rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k₀ n hn]

omit [DecidableEq ι] in
/-- **Trace-level Fourier inversion on `𝔸^ι`.** For a nontrivial additive character `ψ` of
`k₀`, a Weil complex `K` on `𝔸^ι` with `r = #ι`, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}^ι`,

`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = q^{nr} t_K(y)`.

It is the Fourier trace formula applied twice, the signs `(-1)^r` cancelling, followed by
classical Fourier inversion (`FiniteField.fourierTransformPi_inv_fourierTransformPi`).
(sketch blueprint: `det-prop-double-trace`) -/
theorem traceFunction_affineSpaceFourierTransform_inv {ψ : AddChar k₀ (PadicAlgCl l)}
    (hψ : ψ ≠ 1) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    (y : ι → FiniteField.galoisExtension k₀ n) :
    ((affineSpaceFourierTransform ι ψ⁻¹).obj
        ((affineSpaceFourierTransform ι ψ).obj K)).affineSpaceTraceFunction n y =
      (Nat.card k₀ : PadicAlgCl l) ^ (n * Fintype.card ι) * K.affineSpaceTraceFunction n y := by
  classical
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have h : ((affineSpaceFourierTransform ι ψ).obj K).affineSpaceTraceFunction n =
      fun x ↦ (-1) ^ Fintype.card ι *
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) x :=
    funext fun x ↦ traceFunction_affineSpaceFourierTransform ψ K hn x
  rw [traceFunction_affineSpaceFourierTransform ψ⁻¹ _ hn, h,
    FiniteField.fourierTransformPi_const_mul, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul, FiniteField.fourierTransformPi_inv_fourierTransformPi hψ,
    card_galoisExtension_eq hn, pow_mul]
  push_cast
  rfl

end AffineSpace

section AffineLine

/-- The trace function of a Weil complex on the affine line at level `n`, as a function on
`𝔽_{qⁿ}`, through the identification `𝔸¹(𝔽_{qⁿ}) ≃ 𝔽_{qⁿ}`. -/
noncomputable def affineLineTraceFunction (K : WeilComplex k₀ l (affineLine k₀)) (n : ℕ)
    (x : FiniteField.galoisExtension k₀ n) : PadicAlgCl l :=
  K.traceFunction n ((AffineSpace.fieldPointsEquiv k₀ _).symm x)

/-- The trace function on the affine line is the trace function on `𝔸^ι` for `ι = PUnit`, at the
constant vector. -/
lemma affineLineTraceFunction_eq (K : WeilComplex k₀ l (affineLine k₀)) (n : ℕ)
    (x : FiniteField.galoisExtension k₀ n) :
    K.affineLineTraceFunction n x = K.affineSpaceTraceFunction (ι := PUnit.{u + 1}) n fun _ ↦ x :=
  rfl

/-- The trace function of a Weil complex on the affine line is invariant under the
`k₀`-automorphisms of `𝔽_{qⁿ}`. -/
theorem affineLineTraceFunction_algEquiv (K : WeilComplex k₀ l (affineLine k₀)) (n : ℕ)
    (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : FiniteField.galoisExtension k₀ n) :
    K.affineLineTraceFunction n (σ x) = K.affineLineTraceFunction n x := by
  rw [affineLineTraceFunction, affineLineTraceFunction,
    ← traceFunction_fieldPointsCongr K n σ ((AffineSpace.fieldPointsEquiv k₀ _).symm x)]
  congr 1
  rw [Equiv.symm_apply_eq, AffineSpace.fieldPointsEquiv_fieldPointsCongr, Equiv.apply_symm_apply]

/-- The Weil complex `pr₁^* K ⊗ μ^* ℒ_ψ` on the affine plane, whose direct image with compact
support along `pr₂` is the Fourier–Deligne transform of `K` up to the shift `[1]`. -/
noncomputable abbrev fourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) : WeilComplex k₀ l (affinePlane k₀) :=
  (tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).obj
    ((upperStar (affinePlane.fst k₀)).obj K)

/-- The trace function of `pr₁^* K ⊗ μ^* ℒ_ψ` at the point `(x, φ(y))` of the fibre of `pr₂`
over `y` is `ψ(Tr(x φ(y))) t_K(x)`. -/
theorem traceFunction_upperStar_fourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n))
    (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : FiniteField.galoisExtension k₀ n) :
    ((upperStar (affinePlane.sndFiber.fst y)).obj (fourierIntegrand ψ K)).traceFunction n
        (affinePlane.sndFiber.fieldPointsEquiv y _ (φ, x)) =
      ψ (Algebra.trace k₀ _ (x * φ (AffineSpace.fieldPointsEquiv k₀ _ y))) *
        K.affineLineTraceFunction n x := by
  rw [traceFunction_upperStar, traceFunction_tensorLisse, fourierKernel, affineSpaceFourierKernel,
    WeilSheaf.traceFunction_upperStar, WeilSheaf.traceFunction_artinSchreier ψ 1 hn,
    traceFunction_upperStar, map_one, one_mul, affineLineTraceFunction]
  have hK : Scheme.Hom.mapFieldPoints (affinePlane.fst k₀) _
      (Scheme.Hom.mapFieldPoints (affinePlane.sndFiber.fst y) _
        (affinePlane.sndFiber.fieldPointsEquiv y _ (φ, x))) =
      (AffineSpace.fieldPointsEquiv k₀ _).symm x :=
    Subtype.ext ((Category.assoc _ _ _).trans (affinePlane.sndFiber.lift_fst_fst φ x))
  have hμ : (Scheme.ΓSpecIso (.of _)).hom.hom
      ((Scheme.Hom.mapFieldPoints (affineSpacePair.pairing PUnit.{u + 1} k₀) _
        (Scheme.Hom.mapFieldPoints (affinePlane.sndFiber.fst y) _
          (affinePlane.sndFiber.fieldPointsEquiv y _ (φ, x)))).1.appTop
            (AffineSpace.coord _ PUnit.unit)) =
      x * φ (AffineSpace.fieldPointsEquiv k₀ _ y) := by
    rw [← affinePlane.sndFiber.ΓSpecIso_hom_appTop_lift_mul φ x, ← Category.assoc,
      ← affineSpacePair.pairing_punit]
    rfl
  rw [hK, hμ]

/-- Summing the trace function of `pr₁^* K ⊗ μ^* ℒ_ψ` over the `𝔽_{qⁿ}`-rational points
`(x, φ(y))` of the fibre of `pr₂` over `y` gives `n` times the classical Fourier transform of
`t_K` at `y`: by Galois invariance the `n` embeddings `φ` contribute the same sum. -/
theorem finsum_traceFunction_upperStar_fourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] (y : FiniteField.galoisExtension k₀ n) :
    ∑ᶠ w, ((upperStar (affinePlane.sndFiber.fst ((AffineSpace.fieldPointsEquiv k₀ _).symm y))).obj
        (fourierIntegrand ψ K)).traceFunction n w =
      n • FiniteField.fourierTransform ψ (K.affineLineTraceFunction n) y := by
  have : Fintype (FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :=
    Fintype.ofFinite _
  rw [← finsum_comp_equiv (affinePlane.sndFiber.fieldPointsEquiv _ _), finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type]
  simp_rw [traceFunction_upperStar_fourierIntegrand ψ K hn, Equiv.apply_symm_apply]
  have h (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :
      ∑ x, ψ (Algebra.trace k₀ _ (x * φ y)) * K.affineLineTraceFunction n x =
        FiniteField.fourierTransform ψ (K.affineLineTraceFunction n) y := by
    rw [← MulEquiv.apply_symm_apply (algEquivEquivAlgHom k₀ _) φ,
      ← Equiv.sum_comp ((algEquivEquivAlgHom k₀ _).symm φ).toEquiv]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    set σ := (algEquivEquivAlgHom k₀ _).symm φ
    have hσ : algEquivEquivAlgHom k₀ _ σ y = σ y := rfl
    have hx : σ.toEquiv x = σ x := rfl
    rw [mul_comm, hx, hσ, ← map_mul, Algebra.trace_eq_of_algEquiv,
      affineLineTraceFunction_algEquiv]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteField.nat_card_algHom_galoisExtension k₀ hn]

/-- **The Fourier trace formula.** For an additive character `ψ` of `k₀`, a Weil complex `K` on
the affine line, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}`,

`t_{FT_ψ(K)}(y) = -∑_{x ∈ 𝔽_{qⁿ}} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}(x y))`:

up to the sign coming from the shift `[1]`, the trace function of the transform is the
classical Fourier transform of the trace function of `K`. It is the case `ι = PUnit` of
`AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`.
(sketch blueprint: `sec-The-Plancherel-formula`; blueprint: `sec-The-Plancherel-formula`) -/
theorem traceFunction_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] (y : FiniteField.galoisExtension k₀ n) :
    ((fourierTransform ψ).obj K).affineLineTraceFunction n y =
      -FiniteField.fourierTransform ψ (K.affineLineTraceFunction n) y := by
  have h := traceFunction_affineSpaceFourierTransform (ι := PUnit.{u + 1}) ψ K hn fun _ ↦ y
  rw [FiniteField.fourierTransformPi_unique, Fintype.card_punit, pow_one, neg_one_mul] at h
  exact h

/-- **Trace-level Fourier inversion.** For a nontrivial additive character `ψ` of `k₀`, a Weil
complex `K` on the affine line, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}`,

`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = qⁿ t_K(y)`,

which is the trace function of the Tate twist `K(-1)` at points of degree `n`. It is the case
`ι = PUnit` of `AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform_inv`.
(sketch blueprint: `det-prop-double-trace`) -/
theorem traceFunction_fourierTransform_inv_fourierTransform {ψ : AddChar k₀ (PadicAlgCl l)}
    (hψ : ψ ≠ 1) (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : n ≠ 0)
    (y : FiniteField.galoisExtension k₀ n) :
    ((fourierTransform ψ⁻¹).obj ((fourierTransform ψ).obj K)).affineLineTraceFunction n y =
      (Nat.card k₀ : PadicAlgCl l) ^ n * K.affineLineTraceFunction n y := by
  have h := traceFunction_affineSpaceFourierTransform_inv (ι := PUnit.{u + 1}) hψ K hn fun _ ↦ y
  rw [Fintype.card_punit, mul_one] at h
  exact h

end AffineLine

end AlgebraicGeometry.WeilComplex
