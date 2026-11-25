/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTensor

/-!

# The residue field of `Ω ⊗_{k'((t))} K((t))` and the compositum `K((t))·Ω ⊆ Ω_K`

Let `F = k'((t))`, `F_K = K((t))`, `Ω = F^alg`, `Ω_K = F_K^alg` and `F^sep ⊆ Ω` the separable
closure. The product map `Ω ⊗_F F_K ⟶ Ω_K` (`AlgebraicGeometry.traitGenericTensorLift`, from the
embedding `Ω ⟶ Ω_K` over `F ⟶ F_K`) has image the compositum `L = F_K·Ω`
(`AlgebraicGeometry.traitGenericCompositum`, `AlgebraicGeometry.range_traitGenericTensorLift`).
Since `Spec(Ω ⊗_F F_K)` is a single point
(`AlgebraicGeometry.subsingleton_primeSpectrum_traitGenericField_tensorProduct`), its kernel is
the nilradical (`AlgebraicGeometry.ker_traitGenericTensorLift`), so `L` is the residue field of
the unique point (`AlgebraicGeometry.traitGenericTensorResidueEquiv`). Moreover:

* `L` is purely inseparable over `F_K·F^sep`
  (`AlgebraicGeometry.isPurelyInseparable_traitGenericCompositum`);
* `Ω_K / L` is algebraic, `L^sep / L` is Galois and `Ω_K / L^sep` is purely inseparable
  (`AlgebraicGeometry.traitGenericCompositum_tower`).

-/

@[expose] public section

open IntermediateField

open scoped TensorProduct

/-- If `Spec R` has at most one point, the kernel of every ring map from `R` to a domain is the
nilradical of `R`. -/
theorem RingHom.ker_eq_nilradical_of_subsingleton_primeSpectrum {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] [Subsingleton (PrimeSpectrum R)] (f : R →+* S) :
    RingHom.ker f = nilradical R := by
  have hp : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  rw [nilradical_eq_sInf]
  refine le_antisymm (le_sInf fun J hJ ↦ ?_) (sInf_le hp)
  exact (congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨_, hp⟩ : PrimeSpectrum R) ⟨J, hJ⟩)).le

universe u

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The embedding `Ω ⟶ Ω_K` (`AlgebraicGeometry.traitGenericFieldMap`) as a `k'((t))`-algebra
map, `Ω_K` being a `k'((t))`-algebra through `k'((t)) ⟶ K((t)) ⟶ Ω_K`. -/
noncomputable def traitGenericFieldAlgHom :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    traitGenericField k' →ₐ[FractionRing (PowerSeries k')] traitGenericField K :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  { traitGenericFieldMap k' K with
    commutes' := fun r ↦ by
      have h := (letI := (traitFractionFieldMap k' K).toAlgebra
        (IsAlgClosed.lift (R := FractionRing (PowerSeries k')) (S := traitGenericField k')
          (M := traitGenericField K)).commutes r)
      change traitGenericFieldMap k' K (algebraMap _ _ r) = _
      rw [show traitGenericFieldMap k' K (algebraMap _ _ r) = traitFractionFieldMap k' K r from h,
        traitFractionFieldMap_eq_comp, IsScalarTower.algebraMap_apply _
          (FractionRing (PowerSeries K)) (traitGenericField K)]
      rfl }

/-- The product map `Ω ⊗_F F_K ⟶ Ω_K`, `ω ⊗ a ↦ ω·a`. -/
noncomputable def traitGenericTensorLift :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    traitGenericField k' ⊗[FractionRing (PowerSeries k')] FractionRing (PowerSeries K) →+*
      traitGenericField K :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  (Algebra.TensorProduct.productMap (traitGenericFieldAlgHom k' K)
    (IsScalarTower.toAlgHom (FractionRing (PowerSeries k')) (FractionRing (PowerSeries K))
      (traitGenericField K))).toRingHom

/-- The product map on pure tensors. -/
lemma traitGenericTensorLift_tmul (ω : traitGenericField k') (a : FractionRing (PowerSeries K)) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    traitGenericTensorLift k' K (ω ⊗ₜ a) =
      traitGenericFieldMap k' K ω * algebraMap _ (traitGenericField K) a :=
  rfl

/-- The compositum `L = F_K·Ω = F_K(Ω)` of `F_K = K((t))` and the image of `Ω` in `Ω_K`. -/
noncomputable def traitGenericCompositum :
    IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K) :=
  adjoin (FractionRing (PowerSeries K)) (Set.range (traitGenericFieldMap k' K))

/-- The image of `Ω ⊗_F F_K ⟶ Ω_K` is the compositum `F_K·Ω` (a field, `Ω_K` being algebraic
over `F_K`). -/
theorem range_traitGenericTensorLift :
    (traitGenericTensorLift k' K).range = (traitGenericCompositum k' K).toSubalgebra.toSubring := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul ω a =>
      rw [traitGenericTensorLift_tmul]
      exact mul_mem (subset_adjoin _ _ ⟨ω, rfl⟩) (algebraMap_mem _ a)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · let T : Subalgebra (FractionRing (PowerSeries K)) (traitGenericField K) :=
      { (traitGenericTensorLift k' K).range with
        algebraMap_mem' := fun a ↦ ⟨1 ⊗ₜ a, by rw [traitGenericTensorLift_tmul]; simp⟩ }
    let I : IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K) :=
      T.toIntermediateField fun x hx ↦ T.inv_mem_of_algebraic (x := ⟨x, hx⟩)
        (Algebra.IsAlgebraic.isAlgebraic _)
    have : traitGenericCompositum k' K ≤ I := by
      refine adjoin_le_iff.mpr ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨ω ⊗ₜ 1, by rw [traitGenericTensorLift_tmul]; simp⟩
    exact this

variable {k' K} [IsSepClosed k'] [IsAlgClosed K]

/-- The kernel of `Ω ⊗_F F_K ⟶ Ω_K` is the nilradical, the unique prime ideal. -/
theorem ker_traitGenericTensorLift (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    RingHom.ker (traitGenericTensorLift k' K) = nilradical _ := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  have := subsingleton_primeSpectrum_traitGenericField_tensorProduct (K := K) htr
  exact RingHom.ker_eq_nilradical_of_subsingleton_primeSpectrum _

/-- **The residue field of the unique point of `Spec(Ω ⊗_F F_K)` is the compositum `F_K·Ω`**:
`(Ω ⊗_F F_K)_red ≃ F_K·Ω ⊆ Ω_K`. -/
noncomputable def traitGenericTensorResidueEquiv (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    (traitGenericField k' ⊗[FractionRing (PowerSeries k')] FractionRing (PowerSeries K)) ⧸
      nilradical (traitGenericField k' ⊗[FractionRing (PowerSeries k')]
        FractionRing (PowerSeries K)) ≃+* traitGenericCompositum k' K :=
  letI := (traitLaurentFieldMap k' K).toAlgebra
  (Ideal.quotEquivOfEq (ker_traitGenericTensorLift htr).symm).trans
    (((traitGenericTensorLift k' K).quotientKerEquivRange).trans
      (RingEquiv.subringCongr (range_traitGenericTensorLift k' K)))

/-- The nilradical of `Ω ⊗_F F_K` is a maximal ideal. -/
theorem isMaximal_nilradical_traitGenericField_tensorProduct (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    (nilradical (traitGenericField k' ⊗[FractionRing (PowerSeries k')]
      FractionRing (PowerSeries K))).IsMaximal := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (traitGenericTensorResidueEquiv htr).toMulEquiv.isField (Field.toIsField _)

variable (k' K) in
/-- The compositum `F_K·F^sep = F_K(F^sep)` inside `Ω_K`. -/
noncomputable def traitGenericSepCompositum :
    IntermediateField (FractionRing (PowerSeries K)) (traitGenericField K) :=
  adjoin (FractionRing (PowerSeries K)) (traitGenericFieldMap k' K ''
    separableClosure (FractionRing (PowerSeries k')) (traitGenericField k'))

omit [IsSepClosed k'] [IsAlgClosed K] in
/-- `F_K·F^sep ⊆ F_K·Ω`. -/
lemma traitGenericSepCompositum_le :
    traitGenericSepCompositum k' K ≤ traitGenericCompositum k' K :=
  adjoin.mono _ _ _ (Set.image_subset_range _ _)

omit [IsSepClosed k'] [IsAlgClosed K] in
/-- **`F_K·Ω` is purely inseparable over `F_K·F^sep`**, since `Ω` is purely inseparable over
`F^sep`. -/
theorem isPurelyInseparable_traitGenericCompositum :
    IsPurelyInseparable (traitGenericSepCompositum k' K)
      (extendScalars (traitGenericSepCompositum_le (k' := k') (K := K))) := by
  have h : traitGenericSepCompositum k' K ≤ adjoin (FractionRing (PowerSeries K))
      (Set.range (traitGenericFieldMap k' K)) := traitGenericSepCompositum_le
  change IsPurelyInseparable _ (extendScalars h)
  rw [extendScalars_adjoin]
  let q := ringExpChar (traitGenericField K)
  have : ExpChar (traitGenericSepCompositum k' K) q :=
    (algebraMap (traitGenericSepCompositum k' K) (traitGenericField K)).expChar
      (algebraMap (traitGenericSepCompositum k' K) (traitGenericField K)).injective q
  have : ExpChar (traitGenericField k') q :=
    (traitGenericFieldMap k' K).expChar (traitGenericFieldMap k' K).injective q
  have : ExpChar (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k')) q :=
    (algebraMap _ (traitGenericField k')).expChar (Subtype.val_injective) q
  refine (isPurelyInseparable_adjoin_iff_pow_mem _ _ q).mpr ?_
  rintro _ ⟨ω, rfl⟩
  obtain ⟨n, s, hs⟩ := IsPurelyInseparable.pow_mem
    (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k')) q ω
  refine ⟨n, ⟨⟨traitGenericFieldMap k' K s, subset_adjoin _ _ ⟨s, s.2, rfl⟩⟩, ?_⟩⟩
  change traitGenericFieldMap k' K s = _
  rw [← map_pow, ← hs]
  rfl

omit [IsSepClosed k'] [IsAlgClosed K] in
/-- **Decomposition of `Ω_K / F_K·Ω`**: `Ω_K` is algebraic over the compositum `L = F_K·Ω`; the
separable closure `L^sep` of `L` in `Ω_K` is Galois over `L`, and `Ω_K / L^sep` is purely
inseparable. -/
theorem traitGenericCompositum_tower :
    Algebra.IsAlgebraic (traitGenericCompositum k' K) (traitGenericField K) ∧
      IsGalois (traitGenericCompositum k' K)
        (separableClosure (traitGenericCompositum k' K) (traitGenericField K)) ∧
      IsPurelyInseparable (separableClosure (traitGenericCompositum k' K) (traitGenericField K))
        (traitGenericField K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
