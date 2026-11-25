/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineConstructible
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Generic slices of the affine line over the trait

Let `k'` be a field, `K` a field extension of `k'` and `x ∈ K`. The ring homomorphism
`k'⟦t⟧[x] ⟶ K⟦t⟧` extending the coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧` by `x ↦ x`
(`AlgebraicGeometry.traitSliceRingHom`) defines a morphism
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` over the trait map `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧ = S`
(`AlgebraicGeometry.traitSlice`). On closed points it is the point `x : Spec K ⟶ 𝔸¹_{k'}` of
the special fibre of `𝔸¹_S` (`AlgebraicGeometry.traitClosedPoint_traitSlice`); if `x` is
transcendental over `k'` (for instance `K` a separable closure of `k'(x)`), this is the generic
point of the special-fibre line (`AlgebraicGeometry.isGenericPoint_traitSlicePoint`). This is the
*generic slice* of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, identification (2)): `Spec K⟦t⟧` is the
completion of the strict localization of `𝔸¹_S` at the generic point of its special fibre.

The square of traits `Spec K ⟶ Spec K⟦t⟧`, `Spec k' ⟶ Spec k'⟦t⟧` is cartesian
(`AlgebraicGeometry.isPullback_traitClosedPoint_traitMap`).

For a model `M` over `S` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the *slice model* `M''` has total space
`𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, special fibre `𝒳''_s = 𝒳'' ×_{Spec K⟦t⟧} Spec K` and generic fibre
`𝒳'' ×_{Spec K⟦t⟧} E` over a given scheme `E` mapping to `Spec K⟦t⟧` and to the geometric generic
point `Spec Ω` of `S` (`NearbyCyclesModel.sliceModel`, for `E = Spec L`, `L` the compositum of `Ω`
and `Frac K⟦t⟧`). The projection is a morphism of models `M'' ⟶ M`
(`NearbyCyclesModel.sliceHom`) whose special-fibre square is cartesian
(`NearbyCyclesModel.isPullback_sliceHom_i`). Its pullback exchange `α` is invertible as soon as the
base change morphism of its square of generic fibres is
(`NearbyCyclesModel.isIso_pullbackExchange_sliceHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section TraitSlice

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The morphism of traits `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` induced by the coefficientwise map. -/
noncomputable def traitMap : trait K ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)))

/-- The constant coefficient of the coefficientwise image of a power series. -/
lemma constantCoeff_map_apply (f : PowerSeries k') :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap k' K) f) =
      algebraMap k' K (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]

/-- The constant coefficient commutes with the coefficientwise map. -/
lemma constantCoeff_comp_map :
    (PowerSeries.constantCoeff (R := K)).comp (PowerSeries.map (algebraMap k' K)) =
      (algebraMap k' K).comp PowerSeries.constantCoeff := by
  ext f
  exact constantCoeff_map_apply k' K f

/-- The closed point of `Spec K⟦t⟧` lies over the closed point of `Spec k'⟦t⟧`. -/
@[reassoc]
lemma traitClosedPoint_traitMap :
    traitClosedPoint K ≫ traitMap k' K =
      Spec.map (CommRingCat.ofHom (algebraMap k' K)) ≫ traitClosedPoint k' := by
  rw [traitClosedPoint, traitMap, traitClosedPoint, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_map]

/-- The square of rings `k'⟦t⟧ ⟶ K⟦t⟧ ⟶ K`, `k'⟦t⟧ ⟶ k' ⟶ K` is a pushout:
`K⟦t⟧ ⊗_{k'⟦t⟧} k' = K⟦t⟧/(t) = K`. -/
lemma isPushout_constantCoeff_map :
    IsPushout (CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)))
      (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k')))
      (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
      (CommRingCat.ofHom (algebraMap k' K)) := by
  have hsq : CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)) ≫
      CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)) =
      CommRingCat.ofHom (PowerSeries.constantCoeff (R := k')) ≫
        CommRingCat.ofHom (algebraMap k' K) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_map]
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (s.inl.hom.comp PowerSeries.C)) ?_ ?_ ?_)
  · intro s
    have hX : s.inl (PowerSeries.X : PowerSeries K) = 0 := by
      have := congr($(s.condition) (PowerSeries.X : PowerSeries k'))
      simpa using this
    ext f
    change s.inl (PowerSeries.C (PowerSeries.constantCoeff f)) = s.inl f
    conv_rhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
    simp [hX]
  · intro s
    ext a
    change s.inl (PowerSeries.C (algebraMap k' K a)) = s.inr a
    have := congr($(s.condition) (PowerSeries.C a))
    simpa using this
  · intro s m hm _
    ext a
    change m a = s.inl (PowerSeries.C a)
    rw [← hm]
    simp

/-- **The square of traits is cartesian**: `Spec K = Spec K⟦t⟧ ×_{Spec k'⟦t⟧} Spec k'`. -/
lemma isPullback_traitClosedPoint_traitMap :
    IsPullback (traitClosedPoint K) (Spec.map (CommRingCat.ofHom (algebraMap k' K)))
      (traitMap k' K) (traitClosedPoint k') :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_constantCoeff_map k' K)

variable {k' K} (x : K)

/-- The ring homomorphism `k'⟦t⟧[x] ⟶ K⟦t⟧` of the generic slice: the coefficientwise map on
`k'⟦t⟧`, and `x ↦ x`. -/
noncomputable def traitSliceRingHom :
    MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k') →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.map (algebraMap k' K)) fun _ ↦ PowerSeries.C x

/-- The generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`S = Spec k'⟦t⟧`) given by
`k'⟦t⟧[x] ⟶ K⟦t⟧`. -/
noncomputable def traitSlice : trait K ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
  Spec.map (CommRingCat.ofHom (traitSliceRingHom x)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv

/-- The generic slice lies over the trait map `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma traitSlice_over :
    traitSlice x ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = traitMap k' K := by
  rw [traitSlice, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, traitMap]
  congr 2
  ext a : 1
  simp [traitSliceRingHom]

/-- The point `x : Spec K ⟶ 𝔸¹_{k'}` of the special-fibre line, given by `k'[x] ⟶ K`. -/
noncomputable def traitSlicePoint : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k')) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k') fun _ : ULift.{u} (Fin 1) ↦ x)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k')).inv

/-- **The generic slice on closed points**: the closed point of `Spec K⟦t⟧` is mapped by `σ` to
the point `x` of the special-fibre line `𝔸¹_{k'} ⊆ 𝔸¹_S`. -/
@[reassoc]
lemma traitClosedPoint_traitSlice :
    traitClosedPoint K ≫ traitSlice x =
      traitSlicePoint x ≫ AffineSpace.map (ULift.{u} (Fin 1)) (traitClosedPoint k') := by
  simp only [traitClosedPoint]
  rw [AffineSpace.map_SpecMap, traitSlicePoint, traitSlice,
    Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp [traitSliceRingHom, constantCoeff_map_apply]
  · simp [traitSliceRingHom]

/-- **The generic slice hits the generic point of the special fibre**: if `x` is transcendental
over `k'`, the point `x : Spec K ⟶ 𝔸¹_{k'}` is the generic point of the special-fibre line. -/
lemma isGenericPoint_traitSlicePoint (hx : Transcendental k' x) (p : Spec (.of K)) :
    IsGenericPoint (traitSlicePoint (k' := k') x p) Set.univ := by
  refine isGenericPoint_of_isIso_of_asIdeal_eq_bot
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k')).hom ?_
  have hinj : Function.Injective
      (MvPolynomial.aeval (R := k') fun _ : ULift.{u} (Fin 1) ↦ x) :=
    (algebraicIndependent_iff_injective_aeval.mp
      ((algebraicIndependent_unique_type_iff (R := k')
        (x := fun _ : ULift.{u} (Fin 1) ↦ x)).mpr hx))
  have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [traitSlicePoint, ← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Spec.map_apply, PrimeSpectrum.comap_asIdeal, hp, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

end TraitSlice

namespace ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  {E : Scheme.{u}} {γ : E ⟶ trait K} {δ : E ⟶ Spec (.of (traitGenericField k'))}
  (hγδ : γ ≫ traitMap k' K = δ ≫ traitGenericPoint k')

include hb in
/-- On the total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` of the slice, the two maps to the trait
`S = Spec k'⟦t⟧` agree. -/
@[reassoc]
lemma pullback_fst_comp_eq_snd_traitMap :
    pullback.fst b (traitSlice x) ≫ q = pullback.snd b (traitSlice x) ≫ traitMap k' K := by
  rw [← hb, pullback.condition_assoc, traitSlice_over]

/-- The special fibre `𝒳''_s = 𝒳'' ×_{Spec K⟦t⟧} Spec K` of the slice model. -/
noncomputable abbrev sliceSpecial (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')) : Scheme.{u} :=
  pullback (pullback.snd b (traitSlice x)) (traitClosedPoint K)

/-- The geometric generic fibre `𝒳'' ×_{Spec K⟦t⟧} E` of the slice model. -/
noncomputable abbrev sliceGeneric (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
    (γ : E ⟶ trait K) : Scheme.{u} :=
  pullback (pullback.snd b (traitSlice x)) γ

/-- The map of geometric generic fibres `𝒳'' ×_{Spec K⟦t⟧} E ⟶ 𝒳_η̄ = 𝒳 ×_S Spec Ω` of the
slice, induced by `δ : E ⟶ Spec Ω`. -/
noncomputable def sliceGenericMap : sliceGeneric x b γ ⟶ M.generic :=
  hM.isPullback_j.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ δ) (by
    rw [Category.assoc, pullback_fst_comp_eq_snd_traitMap x hb, pullback.condition_assoc, hγδ,
      Category.assoc])

/-- The map of special fibres `𝒳''_s ⟶ 𝒳_s` of the slice. -/
noncomputable def sliceSpecialMap : sliceSpecial x b ⟶ X'.left :=
  hM.isPullback_i.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K))) (by
    rw [Category.assoc, pullback_fst_comp_eq_snd_traitMap x hb, pullback.condition_assoc,
      traitClosedPoint_traitMap, Category.assoc])

/-- The *slice model* `M''` of a model `M` over `S = Spec k'⟦t⟧` with a coordinate
`b : 𝒳 ⟶ 𝔸¹_S`, along the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`: total space
`𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, special fibre `𝒳'' ×_{Spec K⟦t⟧} Spec K`, geometric generic fibre
`𝒳'' ×_{Spec K⟦t⟧} E`, mapping to `X` through `𝒳_η̄`. -/
noncomputable def sliceModel : NearbyCyclesModel X (sliceSpecial x b) where
  total := pullback b (traitSlice x)
  generic := sliceGeneric x b γ
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := sliceGenericMap x hM hb hγδ ≫ M.ε

/-- The projection `M'' ⟶ M` from the slice model, a morphism of models over `𝟙 X` and the map of
special fibres `𝒳''_s ⟶ 𝒳_s`. -/
noncomputable def sliceHom :
    (sliceModel x hM hb hγδ).Hom M (𝟙 X) (sliceSpecialMap x hM hb) where
  total := pullback.fst _ _
  generic := sliceGenericMap x hM hb hγδ
  comm_j := hM.isPullback_j.lift_fst _ _ _
  comm_i := hM.isPullback_i.lift_fst _ _ _
  comm_ε := (Category.comp_id _).symm

/-- **The special-fibre square of the slice is cartesian**: `𝒳''_s = 𝒳_s ×_𝒳 𝒳''`. This uses
that the square of traits `Spec K = Spec K⟦t⟧ ×_{Spec k'⟦t⟧} Spec k'` is cartesian. -/
lemma isPullback_sliceHom_i :
    IsPullback (sliceSpecialMap x hM hb) (sliceModel x hM hb hγδ).i M.i
      (sliceHom x hM hb hγδ).total := by
  have hs := (IsPullback.of_hasPullback (pullback.snd b (traitSlice x))
    (traitClosedPoint K)).flip.paste_horiz (isPullback_traitClosedPoint_traitMap k' K).flip
  have e : sliceSpecialMap x hM hb ≫ X'.hom =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)) :=
    hM.isPullback_i.lift_snd _ _ _
  rw [← e, ← pullback_fst_comp_eq_snd_traitMap x hb] at hs
  exact IsPullback.of_right hs (hM.isPullback_i.lift_fst _ _ _) hM.isPullback_i.flip

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Reduction of the slice identification to generic base change**: the pullback exchange
`α : Lf'^* Ψ_M ⟶ Ψ_{M''}` of the slice is an isomorphism as soon as the base change morphism of
its square of geometric generic fibres is. -/
theorem isIso_pullbackExchange_sliceHom
    [IsIso (baseChangeMap Λ (sliceHom x hM hb hγδ).commSq_j)] :
    IsIso ((sliceHom x hM hb hγδ).pullbackExchange Λ) :=
  (sliceHom x hM hb hγδ).isIso_pullbackExchange_of_isIso_baseChangeMap Λ

end NearbyCyclesModel

end ProEtale.CondensedRing

end AlgebraicGeometry
