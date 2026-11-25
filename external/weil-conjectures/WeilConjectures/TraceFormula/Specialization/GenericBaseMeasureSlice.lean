/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.PowerSeriesTranscendentalConstant
public import WeilConjectures.TraceFormula.Specialization.GenericBaseMeasure
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!
# The measure drops along generic slices

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base, with coordinate
`b : 𝒳 ⟶ 𝔸¹_S`, and let `x ∈ K` be transcendental over `k'`. The generic slice
`σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` hits the generic point of `𝔸¹_η`: the coordinate of `𝔸¹_η` is sent
to `x`, which is transcendental over `η = Frac k'⟦t⟧`
(`AlgebraicGeometry.transcendental_traitFractionMap_C`), so that the residue field of its image
has transcendence degree at least `1` over `η`
(`AlgebraicGeometry.one_le_trdegAt_traitGenericSlice`).

For a point `y` of the base `X₂ = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧` of the generic slice with image
`y₁ ∈ 𝒳_η ⊆ X₁ ×_F η` and `y₀ ∈ X₁`, this gives
`trdeg κ(y) + 1 ≤ trdeg_{κ(b(y₁))} κ(y₁) + trdeg_η κ(b(y₁)) = trdeg_η κ(y₁) ≤ trdeg_F κ(y₀)`,
using `AlgebraicGeometry.Scheme.Pullback.trdegAt_snd_le` twice. Hence
`μ X₂ + 1 ≤ μ X₁` unless `X₂` is empty
(`IsTraitModelOfGenericBase.genericBaseMeasure_genericSliceBase_add_one_le`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {x : K}

/-- If `x ∈ K` is transcendental over `k'`, the constant power series `x` is transcendental over
`Frac k'⟦t⟧` in `Frac K⟦t⟧`. -/
lemma transcendental_traitFractionMap_C (hx : Transcendental k' x) :
    letI := (traitFractionMap k' K).toAlgebra
    Transcendental (FractionRing (PowerSeries k'))
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C x)) := by
  let := (traitFractionMap k' K).toAlgebra
  let : Algebra (PowerSeries k') (FractionRing (PowerSeries K)) :=
    ((traitFractionMap k' K).comp (algebraMap _ (FractionRing (PowerSeries k')))).toAlgebra
  have : @IsScalarTower (PowerSeries k') (FractionRing (PowerSeries k'))
      (FractionRing (PowerSeries K)) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq' rfl
  intro h
  rw [← IsFractionRing.isAlgebraic_iff (PowerSeries k') (FractionRing (PowerSeries k'))] at h
  let : Algebra (PowerSeries k') (PowerSeries K) := (PowerSeries.map (algebraMap k' K)).toAlgebra
  exact PowerSeries.transcendental_C_of_transcendental hx (h.of_ringHom_of_comp_eq (RingHom.id _)
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) Function.surjective_id
    (IsFractionRing.injective _ _) (traitFractionMap_comp_algebraMap k' K))

lemma Scheme.SpecMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

variable (x) in
/-- The generic slice `σ_η` pulls back the coordinate of `𝔸¹_η` to `x ∈ Frac K⟦t⟧`. -/
lemma traitGenericSlice_appTop_coord :
    (traitGenericSlice (k' := k') x).appTop
        (AffineSpace.coord (Spec (.of (FractionRing (PowerSeries k')))) ⟨0⟩) =
      (Scheme.ΓSpecIso _).inv
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C x)) := by
  rw [← AffineSpace.map_appTop_coord (traitGenericSpec k'), ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, traitGenericSlice_map, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    traitSlice, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.SpecIso_inv_appTop_coord,
    Scheme.SpecMap_appTop_ΓSpecIso_inv, traitGenericSpec, Scheme.SpecMap_appTop_ΓSpecIso_inv]
  simp [traitSliceRingHom]

/-- **The generic slice hits a transcendental point**: if `x` is transcendental over `k'`, the
residue field of the image of `σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` has transcendence degree at least
`1` over `η`. -/
lemma one_le_trdegAt_traitGenericSlice (hx : Transcendental k' x)
    (s : Spec (.of (FractionRing (PowerSeries K)))) :
    1 ≤ (𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k')))) ↘
      Spec (.of (FractionRing (PowerSeries k')))).trdegAt (traitGenericSlice (k' := k') x s) := by
  set σ := traitGenericSlice (k' := k') x
  set π := 𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k')))) ↘
    Spec (.of (FractionRing (PowerSeries k')))
  set c := AffineSpace.coord (Spec (.of (FractionRing (PowerSeries k')))) (⟨0⟩ : ULift (Fin 1))
  let := (π.residueFieldMap (σ s)).hom.toAlgebra
  let := (traitFractionMap k' K).toAlgebra
  let : Algebra ((Spec (.of (FractionRing (PowerSeries k')))).residueField (π (σ s)))
      ((Spec (.of (FractionRing (PowerSeries K)))).residueField s) :=
    (π.residueFieldMap (σ s) ≫ σ.residueFieldMap s).hom.toAlgebra
  have htr : Transcendental ((Spec (.of (FractionRing (PowerSeries k')))).residueField (π (σ s)))
      ((𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k'))))).Γevaluation (σ s) c) := by
    intro halg
    have h₁ := halg.ringHom_of_comp_eq (RingHom.id _) (σ.residueFieldMap s).hom
      Function.injective_id rfl
    rw [Scheme.Γevaluation_naturality_apply, traitGenericSlice_appTop_coord] at h₁
    refine transcendental_traitFractionMap_C hx (h₁.of_ringHom_of_comp_eq
      ((Scheme.ΓSpecIso _).inv ≫ (Spec _).Γevaluation (π (σ s))).hom
      ((Scheme.ΓSpecIso _).inv ≫ (Spec _).Γevaluation s).hom
      (Scheme.bijective_ΓSpecIso_inv_Γevaluation _).2
      (Scheme.bijective_ΓSpecIso_inv_Γevaluation _).1 ?_)
    ext r
    have hσπ : σ ≫ π = traitGenericSpecMap k' K := traitGenericSlice_over x
    have happ : (σ ≫ π).appTop ((Scheme.ΓSpecIso _).inv r) =
        (Scheme.ΓSpecIso _).inv (traitFractionMap k' K r) := by
      rw [hσπ, traitGenericSpecMap, Scheme.SpecMap_appTop_ΓSpecIso_inv]
      rfl
    have key := Scheme.Γevaluation_naturality_apply (σ ≫ π) s ((Scheme.ΓSpecIso _).inv r)
    rw [Scheme.residueFieldMap_comp, CommRingCat.comp_apply, happ] at key
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, CommRingCat.hom_comp]
    exact key
  have : Algebra.Transcendental
      ((Spec (.of (FractionRing (PowerSeries k')))).residueField (π (σ s)))
      ((𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k'))))).residueField (σ s)) :=
    ⟨⟨_, htr⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {F : Type u} [Field F] {X₁ : Over (Spec (.of F))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}

/-- For a point `y` of the base `X₂` of the generic slice along `x` transcendental over `k'`,
there is a point `y₀ : X₁` with `trdeg κ(y) + 1 ≤ trdeg_F κ(y₀)`. -/
lemma IsTraitModelOfGenericBase.exists_trdegAt_genericSliceBase_add_one_le
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (hx : Transcendental k' x)
    (y : (genericSliceBase x hb).left) :
    ∃ y₀ : X₁.left, (genericSliceBase x hb).hom.trdegAt y + 1 ≤ X₁.hom.trdegAt y₀ := by
  obtain ⟨w, hw, hw₁, -⟩ := hM.exists_openImmersion_genericFibre
  set e := coordinateBaseChange b hb (traitGenericSpec k')
  set π := 𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k')))) ↘
    Spec (.of (FractionRing (PowerSeries k')))
  set y₁ := pullback.fst e (traitGenericSlice x) y
  refine ⟨pullback.fst X₁.hom ι (w y₁), ?_⟩
  have h₁ : (genericSliceBase x hb).hom.trdegAt y ≤ e.trdegAt y₁ :=
    Scheme.Pullback.trdegAt_snd_le y
  have h₂ : 1 ≤ π.trdegAt (e y₁) := by
    have : e y₁ = traitGenericSlice x (pullback.snd e (traitGenericSlice x) y) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [this]
    exact one_le_trdegAt_traitGenericSlice hx _
  have h₃ : e ≫ π = w ≫ pullback.snd X₁.hom ι := by
    rw [coordinateBaseChange_over, hw₁]
  calc (genericSliceBase x hb).hom.trdegAt y + 1 ≤ e.trdegAt y₁ + π.trdegAt (e y₁) :=
        add_le_add h₁ h₂
    _ = (e ≫ π).trdegAt y₁ := by rw [Scheme.Hom.trdegAt_comp, add_comm]
    _ = (pullback.snd X₁.hom ι).trdegAt (w y₁) := by
        rw [Scheme.Hom.trdegAt_congr h₃, Scheme.Hom.trdegAt_comp_of_isPreimmersion]
    _ ≤ _ := Scheme.Pullback.trdegAt_snd_le _

/-- **The measure drops along generic slices**: for a trait model `M` over the generic base of an
`F`-scheme `X₁` of finite type, a coordinate `b` and `x ∈ K` transcendental over `k'`, the base
`X₂ = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧` of the generic slice satisfies `μ X₂ + 1 ≤ μ X₁`, unless it
is empty. -/
theorem IsTraitModelOfGenericBase.genericBaseMeasure_genericSliceBase_add_one_le
    [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (hx : Transcendental k' x) :
    genericBaseMeasure (genericSliceBase x hb) + 1 ≤ genericBaseMeasure X₁ ∨
      IsEmpty (genericSliceBase x hb).left := by
  rcases isEmpty_or_nonempty (genericSliceBase x hb).left with h | ⟨⟨y₀⟩⟩
  · exact Or.inr h
  refine Or.inl ?_
  have key (y : (genericSliceBase x hb).left) :
      ((genericSliceBase x hb).hom.trdegAt y).toNat + 1 ≤ genericBaseMeasure X₁ := by
    obtain ⟨z, hz⟩ := hM.exists_trdegAt_genericSliceBase_add_one_le hb hx y
    have h := hz.trans (trdegAt_le_genericBaseMeasure X₁ z)
    have hc : (genericSliceBase x hb).hom.trdegAt y < Cardinal.aleph0 :=
      (le_self_add.trans h).trans_lt Cardinal.natCast_lt_aleph0
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hc] at h
    exact_mod_cast h
  have h₀ := key y₀
  have : genericBaseMeasure (genericSliceBase x hb) ≤ genericBaseMeasure X₁ - 1 :=
    ciSup_le' fun y ↦ by
      have := key y
      omega
  omega

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
