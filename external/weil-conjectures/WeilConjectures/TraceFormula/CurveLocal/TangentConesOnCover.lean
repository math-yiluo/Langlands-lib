/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverProperties
public import WeilConjectures.TraceFormula.CurveLocal.CoverPiFinite
public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedDiagonalProduct
public import WeilConjectures.TraceFormula.CurveLocal.ModelAxes
public import WeilConjectures.RingTheory.MiracleFlatness
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Tangent cones on the cover

For a cover datum `D` of a curve local model `M`, the surface `T'` is the strict localization of
the smooth surface `S' = C ×_k C` at the `k`-point `s' = (c, c)`, and `π : T' ⟶ T` is induced by
`p × p`. This file assembles blueprint `lemma-tangent-cones-on-cover`:

* `S'` is smooth of relative dimension two over `k` and `s'` is a `k`-point;
* `π` is finite and flat (miracle flatness: both strict local rings are regular of dimension
  two and the closed fibre is finite);
* `π` is étale over `T ∖ (H ∪ V)`, with all geometric fibres there of cardinality `e²`
  (`e` the ramification index of `C ⟶ X` at `c`, the local degree of the cover);
* `H'` is regular, and the tangent cone of `(G' ∪ V')_red` meets those of `B'` and `H'` only at
  the origin.

## Main statements

- `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.flat_π`: `π : T' ⟶ T` is flat.
- `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.etale_π_openComplement`: `π` is étale over
  `T ∖ (H ∪ V)`.
- `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.natCard_geometricFiber_π`: the geometric
  fibres of `π` over `T ∖ (H ∪ V)` have `e²` points.
- `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.free_and_finrank_π`: `π` is finite free of
  degree `e²`.
- `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.tangentConesOnCover`: the assembled
  statement of blueprint `lemma-tangent-cones-on-cover`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

/-- A regular local ring of dimension `d` has depth at least `d`. -/
private theorem IsRegularLocalRing.natCast_le_depth' (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (d : ℕ) (hd : ringKrullDim S = (d : WithBot ℕ∞)) :
    (d : ℕ∞) ≤ IsLocalRing.depth (R := S) S := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (IsLocalRing.maximalIdeal S).FG from
        (IsLocalRing.maximalIdeal S).fg_of_isNoetherianRing)
  have hlen : s.toList.length = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
    rw [hd] at h
    have hsd : (IsLocalRing.maximalIdeal S).spanFinrank = d := by exact_mod_cast h
    simpa [hsd] using hcard
  have hrs : IsLocalRing.IsRegularSystemOfParameters s.toList :=
    ⟨by simpa using hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators S d hd
    s.toList hrs).1
  unfold IsLocalRing.depth Ideal.depth
  split
  · exact le_top
  · apply le_sSup
    exact ⟨s.toList, hreg, fun x hx ↦ hrs.1 ▸ Ideal.subset_span hx, by rw [hlen]⟩

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- The complement of `H ∪ V` in `T` lies in the locus where both coordinates avoid the closed
point of `X_y`. -/
lemma openComplement_hH_inf_openComplement_v_le_O₂ :
    M.hH.openComplement ⊓ M.v.openComplement ≤ M.O₂ := by
  intro z ⟨hH, hv⟩
  have hH' : z ∉ Set.range M.hH := hH
  have hv' : z ∉ Set.range M.v := hv
  rw [mem_range_hH_iff] at hH'
  rw [mem_range_v_iff] at hv'
  refine ⟨fun h ↦ hv' ?_, fun h ↦ hH' ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← M.q₁_toBase, Scheme.Hom.comp_apply,
      Set.mem_singleton_iff.mp h, strictLocalizationToBase_closedPoint]
  · rw [← Scheme.Hom.comp_apply, ← M.q₂_toBase, Scheme.Hom.comp_apply,
      Set.mem_singleton_iff.mp h, strictLocalizationToBase_closedPoint]

/-- The strict local ring of `T` is a regular local ring of dimension two. -/
lemma regular_T : IsRegularLocalRing (strictHenselization M.diagPoint) ∧
    ringKrullDim (strictHenselization M.diagPoint) = 2 := by
  have : SmoothOfRelativeDimension (1 + 1) (pullback.fst M.f M.f ≫ M.f) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) (pullback.fst M.f M.f) M.f
  obtain ⟨h₁, h₂⟩ := isRegularLocalRing_strictHenselization_of_smoothOfRelativeDimension _ (1 + 1)
    M.diagPoint (by rw [← Category.assoc, diagPoint_fst, M.y_comp])
  exact ⟨h₁, by rw [h₂]; rfl⟩

namespace CoverDatum

variable {M} {ℓ : ℕ} {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

/-- The surface `S' = C ×_k C` is smooth of relative dimension two over `k`. -/
instance smoothOfRelativeDimension_S' :
    SmoothOfRelativeDimension 2 (pullback.fst D.fC D.fC ≫ D.fC) := by
  have : SmoothOfRelativeDimension 1 D.fC := D.smoothOfRelativeDimension
  exact smoothOfRelativeDimension_comp (n := 1) (m := 1) (pullback.fst D.fC D.fC) D.fC

omit [IsAlgClosed k] in
/-- The point `s'` of `S'` is a `k`-point. -/
lemma s'_comp_structure : D.s' ≫ pullback.fst D.fC D.fC ≫ D.fC = 𝟙 _ := by
  rw [← Category.assoc, s'_fst, c_comp_fC]

/-- The ring map of `π` on strict henselizations is local. -/
instance isLocalHom_preimage_π : IsLocalHom (Spec.preimage D.π).hom := by
  have h : Spec.preimage D.π ≫ strictHenselizationEval D.s' =
      strictHenselizationEval M.diagPoint :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, pt_π]; rfl)
  refine ⟨fun a ha ↦ (isUnit_iff_strictHenselizationEval_ne_zero a).2 ?_⟩
  rw [← h, CommRingCat.comp_apply]
  exact (ha.map (strictHenselizationEval D.s').hom).ne_zero

/-- **`π : T' ⟶ T` is flat** (blueprint `lemma-tangent-cones-on-cover`): it is a finite local
homomorphism of regular local rings of dimension two (miracle flatness). -/
theorem flat_π : Flat D.π := by
  set φ := Spec.preimage D.π
  have hπ : D.π = Spec.map φ := (Spec.map_preimage _).symm
  rw [hπ, HasRingHomProperty.Spec_iff (P := @Flat)]
  obtain ⟨hR, hRd⟩ := M.regular_T
  obtain ⟨hS, hSd⟩ := D.regular
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, ← hπ]
    infer_instance
  refine RingHom.flat_of_regular_of_depth_ge φ.hom 2 hSd
    (IsRegularLocalRing.natCast_le_depth' _ 2 hSd) ?_
  let := φ.hom.toAlgebra
  have : Module.Finite (strictHenselization M.diagPoint) (strictHenselization D.s') := hfin
  set p := maximalIdeal (strictHenselization M.diagPoint)
  have : Module.Finite (strictHenselization M.diagPoint ⧸ p)
      (strictHenselization D.s' ⧸ p.map (algebraMap _ (strictHenselization D.s'))) :=
    Module.Finite.of_restrictScalars_finite (strictHenselization M.diagPoint) _ _
  let := Ideal.Quotient.field p
  have : IsArtinianRing
      (strictHenselization D.s' ⧸ p.map (algebraMap _ (strictHenselization D.s'))) :=
    IsArtinianRing.of_finite (strictHenselization M.diagPoint ⧸ p) _
  have hle : p.map (algebraMap _ (strictHenselization D.s')) ≤
      maximalIdeal (strictHenselization D.s') :=
    Ideal.map_le_iff_le_comap.2 fun a ha ↦ map_nonunit φ.hom a ha
  have : Nontrivial
      (strictHenselization D.s' ⧸ p.map (algebraMap _ (strictHenselization D.s'))) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have h0 : ringKrullDim
      (strictHenselization D.s' ⧸ p.map (algebraMap _ (strictHenselization D.s'))) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance
  change _ = _ + ringKrullDim
    (strictHenselization D.s' ⧸ p.map (algebraMap _ (strictHenselization D.s')))
  rw [h0, hSd, hRd, add_zero]

/-- **`π` is étale over `T ∖ (H ∪ V)`** (blueprint `lemma-tangent-cones-on-cover`). -/
instance etale_π_openComplement :
    Etale ((D.π ⁻¹ᵁ (M.hH.openComplement ⊓ M.v.openComplement)).ι ≫ D.π) :=
  etale_comp_ι_of_le D.π (V := D.π ⁻¹ᵁ M.O₂)
    (fun _ hz ↦ M.openComplement_hH_inf_openComplement_v_le_O₂ hz)

/-- **The degree of `π`** (blueprint `lemma-tangent-cones-on-cover`): every geometric fibre of
`π` over a geometric point of `T ∖ (H ∪ V)` has `e²` points. -/
theorem natCard_geometricFiber_π {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ M.T) (hz : z default ∈ M.hH.openComplement ⊓ M.v.openComplement) :
    Nat.card (D.π.GeometricFiber z) = D.e ^ 2 := by
  have hO := M.openComplement_hH_inf_openComplement_v_le_O₂ hz
  rw [Nat.card_congr (D.geometricFiberπEquiv z), Nat.card_prod, sq]
  congr 1
  · exact D.natCard_geometricFiber_ρ _ hO.1
  · exact D.natCard_geometricFiber_ρ _ hO.2

/-- **`π` is finite free of degree `e²`** (blueprint `lemma-tangent-cones-on-cover`): the strict
local ring of `T'` is a free module of rank `e²` over that of `T`. The rank is computed from the
geometric fibre over a point of `T ∖ (H ∪ V)`, namely the image of a point of the diagonal `B'`
other than the closed point. -/
theorem free_and_finrank_π :
    letI := (Spec.preimage D.π).hom.toAlgebra
    Module.Free (strictHenselization M.diagPoint) (strictHenselization D.s') ∧
      Module.finrank (strictHenselization M.diagPoint) (strictHenselization D.s') = D.e ^ 2 := by
  set φ := Spec.preimage D.π
  have hφ : Spec.map φ = D.π := Spec.map_preimage _
  let := φ.hom.toAlgebra
  have : Module.Finite (strictHenselization M.diagPoint) (strictHenselization D.s') := by
    have : φ.hom.Finite := by
      rw [← IsFinite.SpecMap_iff, hφ]
      infer_instance
    exact this
  have : Module.Flat (strictHenselization M.diagPoint) (strictHenselization D.s') := by
    have : φ.hom.Flat := by
      rw [← Flat.SpecMap_iff, hφ]
      exact D.flat_π
    exact this
  have : Module.Free (strictHenselization M.diagPoint) (strictHenselization D.s') :=
    Module.free_of_flat_of_isLocalRing
  refine ⟨this, ?_⟩
  obtain ⟨P, hPb, hP⟩ := D.exists_mem_b_ne_closedPoint
  have h := D.p_fst_eq_p_snd_of_mem_b hPb
  have hz₀ : D.π P ∈ M.hH.openComplement ⊓ M.v.openComplement :=
    ⟨fun hH ↦ hP (D.eq_closedPoint (h.trans (D.p_snd_of_mem_hH hH)) (D.p_snd_of_mem_hH hH)),
      fun hv ↦ hP (D.eq_closedPoint (D.p_fst_of_mem_v hv) (h.symm.trans (D.p_fst_of_mem_v hv)))⟩
  generalize D.π P = x at hz₀
  let z := M.T.algClosurePoint x
  have hrange : Set.range z.base ⊆ (M.hH.openComplement ⊓ M.v.openComplement : M.T.Opens) := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.algClosurePoint_base]
    exact hz₀
  rw [← D.natCard_geometricFiber_π z (hrange ⟨_, rfl⟩)]
  obtain ⟨ζ, hζ⟩ : ∃ ζ, Spec.map ζ = z := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have het := etale_pullback_snd_of_range D.π _ z hrange
  rw [← hφ, ← hζ] at het
  have het' : Etale (pullback.fst (Spec.map ζ) (Spec.map φ)) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  rw [← hζ, ← hφ]
  exact (Scheme.Hom.natCard_geometricFiber_Spec_map_eq_finrank
    (R := strictHenselization M.diagPoint) (S := strictHenselization D.s') ζ.hom het').symm

/-- **Tangent cones on the cover** (blueprint `lemma-tangent-cones-on-cover`): `T'` is the strict
localization of the smooth surface `S' = C ×_k C` at the `k`-point `s'`; the morphism
`π : T' ⟶ T` is finite and flat, étale over `T ∖ (H ∪ V)` with geometric fibres there of
cardinality `e²`; `H'` is regular; and the tangent cone of `(G' ∪ V')_red` meets the tangent
cones of `B'` and of `H'` only at the origin. -/
theorem tangentConesOnCover :
    SmoothOfRelativeDimension 2 (pullback.fst D.fC D.fC ≫ D.fC) ∧
      D.s' ≫ pullback.fst D.fC D.fC ≫ D.fC = 𝟙 _ ∧
      IsFinite D.π ∧ Flat D.π ∧
      Etale ((D.π ⁻¹ᵁ (M.hH.openComplement ⊓ M.v.openComplement)).ι ≫ D.π) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ M.T),
        z default ∈ M.hH.openComplement ⊓ M.v.openComplement →
        Nat.card (D.π.GeometricFiber z) = D.e ^ 2) ∧
      (∃ _ : IsDomain Γ(D.H', ⊤), IsDiscreteValuationRing Γ(D.H', ⊤)) ∧
      IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dB') ∧
      IsLocalRing.TangentConesMeetAtOrigin (strictHenselization D.s') (specIdeal D.dD')
        (specIdeal D.dH') :=
  ⟨inferInstance, D.s'_comp_structure, inferInstance, D.flat_π, inferInstance,
    fun _ _ _ z hz ↦ D.natCard_geometricFiber_π z hz, D.isDiscreteValuationRing_H',
    D.tangentConesMeetAtOrigin.1, D.tangentConesMeetAtOrigin.2⟩

end CoverDatum

end AlgebraicGeometry.Etale.CurveLocalModel
