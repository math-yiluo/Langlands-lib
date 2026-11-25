/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedImmersionLiftReduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedDiagonalProduct
public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedFactors

/-!

# The punctured diagonal of `T'`

For a cover datum (blueprint `lemma-tangent-cones-on-cover` (ii)), the punctured diagonal
`B' ∖ y'` is finite étale of degree `e²` over `B ∖ y`
(`AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum.exists_puncturedDiagonal_finite_etale'`):

* the diagonal `B` of `T` is the strict localization `X_y` of the curve (`CurveLocalModel.bX`), in
  particular it is reduced;
* `B'` maps to `B` (`CoverDatum.πB`), and `B' ∖ D'` is identified with the fibre product
  `T' ×_T (B ∖ Y)` (`CoverDatum.isIso_α`): the fibre product is étale over the reduced scheme
  `B ∖ Y`, as `π` is étale over the locus where both coordinates avoid `y`, hence reduced, so it
  factors through the reduced inverse image `B'`;
* the geometric fibres of `π` over points of `B ∖ Y` are products of two geometric fibres of the
  strictly local cover `ρ : C_c ⟶ X_y` over its generic point, of `e` points each.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- The strict localization `X_y` maps to the diagonal `B` of `T`. -/
noncomputable def bX : M.Xy ⟶ M.B :=
  pullback.lift (strictLocalizationToBase M.y)
    (strictLocalizationMap (pullback.diagonal M.f) M.y ≫ eqToHom (by rw [M.y_comp_diagonal]))
    (by rw [Category.assoc, CoverDatum.eqToHom_comp_strictLocalizationToBase M.y_comp_diagonal,
      strictLocalizationMap_comp_strictLocalizationToBase])

@[reassoc (attr := simp)]
lemma bX_fst : M.bX ≫ pullback.fst (pullback.diagonal M.f) M.τ = strictLocalizationToBase M.y :=
  pullback.lift_fst _ _ _

lemma pt_bX : Spec.map (strictHenselizationEval M.y) ≫ M.bX = M.tB := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bX_fst, spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
      tB, pullback.lift_fst]
  · rw [Category.assoc, bX, pullback.lift_snd, ← Category.assoc,
      spec_map_strictHenselizationEval_comp_strictLocalizationMap,
      CoverDatum.spec_map_strictHenselizationEval_comp_eqToHom M.y_comp_diagonal, tB_comp_b]
    rfl

/-- **The diagonal `B` is the strict localization of the curve** at `y`. -/
instance isIso_bX : IsIso M.bX := by
  obtain ⟨κ, hκ, hpκ⟩ := exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing M.y
    (M.B.isoSpec.inv ≫ pullback.fst _ _) (M.tB ≫ M.B.isoSpec.hom)
    M.isoSpec_hom_tB_apply_closedPoint (by
      rw [Category.assoc, Iso.hom_inv_id_assoc, tB, pullback.lift_fst])
  simp only [Category.assoc] at hpκ
  have h₁ : M.bX ≫ M.B.isoSpec.hom ≫ κ = 𝟙 _ := by
    refine hom_strictLocalization_ext M.y ?_ (Spec.map (strictHenselizationEval M.y))
      (closedPoint k) (spec_map_strictHenselizationEval_apply _ _) ?_
    · rw [Category.assoc, Category.assoc, hκ, Iso.hom_inv_id_assoc, bX_fst, Category.id_comp]
    · rw [reassoc_of% M.pt_bX, hpκ, Category.comp_id]
  have h₂ : κ ≫ M.bX = M.B.isoSpec.inv := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bX_fst, hκ]
    · refine hom_strictLocalization_ext M.diagPoint ?_ (M.tB ≫ M.B.isoSpec.hom) (closedPoint k)
        M.isoSpec_hom_tB_apply_closedPoint ?_
      · rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% bX_fst,
          reassoc_of% hκ, pullback.condition,
          Category.assoc]
      · simp only [Category.assoc]
        rw [reassoc_of% hpκ, reassoc_of% M.pt_bX, Iso.hom_inv_id_assoc]
  exact ⟨M.B.isoSpec.hom ≫ κ, h₁, by rw [Category.assoc, h₂, Iso.hom_inv_id]⟩

/-- The diagonal `B` of `T` is reduced. -/
instance isReduced_B : IsReduced M.B := by
  have hreg := isRegularLocalRing_strictHenselization_of_smoothOfRelativeDimension M.f 1 M.y
    M.y_comp
  have := hreg.1
  exact isReduced_of_isOpenImmersion (inv M.bX)

/-- A point of `B ∖ Y` lies, in `T`, in the locus where both coordinates avoid `y`. -/
lemma b_mem_O₂ (z : M.B) (hz : z ∈ M.yB.openComplement) :
    M.b z ∈ M.O₂ := by
  have hv : M.b z ∉ Set.range M.v := (M.openComplement_yB_le_preimage_O hz).2
  rw [mem_range_v_iff] at hv
  have e₁ : M.b ≫ M.τ ≫ pullback.fst M.f M.f = pullback.fst _ _ := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  have e₂ : M.b ≫ M.τ ≫ pullback.snd M.f M.f = pullback.fst _ _ := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, pullback.diagonal_snd,
      Category.comp_id]
  have hdiag : (pullback.fst M.f M.f) (M.τ (M.b z)) = (pullback.snd M.f M.f) (M.τ (M.b z)) := by
    have h := congrArg (fun f : M.B ⟶ M.X ↦ f z) (e₁.trans e₂.symm)
    simpa only [Scheme.Hom.comp_apply] using h
  refine ⟨fun h ↦ hv ?_, fun h ↦ hv ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← M.q₁_toBase, Scheme.Hom.comp_apply,
      Set.mem_singleton_iff.mp h, strictLocalizationToBase_closedPoint]
  · rw [hdiag, ← Scheme.Hom.comp_apply, ← M.q₂_toBase, Scheme.Hom.comp_apply,
      Set.mem_singleton_iff.mp h, strictLocalizationToBase_closedPoint]

namespace CoverDatum

variable {M} {ℓ : ℕ} {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

lemma range_dB' : Set.range D.dB' = D.π ⁻¹' Set.range M.b := by
  rw [range_reducedClosedι, (D.isClosed_preimage_range M.b).closure_eq]

lemma range_dD' : Set.range D.dD' = D.π ⁻¹' (Set.range M.a ∪ Set.range M.v) := by
  rw [range_reducedClosedι, Set.preimage_union,
    ((D.isClosed_preimage_range M.a).union (D.isClosed_preimage_range M.v)).closure_eq]

/-- The morphism `B' ⟶ B` induced by `π`. -/
noncomputable def πB : D.B' ⟶ M.B :=
  IsClosedImmersion.lift M.b (D.dB' ≫ D.π) (ker_le_ker_of_isReduced M.b _ (by
    rintro _ ⟨x, rfl⟩
    have : D.dB' x ∈ D.π ⁻¹' Set.range M.b := D.range_dB' ▸ ⟨x, rfl⟩
    exact this))

@[reassoc (attr := simp)]
lemma πB_b : D.πB ≫ M.b = D.dB' ≫ D.π :=
  IsClosedImmersion.lift_fac _ _ _

/-- The punctured diagonal `B' ∖ D'`. -/
noncomputable abbrev B'o : D.B'.Opens := D.dB' ⁻¹ᵁ D.dD'.openComplement

lemma B'o_le : D.B'o ≤ D.πB ⁻¹ᵁ M.yB.openComplement := by
  rintro x hx ⟨y', hy'⟩
  apply hx
  rw [D.range_dD']
  left
  refine ⟨pullback.fst M.a M.b y', ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hy',
    ← Scheme.Hom.comp_apply, πB_b, Scheme.Hom.comp_apply]

/-- The restriction `B' ∖ D' ⟶ B ∖ Y` of `πB`. -/
noncomputable def πUo : D.B'o.toScheme ⟶ M.yB.openComplement.toScheme :=
  D.πB.resLE _ _ D.B'o_le

@[reassoc (attr := simp)]
lemma πUo_ι : D.πUo ≫ M.yB.openComplement.ι = D.B'o.ι ≫ D.πB :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The fibre product `F = T' ×_T (B ∖ Y)`. -/
noncomputable abbrev F : Scheme.{u} := pullback D.π (M.yB.openComplement.ι ≫ M.b)

lemma range_ι_b_subset : Set.range (M.yB.openComplement.ι ≫ M.b) ⊆ M.O₂ := by
  rintro _ ⟨z, rfl⟩
  exact M.b_mem_O₂ _ z.2

instance : Etale (pullback.snd D.π (M.yB.openComplement.ι ≫ M.b)) :=
  etale_pullback_snd_of_range D.π M.O₂ _ (range_ι_b_subset (M := M))

instance : IsReduced D.F :=
  isReduced_of_etale (pullback.snd D.π (M.yB.openComplement.ι ≫ M.b))

/-- The comparison morphism `B' ∖ D' ⟶ T' ×_T (B ∖ Y)`. -/
noncomputable def α : D.B'o.toScheme ⟶ D.F :=
  pullback.lift (D.B'o.ι ≫ D.dB') D.πUo (by simp)

@[reassoc (attr := simp)]
lemma α_fst : D.α ≫ pullback.fst _ _ = D.B'o.ι ≫ D.dB' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma α_snd : D.α ≫ pullback.snd _ _ = D.πUo :=
  pullback.lift_snd _ _ _

/-- The inverse `T' ×_T (B ∖ Y) ⟶ B' ∖ D'`: the reduced fibre product factors through `B'`. -/
lemma exists_β : ∃ β : D.F ⟶ D.B'o.toScheme,
    β ≫ D.B'o.ι ≫ D.dB' = pullback.fst D.π (M.yB.openComplement.ι ≫ M.b) := by
  have hrange (w : D.F) : D.π (pullback.fst D.π (M.yB.openComplement.ι ≫ M.b) w) =
      M.b ((pullback.snd D.π (M.yB.openComplement.ι ≫ M.b) w).1) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    rfl
  let γ₁ := IsClosedImmersion.lift D.dB' (pullback.fst D.π (M.yB.openComplement.ι ≫ M.b))
    (ker_le_ker_of_isReduced D.dB' _ (by
      rintro _ ⟨w, rfl⟩
      rw [D.range_dB', Set.mem_preimage, hrange]
      exact ⟨_, rfl⟩))
  have hγ₁ : γ₁ ≫ D.dB' = pullback.fst _ _ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift D.B'o.ι γ₁ ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [Opens.range_ι]
    have hO := M.openComplement_yB_le_preimage_O
      (pullback.snd D.π (M.yB.openComplement.ι ≫ M.b) w).2
    rintro hmem
    rw [← Scheme.Hom.comp_apply, hγ₁, D.range_dD', Set.mem_preimage, hrange] at hmem
    rcases hmem with h | h
    · exact hO.1 h
    · exact hO.2 h
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, hγ₁]

instance isIso_α : IsIso D.α := by
  obtain ⟨β, hβ⟩ := D.exists_β
  have hmono : Mono (D.B'o.ι ≫ D.dB') := inferInstance
  refine ⟨β, ?_, ?_⟩
  · rw [← cancel_mono (D.B'o.ι ≫ D.dB'), Category.assoc, hβ, α_fst, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, α_fst, hβ, Category.id_comp]
    · rw [← cancel_mono (M.yB.openComplement.ι ≫ M.b)]
      simp only [Category.assoc, Category.id_comp, α_snd_assoc, πUo_ι_assoc, πB_b]
      rw [reassoc_of% hβ, pullback.condition]

/-- **The punctured diagonal** (blueprint `lemma-tangent-cones-on-cover` (ii)): `B' ∖ y'` is
finite étale of degree `e²` over `B ∖ y`, compatibly with the inclusions into `T' ∖ D'` and
`T ∖ (G ∪ V)`. -/
theorem exists_puncturedDiagonal_finite_etale' :
    ∃ (πU : (D.dB' ⁻¹ᵁ D.dD'.openComplement).toScheme ⟶ M.yB.openComplement.toScheme)
      (_ : IsFinite πU) (_ : Etale πU),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ M.yB.openComplement.toScheme),
        Nat.card (πU.GeometricFiber s) = D.e ^ 2) ∧
      πU ≫ M.ψ ≫ M.O.ι =
        D.dB'.resLE D.dD'.openComplement (D.dB' ⁻¹ᵁ D.dD'.openComplement) le_rfl ≫
          D.dD'.openComplement.ι ≫ D.π := by
  refine ⟨D.α ≫ pullback.snd _ _, inferInstance, inferInstance, fun Ω _ _ s ↦ ?_, ?_⟩
  · rw [Nat.card_congr ((Scheme.Hom.geometricFiberCompIsoEquiv _ _ s).trans
      ((Scheme.Hom.GeometricFiber.pullbackEquiv _ _ s).trans (D.geometricFiberπEquiv _))),
      Nat.card_prod, sq]
    have hO := M.b_mem_O₂ _ (s default).2
    congr 1
    · exact D.natCard_geometricFiber_ρ _ hO.1
    · exact D.natCard_geometricFiber_ρ _ hO.2
  · rw [Category.assoc, ψ_comp_ι, ← pullback.condition,
      α_fst_assoc, Scheme.Hom.resLE_comp_ι_assoc]

end CoverDatum

end AlgebraicGeometry.Etale.CurveLocalModel
