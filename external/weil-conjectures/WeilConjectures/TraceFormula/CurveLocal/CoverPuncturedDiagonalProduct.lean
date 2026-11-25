/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedDiagonalLocal
public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing

/-!

# The surface `T'` as a product of strictly local covers

For a cover datum, let `ρ : C_c ⟶ X_y` be the strictly local cover of
`WeilConjectures.TraceFormula.CurveLocal.CoverPuncturedDiagonalLocal` and `q₁, q₂ : T ⟶ X_y`
the maps induced by the projections. The fibre product
`Q = (C_c ×_{X_y, q₁} T) ×_T (C_c ×_{X_y, q₂} T)` is finite over `T` with a single point over
the closed point, hence it is the spectrum of a strictly henselian local ring, and the universal
property of the strict localization identifies `T'` with `Q` over `T`
(`CoverDatum.isIso_φQ`). Consequently:

* the geometric fibre of `π : T' ⟶ T` over `z` is the product of the geometric fibres of `ρ` over
  `z ≫ q₁` and `z ≫ q₂` (`CoverDatum.geometricFiberπEquiv`);
* `π` is étale over the locus where both `q₁` and `q₂` avoid the closed point of `X_y`
  (`CoverDatum.etale_π`).

This is the local structure behind blueprint `lemma-tangent-cones-on-cover` (ii): `T'` is finite
flat of rank `e²` over `T`, étale away from `H ∪ V`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
lemma diagPoint_fst : M.diagPoint ≫ pullback.fst M.f M.f = M.y :=
  pullback.lift_fst _ _ _

omit [IsAlgClosed k] in
lemma diagPoint_snd : M.diagPoint ≫ pullback.snd M.f M.f = M.y :=
  pullback.lift_snd _ _ _

/-- The map `q₁ : T ⟶ X_y` induced by the first projection. -/
noncomputable def q₁ : M.T ⟶ M.Xy :=
  strictLocalizationMap (pullback.fst M.f M.f) M.diagPoint ≫ eqToHom (by rw [M.diagPoint_fst])

/-- The map `q₂ : T ⟶ X_y` induced by the second projection. -/
noncomputable def q₂ : M.T ⟶ M.Xy :=
  strictLocalizationMap (pullback.snd M.f M.f) M.diagPoint ≫ eqToHom (by rw [M.diagPoint_snd])

@[reassoc]
lemma q₁_toBase : M.q₁ ≫ strictLocalizationToBase M.y = M.τ ≫ pullback.fst M.f M.f := by
  rw [q₁, Category.assoc, CoverDatum.eqToHom_comp_strictLocalizationToBase M.diagPoint_fst,
    strictLocalizationMap_comp_strictLocalizationToBase]

@[reassoc]
lemma q₂_toBase : M.q₂ ≫ strictLocalizationToBase M.y = M.τ ≫ pullback.snd M.f M.f := by
  rw [q₂, Category.assoc, CoverDatum.eqToHom_comp_strictLocalizationToBase M.diagPoint_snd,
    strictLocalizationMap_comp_strictLocalizationToBase]

@[reassoc]
lemma t_q₁ : M.t ≫ M.q₁ = Spec.map (strictHenselizationEval M.y) := by
  rw [t, q₁, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
    CoverDatum.spec_map_strictHenselizationEval_comp_eqToHom M.diagPoint_fst]

@[reassoc]
lemma t_q₂ : M.t ≫ M.q₂ = Spec.map (strictHenselizationEval M.y) := by
  rw [t, q₂, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
    CoverDatum.spec_map_strictHenselizationEval_comp_eqToHom M.diagPoint_snd]

/-- The locus of `T` where both coordinates avoid the closed point of `X_y`. -/
noncomputable def O₂ : M.T.Opens := M.q₁ ⁻¹ᵁ M.Xyo ⊓ M.q₂ ⁻¹ᵁ M.Xyo

namespace CoverDatum

variable {M} {ℓ : ℕ} {Λ : Type (u + 1)} [CommRing Λ]
  {PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
  (D : M.CoverDatum ℓ PL PK)

/-- The map `r₁ : T' ⟶ C_c` induced by the first projection. -/
noncomputable def r₁ : D.T' ⟶ D.Cc :=
  strictLocalizationMap (pullback.fst D.fC D.fC) D.s' ≫ eqToHom (by rw [D.s'_fst])

/-- The map `r₂ : T' ⟶ C_c` induced by the second projection. -/
noncomputable def r₂ : D.T' ⟶ D.Cc :=
  strictLocalizationMap (pullback.snd D.fC D.fC) D.s' ≫ eqToHom (by rw [D.s'_snd])

@[reassoc]
lemma r₁_toBase : D.r₁ ≫ strictLocalizationToBase D.c =
    strictLocalizationToBase D.s' ≫ pullback.fst D.fC D.fC := by
  rw [r₁, Category.assoc, eqToHom_comp_strictLocalizationToBase D.s'_fst,
    strictLocalizationMap_comp_strictLocalizationToBase]

@[reassoc]
lemma r₂_toBase : D.r₂ ≫ strictLocalizationToBase D.c =
    strictLocalizationToBase D.s' ≫ pullback.snd D.fC D.fC := by
  rw [r₂, Category.assoc, eqToHom_comp_strictLocalizationToBase D.s'_snd,
    strictLocalizationMap_comp_strictLocalizationToBase]

@[reassoc]
lemma pt_r₁ : Spec.map (strictHenselizationEval D.s') ≫ D.r₁ =
    Spec.map (strictHenselizationEval D.c) := by
  rw [r₁, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
    spec_map_strictHenselizationEval_comp_eqToHom D.s'_fst]

@[reassoc]
lemma pt_r₂ : Spec.map (strictHenselizationEval D.s') ≫ D.r₂ =
    Spec.map (strictHenselizationEval D.c) := by
  rw [r₂, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
    spec_map_strictHenselizationEval_comp_eqToHom D.s'_snd]

@[reassoc]
lemma pt_π : Spec.map (strictHenselizationEval D.s') ≫ D.π = M.t := by
  rw [π, ← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
    spec_map_strictHenselizationEval_comp_eqToHom D.s'_comp_g]
  rfl

@[reassoc]
lemma r₁_ρ : D.r₁ ≫ D.ρ = D.π ≫ M.q₁ := by
  refine hom_strictLocalization_ext M.y ?_ (Spec.map (strictHenselizationEval D.s'))
    (closedPoint k) (spec_map_strictHenselizationEval_apply _ _) ?_
  · rw [Category.assoc, ρ_comp_toBase, r₁_toBase_assoc, Category.assoc, M.q₁_toBase,
      ← Category.assoc D.π, π_comp_τ, Category.assoc, g_fst]
  · rw [pt_r₁_assoc, pt_comp_ρ, pt_π_assoc, M.t_q₁]

@[reassoc]
lemma r₂_ρ : D.r₂ ≫ D.ρ = D.π ≫ M.q₂ := by
  refine hom_strictLocalization_ext M.y ?_ (Spec.map (strictHenselizationEval D.s'))
    (closedPoint k) (spec_map_strictHenselizationEval_apply _ _) ?_
  · rw [Category.assoc, ρ_comp_toBase, r₂_toBase_assoc, Category.assoc, M.q₂_toBase,
      ← Category.assoc D.π, π_comp_τ, Category.assoc, g_snd]
  · rw [pt_r₂_assoc, pt_comp_ρ, pt_π_assoc, M.t_q₂]

/-- The fibre product `Q = (C_c ×_{X_y} T) ×_T (C_c ×_{X_y} T)` over `T` of the base changes of
`ρ` along `q₁` and `q₂`. -/
noncomputable abbrev Q : Scheme.{u} :=
  pullback (pullback.snd D.ρ M.q₁) (pullback.snd D.ρ M.q₂)

/-- The structure morphism `Q ⟶ T`. -/
noncomputable abbrev hQ : D.Q ⟶ M.T :=
  pullback.fst (pullback.snd D.ρ M.q₁) (pullback.snd D.ρ M.q₂) ≫ pullback.snd D.ρ M.q₁

lemma hQ_eq : D.hQ =
    pullback.snd (pullback.snd D.ρ M.q₁) (pullback.snd D.ρ M.q₂) ≫ pullback.snd D.ρ M.q₂ :=
  pullback.condition

/-- The comparison morphism `T' ⟶ Q`. -/
noncomputable def φQ : D.T' ⟶ D.Q :=
  pullback.lift (pullback.lift D.r₁ D.π D.r₁_ρ) (pullback.lift D.r₂ D.π D.r₂_ρ) (by simp)

@[reassoc (attr := simp)]
lemma φQ_hQ : D.φQ ≫ D.hQ = D.π := by
  rw [φQ, hQ, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The morphism `Q ⟶ C ×_k C`. -/
noncomputable def γ : D.Q ⟶ D.S' :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst D.ρ M.q₁ ≫ strictLocalizationToBase D.c)
    (pullback.snd _ _ ≫ pullback.fst D.ρ M.q₂ ≫ strictLocalizationToBase D.c) (by
      have h₁ : pullback.fst D.ρ M.q₁ ≫ strictLocalizationToBase D.c ≫ D.fC =
          pullback.snd D.ρ M.q₁ ≫ M.τ ≫ pullback.snd M.f M.f ≫ M.f := by
        rw [← D.p_comp, ← ρ_comp_toBase_assoc, pullback.condition_assoc, M.q₁_toBase_assoc,
          pullback.condition (f := M.f) (g := M.f)]
      have h₂ : pullback.fst D.ρ M.q₂ ≫ strictLocalizationToBase D.c ≫ D.fC =
          pullback.snd D.ρ M.q₂ ≫ M.τ ≫ pullback.snd M.f M.f ≫ M.f := by
        rw [← D.p_comp, ← ρ_comp_toBase_assoc, pullback.condition_assoc, M.q₂_toBase_assoc]
      simp only [Category.assoc]
      rw [h₁, h₂, pullback.condition_assoc])

@[reassoc (attr := simp)]
lemma γ_fst : D.γ ≫ pullback.fst D.fC D.fC =
    pullback.fst _ _ ≫ pullback.fst D.ρ M.q₁ ≫ strictLocalizationToBase D.c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma γ_snd : D.γ ≫ pullback.snd D.fC D.fC =
    pullback.snd _ _ ≫ pullback.fst D.ρ M.q₂ ≫ strictLocalizationToBase D.c :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma φQ_γ : D.φQ ≫ D.γ = strictLocalizationToBase D.s' := by
  apply pullback.hom_ext
  · simp [φQ, r₁_toBase]
  · simp [φQ, r₂_toBase]

@[reassoc]
lemma γ_g : D.γ ≫ D.g = D.hQ ≫ M.τ := by
  apply pullback.hom_ext
  · rw [Category.assoc, g_fst, γ_fst_assoc, ← ρ_comp_toBase, pullback.condition_assoc,
      M.q₁_toBase, Category.assoc, Category.assoc]
  · rw [Category.assoc, g_snd, γ_snd_assoc, ← ρ_comp_toBase, pullback.condition_assoc,
      M.q₂_toBase, hQ_eq, Category.assoc, Category.assoc]

instance : IsFinite D.hQ := by
  unfold hQ
  infer_instance

/-- The geometric fibre of `Q ⟶ T` is the product of the geometric fibres of `ρ` over the two
coordinates. -/
noncomputable def geometricFiberHQEquiv {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ M.T) :
    D.hQ.GeometricFiber z ≃ D.ρ.GeometricFiber (z ≫ M.q₁) × D.ρ.GeometricFiber (z ≫ M.q₂) :=
  (Scheme.Hom.geometricFiberPullbackEquiv _ _ z).trans
    ((Scheme.Hom.GeometricFiber.pullbackEquiv D.ρ M.q₁ z).prodCongr
      (Scheme.Hom.GeometricFiber.pullbackEquiv D.ρ M.q₂ z))

instance : Subsingleton (D.hQ.GeometricFiber M.t) := by
  refine (D.geometricFiberHQEquiv M.t).subsingleton_congr.mpr ⟨fun x y ↦ ?_⟩
  have h (x : D.ρ.GeometricFiber (M.t ≫ M.q₁)) : x.1 = Spec.map (strictHenselizationEval D.c) :=
    D.geometricFiber_ρ_eq ⟨x.1, x.2.trans M.t_q₁⟩
  have h' (x : D.ρ.GeometricFiber (M.t ≫ M.q₂)) : x.1 = Spec.map (strictHenselizationEval D.c) :=
    D.geometricFiber_ρ_eq ⟨x.1, x.2.trans M.t_q₂⟩
  exact Prod.ext (Subtype.ext ((h _).trans (h _).symm)) (Subtype.ext ((h' _).trans (h' _).symm))

/-- `Q` has a single point over the closed point of `T`. -/
lemma eq_of_hQ_eq_closedPoint {w w' : D.Q}
    (hw : D.hQ w = closedPoint (strictHenselization M.diagPoint))
    (hw' : D.hQ w' = closedPoint (strictHenselization M.diagPoint)) : w = w' := by
  have ht : M.t default = closedPoint (strictHenselization M.diagPoint) := by
    rw [← M.t_apply_closedPoint]
    exact congrArg _ (Subsingleton.elim _ _)
  obtain ⟨x, rfl⟩ := Scheme.Hom.GeometricFiber.exists_apply_default_eq D.hQ M.t w (hw.trans ht.symm)
  obtain ⟨x', rfl⟩ := Scheme.Hom.GeometricFiber.exists_apply_default_eq D.hQ M.t w'
    (hw'.trans ht.symm)
  rw [Subsingleton.elim x x']

/-- The closed points of `Q` lie over the closed point of `T`. -/
lemma hQ_eq_closedPoint_of_isClosed {w : D.Q} (hw : IsClosed ({w} : Set D.Q)) :
    D.hQ w = closedPoint (strictHenselization M.diagPoint) := by
  refine IsLocalRing.eq_closedPoint_of_isClosed ?_
  have := D.hQ.isClosedMap _ hw
  rwa [Set.image_singleton] at this

/-- The image in `Q` of the closed point of `T'`. -/
noncomputable abbrev w₀ : D.Q := D.φQ (closedPoint (strictHenselization D.s'))

lemma hQ_w₀ : D.hQ D.w₀ = closedPoint (strictHenselization M.diagPoint) := by
  rw [← Scheme.Hom.comp_apply, φQ_hQ, ← spec_map_strictHenselizationEval_apply D.s'
    (closedPoint k), ← Scheme.Hom.comp_apply, pt_π, M.t_apply_closedPoint]

instance : IsAffine D.Q := isAffine_of_isAffineHom D.hQ

/-- The point `w₀` is the unique closed point of `Q`. -/
lemma isClosed_w₀ : IsClosed ({D.w₀} : Set D.Q) := by
  obtain ⟨w₁, hw₁, hcl⟩ := (isClosed_closure (s := ({D.w₀} : Set D.Q))).exists_closed_singleton
    ⟨D.w₀, subset_closure rfl⟩
  have hsp : D.w₀ ⤳ w₁ := specializes_iff_mem_closure.mpr hw₁
  obtain rfl : w₁ = D.w₀ := D.eq_of_hQ_eq_closedPoint (D.hQ_eq_closedPoint_of_isClosed hcl) D.hQ_w₀
  exact hcl

lemma eq_w₀_of_isClosed {w : D.Q} (hw : IsClosed ({w} : Set D.Q)) : w = D.w₀ :=
  D.eq_of_hQ_eq_closedPoint (D.hQ_eq_closedPoint_of_isClosed hw) D.hQ_w₀

instance : IsLocalRing Γ(D.Q, ⊤) := by
  have : Nontrivial Γ(D.Q, ⊤) := (D.Q.presheaf.germ ⊤ D.w₀ trivial).hom.domain_nontrivial
  refine .of_unique_max_ideal ?_
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(D.Q, ⊤)
  refine ⟨m, hm, fun m' hm' ↦ ?_⟩
  have key (n : Ideal Γ(D.Q, ⊤)) (hn : n.IsMaximal) :
      D.Q.isoSpec.inv ⟨n, hn.isPrime⟩ = D.w₀ := by
    refine D.eq_w₀_of_isClosed (isClosed_singleton_of_isClosedImmersion D.Q.isoSpec.hom ?_)
    have hh := Scheme.hom_inv_apply D.Q.isoSpec.symm ⟨n, hn.isPrime⟩
    rw [Iso.symm_hom, Iso.symm_inv] at hh
    rw [hh]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hn
  have := (key m' hm').trans (key m hm).symm
  exact congrArg PrimeSpectrum.asIdeal (D.Q.isoSpec.inv.isOpenEmbedding.injective this)

/-- `Γ(Q)` is a strictly henselian local ring: it is a finite local algebra over the strictly
henselian local ring of `T`. -/
instance : IsStrictlyHenselianLocalRing Γ(D.Q, ⊤) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = D.Q.isoSpec.inv ≫ D.hQ :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  algebraize [φ.hom]
  have := isStrictlyHenselianLocalRing_strictHenselization' M.diagPoint
  obtain ⟨e, he, he1, hsh⟩ := IsStrictlyHenselianLocalRing.exists_isIdempotentElem_quotient
    (strictHenselization M.diagPoint) Γ(D.Q, ⊤) (maximalIdeal Γ(D.Q, ⊤))
  rcases he.eq_zero_or_one_of_isLocalRing with rfl | rfl
  · exact ((maximalIdeal.isMaximal Γ(D.Q, ⊤)).ne_top ((Ideal.eq_top_iff_one
      (maximalIdeal Γ(D.Q, ⊤))).mpr (by rwa [sub_zero] at he1))).elim
  · rw [sub_self, Ideal.span_singleton_eq_bot.mpr rfl] at hsh
    exact .of_ringEquiv (RingEquiv.quotientBot _)

/-- The geometric point of `Spec Γ(Q)` over the closed point. -/
noncomputable def p₀ : Spec (.of k) ⟶ Spec Γ(D.Q, ⊤) :=
  Spec.map (strictHenselizationEval D.s') ≫ D.φQ ≫ D.Q.isoSpec.hom

lemma p₀_def : D.p₀ = Spec.map (strictHenselizationEval D.s') ≫ D.φQ ≫ D.Q.isoSpec.hom :=
  rfl

lemma p₀_closedPoint : D.p₀ (closedPoint k) = closedPoint Γ(D.Q, ⊤) := by
  refine IsLocalRing.eq_closedPoint_of_isClosed
    (isClosed_singleton_of_isClosedImmersion D.Q.isoSpec.inv ?_)
  rw [p₀_def, ← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id,
    Scheme.Hom.comp_apply, spec_map_strictHenselizationEval_apply]
  exact D.isClosed_w₀

/-- Two morphisms `Spec Γ(Q) ⟶ Q` agreeing in `C ×_k C` and at the closed point agree. -/
lemma hom_Q_ext {ℓ₁ ℓ₂ : Spec Γ(D.Q, ⊤) ⟶ D.Q} (h : ℓ₁ ≫ D.γ = ℓ₂ ≫ D.γ)
    (hp : D.p₀ ≫ ℓ₁ = D.p₀ ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
  have hT : ℓ₁ ≫ D.hQ = ℓ₂ ≫ D.hQ := by
    refine hom_strictLocalization_ext M.diagPoint ?_ D.p₀ (closedPoint k) D.p₀_closedPoint ?_
    · simpa only [Category.assoc, γ_g] using congrArg (· ≫ D.g) h
    · rw [reassoc_of% hp]
  have hC₁ : ℓ₁ ≫ pullback.fst _ _ ≫ pullback.fst D.ρ M.q₁ =
      ℓ₂ ≫ pullback.fst _ _ ≫ pullback.fst D.ρ M.q₁ := by
    refine hom_strictLocalization_ext D.c ?_ D.p₀ (closedPoint k) D.p₀_closedPoint ?_
    · simpa using congrArg (· ≫ pullback.fst D.fC D.fC) h
    · rw [reassoc_of% hp]
  have hC₂ : ℓ₁ ≫ pullback.snd _ _ ≫ pullback.fst D.ρ M.q₂ =
      ℓ₂ ≫ pullback.snd _ _ ≫ pullback.fst D.ρ M.q₂ := by
    refine hom_strictLocalization_ext D.c ?_ D.p₀ (closedPoint k) D.p₀_closedPoint ?_
    · simpa using congrArg (· ≫ pullback.snd D.fC D.fC) h
    · rw [reassoc_of% hp]
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
  · simpa using hC₁
  · simpa using hT
  · simpa using hC₂
  · simpa [hQ_eq] using hT

/-- The inverse `Q ⟶ T'` of `φQ`, from the universal property of the strict localization. -/
lemma exists_inv_φQ : ∃ ψ : D.Q ⟶ D.T', D.φQ ≫ ψ = 𝟙 _ ∧ ψ ≫ D.φQ = 𝟙 _ := by
  obtain ⟨κ, hκ, hpκ⟩ := exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing D.s'
    (D.Q.isoSpec.inv ≫ D.γ) D.p₀ D.p₀_closedPoint (by
      rw [p₀_def, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, φQ_γ,
        spec_map_strictHenselizationEval_comp_strictLocalizationToBase])
  have h₁ : D.φQ ≫ D.Q.isoSpec.hom ≫ κ = 𝟙 _ := by
    refine hom_strictLocalization_ext D.s' ?_ (Spec.map (strictHenselizationEval D.s'))
      (closedPoint k) (spec_map_strictHenselizationEval_apply _ _) ?_
    · rw [Category.assoc, Category.assoc, hκ, Iso.hom_inv_id_assoc, φQ_γ, Category.id_comp]
    · have := hpκ
      rw [p₀_def, Category.assoc, Category.assoc] at this
      rw [Category.comp_id]
      exact this
  have h₂ : κ ≫ D.φQ = D.Q.isoSpec.inv := by
    refine D.hom_Q_ext ?_ ?_
    · rw [Category.assoc, φQ_γ, hκ]
    · rw [reassoc_of% hpκ, p₀_def, Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
  exact ⟨D.Q.isoSpec.hom ≫ κ, h₁, by rw [Category.assoc, h₂, Iso.hom_inv_id]⟩

instance isIso_φQ : IsIso D.φQ := by
  obtain ⟨ψ, h₁, h₂⟩ := D.exists_inv_φQ
  exact ⟨ψ, h₁, h₂⟩

/-- **The geometric fibre of `π`** over `z` is the product of the geometric fibres of `ρ` over
`z ≫ q₁` and `z ≫ q₂`. -/
noncomputable def geometricFiberπEquiv {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ M.T) :
    D.π.GeometricFiber z ≃ D.ρ.GeometricFiber (z ≫ M.q₁) × D.ρ.GeometricFiber (z ≫ M.q₂) :=
  (Equiv.cast (by rw [φQ_hQ])).trans
    ((Scheme.Hom.geometricFiberCompIsoEquiv D.φQ D.hQ z).trans (D.geometricFiberHQEquiv z))

/-- **`π` is étale** over the locus where both coordinates avoid the closed point. -/
instance etale_π : Etale ((D.π ⁻¹ᵁ M.O₂).ι ≫ D.π) := by
  let V₁ := pullback.fst D.ρ M.q₁ ⁻¹ᵁ (D.ρ ⁻¹ᵁ M.Xyo)
  let V₂ := pullback.fst D.ρ M.q₂ ⁻¹ᵁ (D.ρ ⁻¹ᵁ M.Xyo)
  have : Etale (V₁.ι ≫ pullback.snd D.ρ M.q₁) :=
    etale_comp_ι_of_isPullback (IsPullback.of_hasPullback D.ρ M.q₁) _
  have : Etale (V₂.ι ≫ pullback.snd D.ρ M.q₂) :=
    etale_comp_ι_of_isPullback (IsPullback.of_hasPullback D.ρ M.q₂) _
  let W₂ := pullback.snd (pullback.snd D.ρ M.q₁) (pullback.snd D.ρ M.q₂) ⁻¹ᵁ V₂
  have : Etale (W₂.ι ≫ pullback.fst (pullback.snd D.ρ M.q₁) (pullback.snd D.ρ M.q₂)) :=
    etale_comp_ι_of_isPullback (IsPullback.of_hasPullback _ _).flip _
  have hle : D.hQ ⁻¹ᵁ M.O₂ ≤ W₂ := by
    intro w hw
    have h₂ : M.q₂ (D.hQ w) ∈ M.Xyo := hw.2
    rw [hQ_eq, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (pullback.snd D.ρ M.q₂),
      ← pullback.condition, Scheme.Hom.comp_apply] at h₂
    exact h₂
  have : Etale ((D.hQ ⁻¹ᵁ M.O₂).ι ≫ pullback.fst (pullback.snd D.ρ M.q₁)
      (pullback.snd D.ρ M.q₂)) := etale_comp_ι_of_le _ hle
  have : Etale ((D.hQ ⁻¹ᵁ M.O₂).ι ≫ D.hQ) := by
    refine etale_comp_ι_comp_of_range _ _ _ V₁ ?_
    rintro _ ⟨w, rfl⟩
    have h₁ : M.q₁ (D.hQ w.1) ∈ M.Xyo := w.2.1
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (pullback.snd D.ρ M.q₁),
      ← pullback.condition, Scheme.Hom.comp_apply] at h₁
    exact h₁
  have : Etale ((D.π ⁻¹ᵁ M.O₂).ι ≫ D.φQ ≫ D.hQ) := by
    refine etale_comp_ι_comp_of_range _ _ _ (D.hQ ⁻¹ᵁ M.O₂) ?_
    rintro _ ⟨w, rfl⟩
    have h : (D.φQ ≫ D.hQ) w.1 ∈ M.O₂ := by
      rw [φQ_hQ]
      exact w.2
    exact h
  rwa [φQ_hQ] at this

end CoverDatum

end AlgebraicGeometry.Etale.CurveLocalModel
