/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CocycleLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Descent
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Trivialization
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedFiniteEtale

/-!
# Lisse sheaves are constant on the universal profinite étale cover

Let `Y` be a connected normal Noetherian scheme and `Ỹ_y` its universal profinite étale cover
at a geometric point `y` (`AlgebraicGeometry.Scheme.UniversalCovers`). Every lisse `ℓ`-adic sheaf
`G` on `Y_proét` becomes constant on `Ỹ_y`: `G|_{Ỹ_y} ≅ ℚ̄_ℓⁿ`
(`IsAdicLisseSheaf.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk`; the regular
case is `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_upperStar_universalCover`).

This is the `ℚ̄_ℓ`-part of the blueprint `proposition-lattices-representations-normal-scheme` in the
form needed here. The blueprint deduces it from the case of finite coefficients by passing to the
coefficient stages; in the Bhatt–Scholze model of lisse sheaves used in this project
(pro-étale locally free `ℚ̄_ℓ,Y`-modules, whose sections are *locally finite* continuous
`ℚ̄_ℓ`-valued functions) we argue with the descent data of a trivialisation instead, following
Bhatt–Scholze (*The pro-étale topology for schemes*, §7.4):

1. `G` is trivialised on a single affine pro-étale cover `f : V ⟶ Y`, `f^* G ≅ ℚ̄_ℓⁿ`
   (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_affine_cover_iso`); its transition
   matrix on the compact `V ×_Y V` takes values in `GL_n(E)` for a finite extension `E` of
   `ℚ_ℓ` (`PadicAlgCl.exists_finiteDimensional_forall_mem_locallyFinite`), and is a cocycle `γ`
   (`AlgebraicGeometry.ProEtale.AdicSheaf.transitionMatrix_trans`,
   `AlgebraicGeometry.ProEtale.AdicSheaf.transitionMatrix_comp`).
2. For every congruence subgroup `K_k ⊆ GL_n(𝒪_E)` (`PadicAlgCl.congruenceSubgroup`), `γ`
   twists the discrete set `GL_n(E) ⧸ K_k` into a pro-étale locally constant sheaf of sets on
   `Y`, which is constant on `Ỹ_y`
   (`AlgebraicGeometry.exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk`,
   Bhatt–Scholze, Lemma 7.4.10). For `k = 0` this is the existence of an `𝒪_E`-lattice, and for
   `k ≥ 1` the triviality on `Ỹ_y` of its reductions modulo `ℓᵏ`.
3. Sections over the connected `Ỹ_y` are determined by one value
   (`AlgebraicGeometry.IsTwistedSection.apply_eq_of_preconnectedSpace`); König's lemma and the
   completeness of `GL_n(E)` give a trivialisation of `γ` over `V ×_Y Ỹ_y`
   (`CocycleTrivialization.exists_cocycle_trivialization`).
4. Correcting the pulled back trivialisation by it, the descent datum becomes trivial and the
   trivialisation descends to `Ỹ_y`
   (`AlgebraicGeometry.ProEtale.AdicSheaf.nonempty_iso_of_transitionMatrix_eq_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

open PadicAlgCl AdicSheaf

/-- Two matrices of locally finite functions agreeing at every point are equal. -/
lemma matrix_ext_eval {T : Type*} [TopologicalSpace T] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l T)}
    (h : ∀ t, A.map (locallyFiniteFunctionsEval t) = B.map (locallyFiniteFunctionsEval t)) :
    A = B :=
  Matrix.ext fun i j ↦ Subtype.ext (ContinuousMap.ext fun t ↦ congrFun (congrFun (h t) i) j)

/-- **Lisse sheaves are constant on the universal cover** (blueprint:
`proposition-lattices-representations-normal-scheme`, the case `Λ = ℚ̄_ℓ`). On a connected normal
Noetherian scheme `Y` (its local rings are integrally closed domains), the pullback of a lisse
`ℓ`-adic sheaf to the universal profinite étale cover `Ỹ_y` at a geometric point `y` is isomorphic
to `ℚ̄_ℓⁿ` for some `n`. -/
theorem IsAdicLisseSheaf.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian Y] [CompactSpace Y] [ConnectedSpace Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Scheme.UniversalCovers Y Ω) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {G : AdicSheaf l Y} (hG : IsAdicLisseSheaf G) :
    ∃ n : ℕ, Nonempty ((U.proj y)^*ᵃ[l].obj G ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)) := by
  classical
  -- 1. a single affine trivialising cover
  obtain ⟨V, f, hfe, hfs, hfq, hV, n, ⟨e⟩⟩ := hG.exists_affine_cover_iso (l := l)
  refine ⟨n, ?_⟩
  set π := U.proj y
  have := U.weaklyEtale_proj y
  have := U.connectedSpace y
  -- the transition matrices on `V ×_Y V`
  let g := transitionMatrix e (pullback.fst f f) (pullback.snd f f) pullback.condition
  let g' := transitionMatrix e (pullback.snd f f) (pullback.fst f f) pullback.condition.symm
  have hgg' : g * g' = 1 := by
    rw [← transitionMatrix_trans e _ _ _ _ _ rfl]
    exact transitionMatrix_self _ _ _
  have hg'g : g' * g = 1 := by
    rw [← transitionMatrix_trans e _ _ _ _ _ rfl]
    exact transitionMatrix_self _ _ _
  -- a finite extension `E` containing their values
  obtain ⟨E, hE, hEmem⟩ := exists_finiteDimensional_forall_mem_locallyFinite
    (l := l) (T := ↥(pullback f f))
    ((Finset.univ.image fun p : Fin n × Fin n ↦ g p.1 p.2) ∪
      Finset.univ.image fun p : Fin n × Fin n ↦ g' p.1 p.2)
  have hgE (i j : Fin n) (z) : (g i j).1 z ∈ E :=
    hEmem _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) z
  have hg'E (i j : Fin n) (z) : (g' i j).1 z ∈ E :=
    hEmem _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))) z
  -- the cocycle `γ = g⁻¹ : V ×_Y V → GL_n(E)`
  let γ : ↥(pullback f f) → GL (Fin n) E := glOfMatrix g' g hg'g hgg' hg'E hgE
  have hγc (i j : Fin n) := continuous_glOfMatrix_apply g' g hg'g hgg' hg'E hgE i j
  have hinj : Function.Injective fun A : Matrix (Fin n) (Fin n) E ↦
      A.map (algebraMap E (PadicAlgCl l)) :=
    Matrix.map_injective (algebraMap E (PadicAlgCl l)).injective
  have hγmap (z : ↥(pullback f f)) : ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
      (algebraMap E (PadicAlgCl l)) = g'.map (locallyFiniteFunctionsEval z) :=
    glOfMatrix_map g' g hg'g hgg' hg'E hgE z
  have hγdiag (v : V) : γ ((pullback.diagonal f).base v) = 1 := by
    have key : transitionMatrix e (pullback.diagonal f ≫ pullback.snd f f)
        (pullback.diagonal f ≫ pullback.fst f f) (by simp) = g'.map
          (locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) :=
      transitionMatrix_comp e _ _ _ _ _
    rw [transitionMatrix_congr e (pullback.diagonal_snd f) (pullback.diagonal_fst f) _ rfl,
      transitionMatrix_self] at key
    apply Units.ext
    apply hinj
    dsimp only
    rw [hγmap, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have := congrArg (fun N ↦ N.map (locallyFiniteFunctionsEval v)) key
    simp only [map_locallyFiniteFunctionsComp_map_eval,
      Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  have hγcocycle (w : ↥(tripleProduct f)) : γ ((tripleProj₁₃ f).base w) =
      γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
        γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) := by
    set q₁₂ := pullback.fst (pullback.snd f f) (pullback.fst f f)
    set q₂₃ := pullback.snd (pullback.snd f f) (pullback.fst f f)
    set q₁₃ := tripleProj₁₃ f
    have hA : pullback.snd f f ≫ f = pullback.fst f f ≫ f := pullback.condition.symm
    have hB : q₁₂ ≫ pullback.snd f f = q₂₃ ≫ pullback.fst f f := pullback.condition
    have h₁₃f : q₁₃ ≫ pullback.fst f f = q₁₂ ≫ pullback.fst f f := pullback.lift_fst _ _ _
    have h₁₃s : q₁₃ ≫ pullback.snd f f = q₂₃ ≫ pullback.snd f f := pullback.lift_snd _ _ _
    -- all morphisms from the triple product to `Y` agree
    have e₁ : (q₁₂ ≫ pullback.snd f f) ≫ f = (q₁₂ ≫ pullback.fst f f) ≫ f := by
      rw [Category.assoc, Category.assoc, hA]
    have e₂ : (q₂₃ ≫ pullback.fst f f) ≫ f = (q₁₂ ≫ pullback.fst f f) ≫ f := by
      rw [← hB, e₁]
    have e₃ : (q₂₃ ≫ pullback.snd f f) ≫ f = (q₁₂ ≫ pullback.fst f f) ≫ f := by
      rw [Category.assoc, hA, ← Category.assoc, e₂]
    have : WeaklyEtale (q₁₃ ≫ pullback.fst f f) := by
      rw [h₁₃f]
      infer_instance
    have : WeaklyEtale q₁₃ := WeaklyEtale.of_comp _ (pullback.fst f f)
    have h₁₃ := transitionMatrix_comp e q₁₃ (pullback.snd f f) (pullback.fst f f)
      pullback.condition.symm (by rw [h₁₃f, h₁₃s, e₃])
    have h₁₂ := transitionMatrix_comp e q₁₂ (pullback.snd f f) (pullback.fst f f)
      pullback.condition.symm e₁
    have h₂₃ := transitionMatrix_comp e q₂₃ (pullback.snd f f) (pullback.fst f f)
      pullback.condition.symm (by rw [e₂, e₃])
    have htr := transitionMatrix_trans e (q₂₃ ≫ pullback.snd f f) (q₁₂ ≫ pullback.snd f f)
      (q₁₂ ≫ pullback.fst f f) (by rw [e₁, e₃]) e₁ e₃
    rw [transitionMatrix_congr e h₁₃s.symm h₁₃f.symm _ (by rw [h₁₃f, h₁₃s, e₃]), h₁₃, h₁₂,
      transitionMatrix_congr e rfl hB _ (by rw [e₂, e₃]), h₂₃] at htr
    apply Units.ext
    apply hinj
    dsimp only
    rw [Units.val_mul, Matrix.map_mul, hγmap, hγmap, hγmap]
    have := congrArg (fun N ↦ N.map (locallyFiniteFunctionsEval w)) htr
    simp only [Matrix.map_mul, map_locallyFiniteFunctionsComp_map_eval] at this
    exact this
  have hcoc (k : ℕ) : IsDescentCocycle f
      (fun z (s : GL (Fin n) E ⧸ congruenceSubgroup E n k) ↦ γ z • s) :=
    { isLocallyConstant := fun s ↦ isLocallyConstant_smul_mk γ (fun i j ↦ (hγc i j).1)
        (fun i j ↦ (hγc i j).2) k s
      bijective := fun z ↦ MulAction.bijective (γ z)
      diagonal := fun v ↦ funext fun s ↦ by simp [hγdiag v]
      cocycle := fun w ↦ funext fun s ↦ by simp [hγcocycle w, mul_smul] }
  -- 2.–3. the cocycle is trivial over `V ×_Y Ỹ_y`
  obtain ⟨σ, hσlc, hσ⟩ := CocycleTrivialization.exists_cocycle_trivialization
    (p₁ := (pullback.fst (pullback.snd f π) (pullback.snd f π)).base)
    (p₂ := (pullback.snd (pullback.snd f π) (pullback.snd f π)).base)
    (g := fun w ↦ γ ((twistedPairMap f π).base w)) (congruenceSubgroup E n)
    (fun k ↦ congruenceSubgroup_antitone k.le_succ) finite_image_congruenceSubgroup_zero
    exists_limit_congruenceSubgroup (fun _ ↦ eq_one_of_forall_mem_congruenceSubgroup)
    (fun τ hτ hinv x x' ↦ IsTwistedSection.apply_eq_of_preconnectedSpace π τ hτ hinv x x')
    (fun k x ↦ exists_isTwistedSection_universalCover_of_isIntegrallyClosed_stalk hY U y f
      (hcoc k) x _)
  have hσc (i j : Fin n) := continuous_apply_of_isLocallyConstant_mk σ hσlc i j
  -- 4. the corrected trivialisation over `V ×_Y Ỹ_y` descends
  let H := matrixOfGL (fun x ↦ (σ x)⁻¹) fun i j ↦ (hσc i j).2
  let H' := matrixOfGL σ fun i j ↦ (hσc i j).1
  have hHH' : H * H' = 1 := matrixOfGL_mul _ _ _ _ fun x ↦ inv_mul_cancel (σ x)
  have hH'H : H' * H = 1 := matrixOfGL_mul _ _ _ _ fun x ↦ mul_inv_cancel (σ x)
  have : IsIso (ofUnitMatrix H) := isIso_ofUnitMatrix H (Matrix.isUnit_det_of_right_inverse hHH')
  have hq : pullback.snd f π ≫ π = pullback.fst f π ≫ f := pullback.condition.symm
  let εT := trivBaseChange e π (pullback.snd f π) (pullback.fst f π) hq ≪≫
    asIso (ofUnitMatrix H)
  refine nonempty_iso_of_transitionMatrix_eq_one (pullback.snd f π) εT ?_
  have hinvH : inv (ofUnitMatrix H) = ofUnitMatrix H' := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [← ofUnitMatrix_mul, hH'H, ofUnitMatrix_one]
  set m := twistedPairMap f π
  set r₁ := pullback.fst (pullback.snd f π) (pullback.snd f π)
  set r₂ := pullback.snd (pullback.snd f π) (pullback.snd f π)
  have hm₁ : m ≫ pullback.fst f f = r₁ ≫ pullback.fst f π := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f f = r₂ ≫ pullback.fst f π := pullback.lift_snd _ _ _
  have : WeaklyEtale (m ≫ pullback.fst f f) := by rw [hm₁]; infer_instance
  have : WeaklyEtale m := WeaklyEtale.of_comp _ (pullback.fst f f)
  have hr : r₁ ≫ pullback.snd f π = r₂ ≫ pullback.snd f π := pullback.condition
  have hr' : (r₁ ≫ pullback.fst f π) ≫ f = (r₂ ≫ pullback.fst f π) ≫ f := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
      hr]
  rw [transitionMatrix_trans_iso, transitionMatrix_baseChange e π _ _ hq r₁ r₂ _ hr',
    transitionMatrix_congr e hm₁.symm hm₂.symm _ (by rw [hm₁, hm₂, hr']),
    transitionMatrix_comp e m _ _ pullback.condition]
  refine matrix_ext_eval fun w ↦ ?_
  simp only [Matrix.map_mul, map_locallyFiniteFunctionsComp_map_eval, asIso_hom, asIso_inv,
    hinvH, unitMatrix_ofUnitMatrix, Matrix.map_one _ (map_zero _) (map_one _)]
  have hγinv (z : ↥(pullback f f)) : (transitionMatrix e (pullback.fst f f) (pullback.snd f f)
      pullback.condition).map (locallyFiniteFunctionsEval z) =
        (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl l)) :=
    (glOfMatrix_inv_map g' g hg'g hgg' hg'E hgE z).symm
  rw [matrixOfGL_map, matrixOfGL_map, hγinv, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul,
    ← Units.val_mul]
  have hσw := hσ w
  rw [hσw, show ∀ a b : GL (Fin n) E, a⁻¹ * b⁻¹ * (b * a) = 1 from fun a b ↦ by group,
    Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **Lisse sheaves are constant on the universal cover** of a connected regular Noetherian
scheme `Y`: regular schemes are normal
(`IsAdicLisseSheaf.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk`). -/
theorem IsAdicLisseSheaf.exists_iso_upperStar_universalCover [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G : AdicSheaf l Y} (hG : IsAdicLisseSheaf G) :
    ∃ n : ℕ, Nonempty ((U.proj y)^*ᵃ[l].obj G ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)) :=
  hG.exists_iso_upperStar_universalCover_of_isIntegrallyClosed_stalk
    (fun _ ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk _⟩) U y

end AlgebraicGeometry.ProEtale
