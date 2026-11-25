/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseUniversalCover
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice

/-!
# The transition cocycle of a trivialisation

Let `G` be an `ℓ`-adic sheaf on `Y` trivialised, `ε : f^* G ≅ ℚ̄_ℓⁿ`, on a weakly étale
`f : V ⟶ Y` with `V ×_Y V` compact. Its transition matrices take values in `GL_n(E)` for a finite
extension `E` of `ℚ_ℓ` and form a continuous cocycle `γ : V ×_Y V → GL_n(E)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_transitionCocycle`). Acting on the lattices of
`Eⁿ` (`PadicAlgCl.CompactOpenLattice`), `γ` is a descent cocycle
(`AlgebraicGeometry.ProEtale.AdicSheaf.isDescentCocycle_smul_compactOpenLattice`), whose
twisted sections are the lattices of `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}}

open PadicAlgCl AdicSheaf

/-- **The transition cocycle of a trivialisation.** -/
theorem AdicSheaf.exists_transitionCocycle {G : AdicSheaf l Y} (f : V ⟶ Y) [WeaklyEtale f]
    [CompactSpace ↥(pullback f f)] {n : ℕ}
    (e : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E)
      (γ : ↥(pullback f f) → GL (Fin n) E),
      (∀ z, ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
        (algebraMap E (PadicAlgCl l)) = (transitionMatrix e (pullback.snd f f)
          (pullback.fst f f) pullback.condition.symm).map (locallyFiniteFunctionsEval z)) ∧
      (∀ i j, Continuous fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) ∧
      (∀ i j, Continuous fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) ∧
      (∀ v, γ ((pullback.diagonal f).base v) = 1) ∧
      ∀ w : ↥(tripleProduct f), γ ((tripleProj₁₃ f).base w) =
        γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
          γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) := by
  classical
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
  exact ⟨E, hE, γ, hγmap, fun i j ↦ (hγc i j).1, fun i j ↦ (hγc i j).2, hγdiag, hγcocycle⟩

/-- **Transition cocycles act on lattices by descent cocycles.** -/
lemma AdicSheaf.isDescentCocycle_smul_compactOpenLattice (f : V ⟶ Y)
    {E : IntermediateField ℚ_[l] (PadicAlgCl l)} {n : ℕ} (γ : ↥(pullback f f) → GL (Fin n) E)
    (hγc : ∀ i j, Continuous fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
    (hγc' : ∀ i j, Continuous fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
    (hγdiag : ∀ v, γ ((pullback.diagonal f).base v) = 1)
    (hγcocycle : ∀ w : ↥(tripleProduct f), γ ((tripleProj₁₃ f).base w) =
        γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
          γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w)) :
    IsDescentCocycle f (fun z (L : CompactOpenLattice E n) ↦ γ z • L) where
  isLocallyConstant L := CompactOpenLattice.isLocallyConstant_smul γ hγc hγc' L
  bijective z := MulAction.bijective (γ z)
  diagonal v := funext fun L ↦ by simp [hγdiag v]
  cocycle w := funext fun L ↦ by simp [hγcocycle w, mul_smul]

end AlgebraicGeometry.ProEtale
