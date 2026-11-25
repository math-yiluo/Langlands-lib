/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent
public import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

/-!
# Trivialised `ℓ`-adic sheaves as descents of their transition matrices

Let `f : W ⟶ X` be weakly étale, surjective and quasi-compact. An `ℓ`-adic sheaf `G` on `X` with
a trivialisation `ε : f^* G ≅ ℚ̄_ℓ,Wⁿ` is the descent of `ℚ̄_ℓ,Wⁿ` along the transition matrix
of `ε` (`AlgebraicGeometry.ProEtale.AdicSheaf.isoDescentSheafOfTrivialization`): the adjoint
`G ⟶ f_* ℚ̄_ℓ,Wⁿ` of `ε` lands in the kernel of the descent map, and its pullback is `ε`. More
generally a morphism `G ⟶ f_* ℚ̄_ℓ,Wⁿ` killed by the descent map whose adjoint is an isomorphism
identifies `G` with the descent (`AlgebraicGeometry.ProEtale.AdicSheaf.isIso_kernelLift`).

A matrix `A` of locally finite functions on `W` intertwining two cocycles, `γ₂ A₁ = A₂ γ₁` on
`W ×_X W`, induces a morphism of their descents
(`AlgebraicGeometry.ProEtale.AdicSheaf.descentSheafMap`), functorially.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X W : Scheme.{u}} (f : W ⟶ X) [WeaklyEtale f]

open PadicAlgCl

-- The kernel unfolds the composites of sheaf morphisms in the descent map.
omit [WeaklyEtale f] in
/-- **The adjoint of a trivialisation lands in the kernel of the descent map** of its transition
matrix. -/
lemma homEquiv_comp_descentMap_eq_zero {G : AdicSheaf l X} {n : ℕ}
    (ε : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W) :
    (adicUpperStarLowerStarAdjunction l f).homEquiv _ _ ε.hom ≫
      descentMap f (transitionMatrix ε (pullback.fst f f) (pullback.snd f f)
        pullback.condition) = 0 := by
  have key : (trivPull f ε (pullback.fst f f)).hom ≫ ofUnitMatrix (transitionMatrix ε
      (pullback.fst f f) (pullback.snd f f) pullback.condition) =
      (adicUpperStarCongr l pullback.condition).hom.app _ ≫
        (trivPull f ε (pullback.snd f f)).hom := by
    rw [transitionMatrix, ofUnitMatrix_unitMatrix, transitionHom_eq, Iso.hom_inv_id_assoc]
  have hk := congrArg ((adicUpperStarLowerStarAdjunction l (pullback.fst f f ≫ f)).homEquiv _ _)
    key
  simp only [trivPull, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] at hk
  rw [homEquiv_adicUpperStarCongr, homEquiv_adicUpperStarComp, homEquiv_adicUpperStarComp,
    Adjunction.homEquiv_naturality_right, ← freePull_eq, ← freePull_eq] at hk
  rw [descentMap_eq, Preadditive.comp_sub, sub_eq_zero]
  simp only [descentMapFst, descentMapSnd, Functor.map_comp, Category.assoc] at hk ⊢
  exact hk

variable [Surjective f] [QuasiCompact f]

variable {f} in
/-- **Identification with a descent.** A morphism `κ : G ⟶ f_* ℚ̄_ℓ,Wⁿ` killed by the descent map
of a cocycle `γ`, whose adjoint `f^* G ⟶ ℚ̄_ℓ,Wⁿ` is an isomorphism, factors through an
isomorphism `G ≅ descentSheaf f γ`. -/
lemma isIso_kernelLift {G : AdicSheaf l X} {n : ℕ}
    {γ : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l ↥(Limits.pullback f f))}
    (hdiag : γ.map (locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1)
    (hcoc : γ.map (locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      γ.map (locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      γ.map (locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom))
    (κ : G ⟶ (f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ unit l W)) (hκ : κ ≫ descentMap f γ = 0)
    (hiso : IsIso (((adicUpperStarLowerStarAdjunction l f).homEquiv _ _).symm κ)) :
    IsIso (kernel.lift _ κ hκ) := by
  have := isIso_descentTriv (l := l) hdiag hcoc
  have h : (f)^*ᵃ[l].map (kernel.lift _ κ hκ) ≫ descentTriv f γ =
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _).symm κ := by
    apply ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _).injective
    have hd : (adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (descentTriv f γ) =
        kernel.ι (descentMap (l := l) f γ) := Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_naturality_left]
    erw [hd]
    rw [Equiv.apply_symm_apply, kernel.lift_ι]
  have : IsIso ((f)^*ᵃ[l].map (kernel.lift _ κ hκ)) := by
    have : (f)^*ᵃ[l].map (kernel.lift _ κ hκ) =
        ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _).symm κ ≫
          inv (descentTriv f γ) := by
      rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ f) ∈
      Scheme.proetalePrecoverage X := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  exact isIso_of_isIso_adicUpperStar l (fun _ : Unit ↦ f) hcov _ fun _ ↦ this

section Cocycle

variable {f} {G : AdicSheaf l X} {n : ℕ} (ε : (f)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W)

omit [Surjective f] [QuasiCompact f] in
/-- The transition matrix of a trivialisation is trivial on the diagonal. -/
lemma transitionMatrix_map_diagonal :
    (transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition).map
      (locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1 := by
  rw [← transitionMatrix_comp ε (pullback.diagonal f) _ _ _ (by simp),
    transitionMatrix_congr ε (pullback.diagonal_fst f) (pullback.diagonal_snd f) _ rfl,
    transitionMatrix_self]

omit [Surjective f] [QuasiCompact f] in
/-- **The cocycle condition** for the transition matrix of a trivialisation. -/
lemma transitionMatrix_map_tripleProj₁₃ :
    (transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition).map
        (locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      (transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition).map
        (locallyFiniteFunctionsComp l
          (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      (transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition).map
        (locallyFiniteFunctionsComp l
          (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom) := by
  set q₁₂ := pullback.fst (pullback.snd f f) (pullback.fst f f)
  set q₂₃ := pullback.snd (pullback.snd f f) (pullback.fst f f)
  set q₁₃ := tripleProj₁₃ f
  have hA : pullback.fst f f ≫ f = pullback.snd f f ≫ f := pullback.condition
  have hB : q₁₂ ≫ pullback.snd f f = q₂₃ ≫ pullback.fst f f := pullback.condition
  have h₁₃f : q₁₃ ≫ pullback.fst f f = q₁₂ ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have h₁₃s : q₁₃ ≫ pullback.snd f f = q₂₃ ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have e₁ : (q₁₂ ≫ pullback.fst f f) ≫ f = (q₁₂ ≫ pullback.snd f f) ≫ f := by
    rw [Category.assoc, Category.assoc, hA]
  have e₂ : (q₂₃ ≫ pullback.fst f f) ≫ f = (q₂₃ ≫ pullback.snd f f) ≫ f := by
    rw [Category.assoc, Category.assoc, hA]
  have e₃ : (q₁₂ ≫ pullback.snd f f) ≫ f = (q₂₃ ≫ pullback.snd f f) ≫ f := by
    rw [hB, e₂]
  have : WeaklyEtale (q₁₃ ≫ pullback.fst f f) := by
    rw [h₁₃f]
    infer_instance
  have : WeaklyEtale q₁₃ := WeaklyEtale.of_comp _ (pullback.fst f f)
  rw [← transitionMatrix_comp ε q₁₃ _ _ _ (by rw [Category.assoc, Category.assoc, hA]),
    ← transitionMatrix_comp ε q₂₃ _ _ _ e₂, ← transitionMatrix_comp ε q₁₂ _ _ _ e₁,
    transitionMatrix_congr ε h₁₃f h₁₃s _ (e₁.trans e₃), transitionMatrix_congr ε hB.symm rfl _ e₃]
  exact transitionMatrix_trans ε _ _ _ e₁ e₃ _

/-- **A trivialised sheaf is the descent of its transition matrix.** -/
lemma nonempty_iso_descentSheaf :
    Nonempty (G ≅ descentSheaf f (transitionMatrix ε (pullback.fst f f) (pullback.snd f f)
      pullback.condition)) := by
  exact ⟨@asIso _ _ _ _ (kernel.lift _ _ (homEquiv_comp_descentMap_eq_zero f ε))
    (isIso_kernelLift (transitionMatrix_map_diagonal ε) (transitionMatrix_map_tripleProj₁₃ ε)
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ ε.hom)
      (homEquiv_comp_descentMap_eq_zero f ε) (by rw [Equiv.symm_apply_apply]; infer_instance))⟩

end Cocycle

end AlgebraicGeometry.ProEtale.AdicSheaf
