/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomDual
public import WeilConjectures.SixFunctors.ProEtale.Adic.StalkEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermMonoidal

/-!
# Stalks of the map `F ⊗ N ⟶ 𝓗om(F^∨, N)` for a lisse sheaf `F`

Let `F` be a lisse `ℓ`-adic sheaf and `N` any `ℓ`-adic sheaf on a scheme `Z`, and
`F ⊗ N ⟶ 𝓗om(F^∨, N)`, `f ⊗ n ↦ (φ ↦ φ(f) n)`, the morphism of the underlying sheaves
`CategoryTheory.Mod.toIhomDual`. At a geometric point `s`, the image of `f ⊗ n` is nonzero as
soon as `f` and `n` are (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.toIhomDual_stalk_ne_zero`):
the stalk of `F^∨` is the dual of the stalk of `F`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing`), so some `φ` has
`φ(f) = 1`, and then the pairing of the image of `f ⊗ n` with `φ` is `n`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] {Z : Scheme.{u}}

/-- The unit section of the stalk of the constant sheaf is nonzero. -/
lemma unitSection_one_ne_zero (s : Spec (.of K) ⟶ Z) :
    (unitSection l s).hom (1 : ULift.{u + 1} (PadicAlgCl l)) ≠ 0 := by
  intro h
  have := (asIso (unitSection l s)).toLinearEquiv.injective
    (h.trans (map_zero (asIso (unitSection l s)).toLinearEquiv).symm)
  exact one_ne_zero (α := ULift.{u + 1} (PadicAlgCl l)) this

/-- The action of the unit section of the stalk of `ℚ̄_ℓ` on the stalk of a sheaf of
`ℚ̄_ℓ`-modules is trivial. -/
lemma stalkFunctor_act_unitSection (s : Spec (.of K) ⟶ Z) (N : AdicSheaf l Z)
    (n : (stalkFunctor l s).obj N.X) :
    ((stalkFunctor l s).map (Mod.act N.X)).hom ((μ (stalkFunctor l s) _ N.X).hom
      ((unitSection l s).hom (1 : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ n)) = n := by
  have h₁ := congrArg (fun f ↦ f.hom
    ((ε (stalkFunctor l s)).hom (1 : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ n))
    (μ_natural_left (stalkFunctor l s) (MonObj.one (X := adicConstantSheaf l Z)) N.X)
  have h₂ := congrArg (fun f ↦ f.hom ((1 : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ n))
    (left_unitality (stalkFunctor l s) N.X)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at h₁ h₂
  rw [unitSection, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [h₁]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Mod.one_act]
  refine h₂.symm.trans ?_
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul]

variable [IsAlgClosed K]

-- unifying the stalks of `Mod.regular ℚ̄_ℓ` and `AdicSheaf.unit` unfolds deeply
set_option maxRecDepth 8000 in
/-- **The image of `f ⊗ n` under `F ⊗ N ⟶ 𝓗om(F^∨, N)` is nonzero at a geometric point** if `f`
and `n` are nonzero, for `F` lisse. -/
theorem IsAdicLisseSheaf.toIhomDual_stalk_ne_zero {F : AdicSheaf l Z} (hF : IsAdicLisseSheaf F)
    (N : AdicSheaf l Z) (s : Spec (.of K) ⟶ Z) {f : (stalkFunctor l s).obj F.X} (hf : f ≠ 0)
    {n : (stalkFunctor l s).obj N.X} (hn : n ≠ 0) :
    ((stalkFunctor l s).map (Mod.toIhomDual F N)).hom
      ((μ (stalkFunctor l s) F.X N.X).hom (f ⊗ₜ n)) ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one (ULift.{u + 1} (PadicAlgCl l)) hf
  obtain ⟨φ, hφ⟩ := (hF.bijective_evaluationPairing s).2 ((unitSection l s).hom ∘ₗ ℓ)
  intro h
  have key := Mod.evaluationPairing_toIhomDual F N (stalkFunctor l s)
    (μ_comp_map_braiding_upperStar_comp_Γ s) f n φ
  have e₁ := LinearMap.congr_fun hφ f
  rw [LinearMap.comp_apply] at e₁
  erw [hℓ] at e₁
  apply hn
  refine (stalkFunctor_act_unitSection s N n).symm.trans ?_
  refine (congrArg (fun x ↦ ((stalkFunctor l s).map (Mod.act (A := adicConstantSheaf l Z) N.X)).hom
    ((μ (stalkFunctor l s) (adicConstantSheaf l Z) N.X).hom (x ⊗ₜ n))) e₁.symm).trans ?_
  refine key.symm.trans ?_
  erw [h]
  rw [map_zero, LinearMap.zero_apply]

end AlgebraicGeometry.ProEtale
