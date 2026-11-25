/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection

/-!
# Transition cocycles with values in `GL_n(E)`

Let `ε : f^* F ≅ ℚ̄_ℓ,Vⁿ` trivialise an `ℓ`-adic sheaf on a weakly étale `f : V ⟶ T`, and let
`γ : V ×_T V → GL_n(E)` have the transition matrix `T(p₂, p₁)` of `ε` as values. Then `γ` is a
continuous cocycle: its entries and those of its inverse are continuous, the inverse has the
values of `T(p₁, p₂)`, `γ` is trivial on the diagonal and satisfies the cocycle condition
(`AlgebraicGeometry.ProEtale.AdicSheaf.IsTransitionValues`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale.AdicSheaf

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T} [WeaklyEtale f]
  {F : AdicSheaf l T} {n : ℕ} (ε : (f)^*ᵃ[l].obj F ≅ ⨁ fun _ : Fin n ↦ unit l V)
  {E : IntermediateField ℚ_[l] (PadicAlgCl l)}

omit [WeaklyEtale f] in
/-- The transition matrices `T(p₂, p₁)` and `T(p₁, p₂)` are inverse. -/
lemma transitionMatrix_snd_fst_mul :
    transitionMatrix ε (pullback.snd f f) (pullback.fst f f) pullback.condition.symm *
      transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition = 1 := by
  rw [← transitionMatrix_trans ε _ _ _ _ _ rfl, transitionMatrix_self]

omit [WeaklyEtale f] in
/-- The transition matrices `T(p₁, p₂)` and `T(p₂, p₁)` are inverse. -/
lemma transitionMatrix_fst_snd_mul :
    transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition *
      transitionMatrix ε (pullback.snd f f) (pullback.fst f f) pullback.condition.symm = 1 := by
  rw [← transitionMatrix_trans ε _ _ _ _ _ rfl, transitionMatrix_self]

/-- The embedding `E ⊆ ℚ̄_ℓ` is injective on matrices. -/
lemma map_algebraMap_injective {ι κ : Type*} :
    Function.Injective fun A : Matrix ι κ E ↦ A.map (algebraMap E (PadicAlgCl l)) :=
  Matrix.map_injective (algebraMap E (PadicAlgCl l)).injective

/-- `γ : V ×_T V → GL_n(E)` has the transition matrices `T(p₂, p₁)` of `ε` as values. -/
def IsTransitionValues (γ : ↥(pullback f f) → GL (Fin n) E) : Prop :=
  ∀ z, ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl l)) =
    (transitionMatrix ε (pullback.snd f f) (pullback.fst f f) pullback.condition.symm).map
      (locallyFiniteFunctionsEval z)

namespace IsTransitionValues

variable {ε} {γ : ↥(pullback f f) → GL (Fin n) E}

omit [WeaklyEtale f] in
/-- The inverses of the values of `γ` are the transition matrices `T(p₁, p₂)`. -/
lemma inv_map (hγ : IsTransitionValues ε γ) (z : ↥(pullback f f)) :
    (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl l)) =
      (transitionMatrix ε (pullback.fst f f) (pullback.snd f f) pullback.condition).map
        (locallyFiniteFunctionsEval z) := by
  have h₁ := congrArg (fun A ↦ A.map (locallyFiniteFunctionsEval z))
    (transitionMatrix_snd_fst_mul ε)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h₁
  rw [← hγ z] at h₁
  calc _ = (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
        (algebraMap E (PadicAlgCl l)) * (((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
          (algebraMap E (PadicAlgCl l)) * (transitionMatrix ε (pullback.fst f f)
            (pullback.snd f f) pullback.condition).map (locallyFiniteFunctionsEval z)) := by
        rw [h₁, Matrix.mul_one]
    _ = _ := by
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

/-- An `E`-valued function whose values are those of a locally finite function is
continuous. -/
lemma _root_.PadicAlgCl.continuous_of_coe_eq {X : Type*} [TopologicalSpace X] {c : X → E}
    (a : locallyFiniteFunctions l X) (h : ∀ x, (c x : PadicAlgCl l) = a.1 x) : Continuous c := by
  have : c = fun x ↦ ⟨a.1 x, h x ▸ (c x).2⟩ := funext fun x ↦ Subtype.ext (h x)
  rw [this]
  exact a.1.continuous.subtype_mk _

omit [WeaklyEtale f] in
/-- The entries of a cocycle with transition values are continuous. -/
lemma continuous_apply (hγ : IsTransitionValues ε γ) (i j : Fin n) :
    Continuous fun z ↦ ((γ z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j :=
  continuous_of_coe_eq _ fun z ↦ congrFun (congrFun (hγ z) i) j

omit [WeaklyEtale f] in
/-- The entries of the inverse of a cocycle with transition values are continuous. -/
lemma continuous_inv_apply (hγ : IsTransitionValues ε γ) (i j : Fin n) :
    Continuous fun z ↦ (((γ z)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j :=
  continuous_of_coe_eq _ fun z ↦ congrFun (congrFun (hγ.inv_map z) i) j

/-- A cocycle with transition values is trivial on the diagonal. -/
lemma diagonal (hγ : IsTransitionValues ε γ) (v : V) :
    γ ((pullback.diagonal f).base v) = 1 := by
  refine Units.ext (map_algebraMap_injective ?_)
  simp only [hγ _, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← map_locallyFiniteFunctionsComp_map_eval _ (pullback.diagonal f).base.hom,
    ← transitionMatrix_comp ε (pullback.diagonal f) _ _ _ (by simp),
    transitionMatrix_congr ε (pullback.diagonal_snd f) (pullback.diagonal_fst f) _ rfl,
    transitionMatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **The cocycle condition** for a cocycle with transition values. -/
lemma cocycle (hγ : IsTransitionValues ε γ) (w : ↥(tripleProduct f)) :
    γ ((tripleProj₁₃ f).base w) =
      γ ((pullback.fst (pullback.snd f f) (pullback.fst f f)).base w) *
      γ ((pullback.snd (pullback.snd f f) (pullback.fst f f)).base w) := by
  set q₁₂ := pullback.fst (pullback.snd f f) (pullback.fst f f)
  set q₂₃ := pullback.snd (pullback.snd f f) (pullback.fst f f)
  set q₁₃ := tripleProj₁₃ f
  have hA : pullback.snd f f ≫ f = pullback.fst f f ≫ f := pullback.condition.symm
  have hB : q₁₂ ≫ pullback.snd f f = q₂₃ ≫ pullback.fst f f := pullback.condition
  have h₁₃f : q₁₃ ≫ pullback.fst f f = q₁₂ ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have h₁₃s : q₁₃ ≫ pullback.snd f f = q₂₃ ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have e₁ : (q₁₂ ≫ pullback.snd f f) ≫ f = (q₁₂ ≫ pullback.fst f f) ≫ f := by
    rw [Category.assoc, Category.assoc, hA]
  have e₂ : (q₂₃ ≫ pullback.snd f f) ≫ f = (q₂₃ ≫ pullback.fst f f) ≫ f := by
    rw [Category.assoc, Category.assoc, hA]
  have e₃ : (q₂₃ ≫ pullback.snd f f) ≫ f = (q₁₂ ≫ pullback.snd f f) ≫ f := by
    rw [hB, e₂]
  have : WeaklyEtale (q₁₃ ≫ pullback.fst f f) := by
    rw [h₁₃f]
    infer_instance
  have : WeaklyEtale q₁₃ := WeaklyEtale.of_comp _ (pullback.fst f f)
  refine Units.ext (map_algebraMap_injective ?_)
  simp only [Units.val_mul, Matrix.map_mul, hγ _]
  rw [← map_locallyFiniteFunctionsComp_map_eval _ q₁₃.base.hom,
    ← map_locallyFiniteFunctionsComp_map_eval _ q₁₂.base.hom,
    ← map_locallyFiniteFunctionsComp_map_eval _ q₂₃.base.hom, ← Matrix.map_mul,
    ← transitionMatrix_comp ε q₁₃ _ _ _ (by rw [Category.assoc, Category.assoc, hA]),
    ← transitionMatrix_comp ε q₂₃ _ _ _ e₂, ← transitionMatrix_comp ε q₁₂ _ _ _ e₁,
    transitionMatrix_congr ε h₁₃s h₁₃f _ (e₃.trans e₁), transitionMatrix_congr ε rfl hB.symm e₂ e₃,
    ← transitionMatrix_trans ε _ _ _ e₃ e₁ (e₃.trans e₁)]

end IsTransitionValues

end AlgebraicGeometry.ProEtale.AdicSheaf
