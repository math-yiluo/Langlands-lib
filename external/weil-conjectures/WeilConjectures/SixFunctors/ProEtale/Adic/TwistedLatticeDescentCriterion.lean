/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicInt

/-!
# A criterion for landing in a descent

Let `f : V ⟶ T` be weakly étale and `Γ` a matrix of locally finite functions on `V ×_T V`. A
morphism of abelian sheaves `Φ` into the restriction of scalars of `f_* ℚ̄_ℓ,Vⁿ` whose sections
`y` satisfy `Γ · ρ₁^* y = ρ₂^* y` is killed by the descent map of `Γ`
(`AlgebraicGeometry.ProEtale.comp_descentMap_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf Scheme

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T}

section Descent

/-- The sections of a morphism followed by the restriction of scalars of a morphism of `ℓ`-adic
sheaves. -/
lemma comp_restrictPadicInt_map_hom_app {A B : AdicSheaf l T}
    {Z : Sheaf (ProEt.topology T) Ab.{u + 1}} (Φ : Z ⟶ ((AdicSheaf.restrictPadicInt T l).obj A).X)
    (φ : A ⟶ B) (T' : T.ProEtᵒᵖ) (s : Z.obj.obj T') :
    ((Φ ≫ ((AdicSheaf.restrictPadicInt T l).map φ).hom).hom.app T') s =
      φ.hom.hom.app T' (Φ.hom.app T' s) :=
  rfl

private lemma comp_restrictPadicInt_eq_zero {A B : AdicSheaf l T}
    {Z : Sheaf (ProEt.topology T) Ab.{u + 1}}
    (Φ : Z ⟶ ((AdicSheaf.restrictPadicInt T l).obj A).X) (φ : A ⟶ B)
    (h : ∀ (T' : T.ProEtᵒᵖ) (s : Z.obj.obj T'),
      φ.hom.hom.app T' (Φ.hom.app T' s) = 0) :
    Φ ≫ ((AdicSheaf.restrictPadicInt T l).map φ).hom = 0 := by
  ext T' s
  rw [comp_restrictPadicInt_map_hom_app, h]
  simp

private lemma comp_restrictPadicInt_free_eq_zero {W : Scheme.{u}} (g : W ⟶ T)
    {n : ℕ} {A : AdicSheaf l T} {Z : Sheaf (ProEt.topology T) Ab.{u + 1}}
    (Φ : Z ⟶ ((AdicSheaf.restrictPadicInt T l).obj A).X)
    (φ : A ⟶ (g)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l W))
    (q : ∀ T' : T.ProEt, A.X.obj.obj (op T') → Fin n →
      locallyFiniteFunctions l ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj T').left)
    (hq : ∀ (T' : T.ProEt) (x : A.X.obj.obj (op T')),
      comps (B := W) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj T')
        (φ.hom.hom.app (op T') x) = q T' x)
    (h : ∀ (T' : T.ProEt) (s : Z.obj.obj (op T')), q T' (Φ.hom.app (op T') s) = 0) :
    Φ ≫ ((AdicSheaf.restrictPadicInt T l).map φ).hom = 0 := by
  apply comp_restrictPadicInt_eq_zero Φ φ
  intro T' s
  exact comps_injective
    ((hq T'.unop (Φ.hom.app T' s)).trans ((h T'.unop s).trans comps_zero.symm))

/-- **A criterion for landing in a descent**: a morphism of abelian sheaves into `f_* ℚ̄_ℓ,Vⁿ`
whose sections satisfy `γ · ρ₁^* y = ρ₂^* y` is killed by the descent map of `γ`. -/
lemma comp_descentMap_eq_zero [WeaklyEtale f] {n : ℕ}
    (Γ : Matrix (Fin n) (Fin n) (locallyFiniteFunctions l ↥(pullback f f)))
    {Z : Sheaf (ProEt.topology T) Ab.{u + 1}}
    (Φ : Z ⟶ ((AdicSheaf.restrictPadicInt T l).obj
      ((f)_*ᵃ[l].obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l V))).X)
    (y : ∀ T' : T.ProEt, Z.obj.obj (op T') → Fin n →
      locallyFiniteFunctions l ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T').left)
    (hy : ∀ (T' : T.ProEt) (s : Z.obj.obj (op T')),
      comps (l := l) (B := V) (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T')
        (Φ.hom.app (op T') s) = y T' s)
    (h : ∀ (T' : T.ProEt) (s : Z.obj.obj (op T')) (i : Fin n),
      ∑ j, locallyFiniteFunctionsComp l
          (pullback.snd T'.hom (pullback.fst f f ≫ f)).base.hom (Γ i j) *
        locallyFiniteFunctionsComp l (descentρ₁ f T').base.hom (y T' s j) =
      locallyFiniteFunctionsComp l (descentρ₂ f T').base.hom (y T' s i)) :
    Φ ≫ ((AdicSheaf.restrictPadicInt T l).map (descentMap f Γ)).hom = 0 := by
  refine comp_restrictPadicInt_free_eq_zero (pullback.fst f f ≫ f) Φ (descentMap f Γ)
    _ (comps_descentMap f Γ) ?_
  intro T' s
  rw [hy T' s]
  funext i
  rw [h T' s i, sub_self]
  rfl

end Descent

end AlgebraicGeometry.ProEtale
