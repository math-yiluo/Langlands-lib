/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# Pasting of derived base change morphisms

For two horizontally pasted commutative squares of schemes
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
the derived pullback comparisons paste
(`ProEtale.CondensedRing.pullbackSquareComparison_paste`), hence so do the base change morphisms
`Lg^* Rf_* ⟶ Rf'_* Lg'^*` on the ambient derived categories of module objects
(`CategoryTheory.Adjunction.exchangeRight_app_paste`). Consequently, if the base change morphism of
the left square is invertible, the base change morphism of the outer square is invertible if and
only if that of the right square is invertible on all pullbacks `Lg'^* M`
(`ProEtale.CondensedRing.isIso_baseChangeMap_paste_iff`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B''] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}

/-- **Two-out-of-three for pasted exchange morphisms**: in the situation of
`CategoryTheory.Adjunction.exchangeRight_app_paste`, with squares
```
B --G₁--> B' --G₂--> B''
|Lf        |Lf'       |Lf''
v          v           v
A --G₁'-> A' --G₂'-> A''
```
and right adjoints `Rf`, `Rf'`, `Rf''` going up, if the exchange morphism of the left square
is invertible, then the exchange morphism of the outer square is invertible if and only if the
exchange morphism of the right square is invertible at all objects `G₁' K`. -/
lemma isIso_exchangeRight_paste_iff {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''}
    {G₂' : A' ⥤ A''} {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (af'' : Lf'' ⊣ Rf'') (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂')
    (θ : G ⋙ Lf'' ≅ Lf ⋙ G') (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N)) (hθ₁ : IsIso (exchangeRight af af' θ₁)) :
    IsIso (exchangeRight af af'' θ) ↔
      ∀ K : A, IsIso ((exchangeRight af' af'' θ₂).app (G₁'.obj K)) := by
  constructor
  · intro _ K
    have e := exchangeRight_app_paste af af' af'' θ₁ θ₂ θ c c' h K
    have : IsIso (c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K) ≫
        (exchangeRight af' af'' θ₂).app (G₁'.obj K)) := by
      rw [e]
      infer_instance
    have := IsIso.of_isIso_comp_left (c.hom.app (Rf.obj K))
      (G₂.map ((exchangeRight af af' θ₁).app K) ≫ (exchangeRight af' af'' θ₂).app (G₁'.obj K))
    exact IsIso.of_isIso_comp_left (G₂.map ((exchangeRight af af' θ₁).app K)) _
  · intro hK
    have (K : A) : IsIso ((exchangeRight af af'' θ).app K) := by
      have e := exchangeRight_app_paste af af' af'' θ₁ θ₂ θ c c' h K
      have : IsIso ((exchangeRight af af'' θ).app K ≫ Rf''.map (c'.hom.app K)) := by
        rw [← e]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (Rf''.map (c'.hom.app K))
    exact NatIso.isIso_of_isIso_app _

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The diagram chase behind `pullbackSquareComparison_paste`, in an abstract category. -/
private lemma paste_aux {C : Type*} [Category C]
    {o a b o₁ w₁ w₂ o₂ d o₃ v e o₄ v₂ o₅ u : C}
    (x : o ⟶ a) (x' : a ⟶ o) (hx : x ≫ x' = 𝟙 _) [IsIso x] (m : a ⟶ b)
    (y : o₁ ⟶ w₁) (z : w₁ ⟶ b) (pA : o₁ = o) (hA : y ≫ z = eqToHom pA ≫ x ≫ m)
    (θ₂ : b ⟶ d) (z' : b ⟶ w₁) (hz : z ≫ z' = 𝟙 _) (p₂ : w₁ = w₂) (t : w₂ ⟶ d)
    (hθ₂ : θ₂ = z' ≫ eqToHom p₂ ≫ t) (y₂ : o₂ ⟶ w₂) (pE : o₁ = o₂)
    (hE : y ≫ eqToHom p₂ = eqToHom pE ≫ y₂) (r : o₃ ⟶ v) (s : v ⟶ d) (pB : o₂ = o₃)
    (hB : y₂ ≫ t = eqToHom pB ≫ r ≫ s) (φ : d ⟶ e) (r₂ : o₄ ⟶ v₂) (s₂ : v₂ ⟶ e)
    (pM : o₃ = o₄) (hM : r ≫ s ≫ φ = eqToHom pM ≫ r₂ ≫ s₂) (q : o₅ ⟶ u) (k : u ⟶ e)
    (pC : o₅ = o₄) (hC : q ≫ k = eqToHom pC ≫ r₂ ≫ s₂) (θ : a ⟶ u) (p₇ : o = o₅)
    (hθ : θ = x' ≫ eqToHom p₇ ≫ q) :
    m ≫ θ₂ ≫ φ = θ ≫ k := by
  have hA' : x ≫ m = eqToHom pA.symm ≫ y ≫ z := by
    rw [hA]
    simp
  have hC' : r₂ ≫ s₂ = eqToHom pC.symm ≫ q ≫ k := by
    rw [hC]
    simp
  rw [← cancel_epi x, reassoc_of% hA', hθ₂]
  simp only [Category.assoc]
  rw [reassoc_of% hz, reassoc_of% hE, reassoc_of% hB, hM, hC', hθ]
  simp only [Category.assoc]
  rw [reassoc_of% hx]
  simp

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- **Pasting law of the derived pullback comparisons**: the comparison of the outer square of
two horizontally pasted squares is the pasting of their comparisons, through the composition
isomorphisms `leftDerivedUpperStarComp`. The squares are
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
-/
lemma pullbackSquareComparison_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g)) (N : 𝔻(Y)) :
    (L((f'')^*⟦Λ⟧)).map ((leftDerivedUpperStarComp Λ h g).hom.app N) ≫
        (pullbackSquareComparison Λ sq₂).hom.app ((L((g)^*⟦Λ⟧)).obj N) ≫
          (L((h')^*⟦Λ⟧)).map ((pullbackSquareComparison Λ sq₁).hom.app N) =
      (pullbackSquareComparison Λ sq).hom.app N ≫
        (leftDerivedUpperStarComp Λ h' g').hom.app ((L((f)^*⟦Λ⟧)).obj N) :=
  paste_aux _ _ ((leftDerivedUpperStarComp Λ f'' (h ≫ g)).hom_inv_id_app N) _ _ _ _
    (leftDerivedUpperStarComp_assoc_app Λ f'' h g N) _ _
    ((leftDerivedUpperStarComp Λ f'' h).hom_inv_id_app _) _ _
    (pullbackSquareComparison_hom_app Λ sq₂ ((L((g)^*⟦Λ⟧)).obj N)) _ _
    (leftDerivedUpperStarComp_hom_app_eqToHom Λ sq₂.w.symm g N) _ _ _
    (leftDerivedUpperStarComp_assoc_app Λ h' f' g N) _ _ _ _
    (map_pullbackSquareComparison_hom_app Λ sq₁ h' N) _ _ _
    (leftDerivedUpperStarComp_assoc_app Λ h' g' f N) _ _
    (pullbackSquareComparison_hom_app Λ sq N)

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- **Two-out-of-three for pasted base change morphisms**: if the base change morphism of the
left square `sq₁` is invertible, then the base change morphism of the outer square is invertible
if and only if the one of the right square `sq₂` is invertible on all pullbacks `Lg'^* M`. The
base change morphisms paste by `CategoryTheory.Adjunction.exchangeRight_app_paste`, through the
pasting law `pullbackSquareComparison_paste` of the pullback comparisons. -/
theorem isIso_baseChangeMap_paste_iff (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g)) [IsIso (baseChangeMap Λ sq₁)] :
    IsIso (baseChangeMap Λ sq) ↔
      ∀ M : 𝔻(X), IsIso ((baseChangeMap Λ sq₂).app ((L((g')^*⟦Λ⟧)).obj M)) := by
  have hp := pullbackSquareComparison_paste Λ sq₁ sq₂ sq
  have key := Adjunction.isIso_exchangeRight_paste_iff (G := L((h ≫ g)^*⟦Λ⟧))
    (G' := L((h' ≫ g')^*⟦Λ⟧)) (G₁ := L((g)^*⟦Λ⟧)) (G₁' := L((g')^*⟦Λ⟧))
    (G₂ := L((h)^*⟦Λ⟧)) (G₂' := L((h')^*⟦Λ⟧)) (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (derivedUpperStarLowerStarAdjunction Λ f'')
    (pullbackSquareComparison Λ sq₁) (pullbackSquareComparison Λ sq₂)
    (pullbackSquareComparison Λ sq) (leftDerivedUpperStarComp Λ h g)
    (leftDerivedUpperStarComp Λ h' g') hp ‹_›
  have t1 : IsIso (baseChangeMap Λ sq) ↔ IsIso (Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ f'')
      (pullbackSquareComparison Λ sq)) := Iff.rfl
  have t2 : ∀ M : 𝔻(X), IsIso ((baseChangeMap Λ sq₂).app ((L((g')^*⟦Λ⟧)).obj M)) ↔
      IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f')
        (derivedUpperStarLowerStarAdjunction Λ f'') (pullbackSquareComparison Λ sq₂)).app
        ((L((g')^*⟦Λ⟧)).obj M)) := fun _ ↦ by
    rw [show baseChangeMap Λ sq₂ = Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ f') (derivedUpperStarLowerStarAdjunction Λ f'')
      (pullbackSquareComparison Λ sq₂) from rfl]
  rw [t1, forall_congr' t2]
  exact key

/-- The base change morphism of the outer square of two horizontally pasted squares is invertible
when those of the two squares are. -/
theorem isIso_baseChangeMap_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g)) [IsIso (baseChangeMap Λ sq₁)]
    [IsIso (baseChangeMap Λ sq₂)] : IsIso (baseChangeMap Λ sq) :=
  (isIso_baseChangeMap_paste_iff Λ sq₁ sq₂ sq).mpr fun _ ↦ inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
