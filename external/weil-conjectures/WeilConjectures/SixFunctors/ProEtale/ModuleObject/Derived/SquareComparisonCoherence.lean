/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!
# Coherence of the pullback comparisons of derived pullbacks

For a commutative square `g' ≫ p = p' ≫ g` of schemes, the pullback comparison
`θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` (`ProEtale.CondensedRing.pullbackSquareComparison`) of the
derived pullbacks of module objects satisfies the following coherences:

- `ProEtale.CondensedRing.pullbackSquareComparison_flip`: the comparison of the transposed square
  is the inverse comparison;
- `ProEtale.CondensedRing.pullbackSquareComparison_cube`: for a commutative cube, the two
  composites of the comparisons of the faces agree;
- `ProEtale.CondensedRing.pullbackSquareComparison_tensor`: the comparison is monoidal, i.e.
  compatible with the tensor comparisons of the derived pullbacks.

The comparisons are compared with the triple composition isomorphisms
`L(a ≫ b ≫ c)^* ≅ Lc^* ⋙ Lb^* ⋙ La^*`
(`ProEtale.CondensedRing.map_pullbackSquareComparison_hom_app`,
`ProEtale.CondensedRing.pullbackSquareComparison_hom_app_obj`), using the associativity of the
composition isomorphisms. The diagram chases are carried out in abstract categories, where the
computations are cheap, and then specialized.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

/-- The components of `α ≪≫ eqToIso h ≪≫ β`. -/
private lemma trans_eqToIso_trans_hom_app {C D : Type*} [Category C] [Category D]
    {F F' G H : C ⥤ D} (α : G ≅ F) (h : F = F') (β : F' ≅ H) (K : C) :
    (α ≪≫ eqToIso h ≪≫ β).hom.app K =
      α.hom.app K ≫ eqToHom (Functor.congr_obj h K) ≫ β.hom.app K := by
  subst h
  simp

/-- The diagram chase behind `pullbackSquareComparison_flip`. -/
private lemma flip_aux {C : Type*} [Category C] {y₀ y₁ y₂ y₃ : C}
    (c₁ : y₀ ⟶ y₁) (c₁' : y₁ ⟶ y₀) (hc₁ : c₁' ≫ c₁ = 𝟙 _) (c₂ : y₂ ⟶ y₃) (c₂' : y₃ ⟶ y₂)
    (hc₂ : c₂ ≫ c₂' = 𝟙 _) (p : y₀ = y₂) (p' : y₂ = y₀) (θ : y₁ ⟶ y₃) (θ' : y₃ ⟶ y₁)
    (θi : y₃ ⟶ y₁) (hθi : θi ≫ θ = 𝟙 _) (hθ : θ = c₁' ≫ eqToHom p ≫ c₂)
    (hθ' : θ' = c₂' ≫ eqToHom p' ≫ c₁) : θ' = θi := by
  rw [← Category.id_comp θ', ← hθi, Category.assoc, hθ, hθ']
  simp [reassoc_of% hc₂, hc₁]

/-- The image under a functor of the expression of a pullback comparison through composition
isomorphisms. -/
private lemma map_comp_map_aux {C D : Type*} {_ : Category C} {_ : Category D} (H : D ⥤ C)
    {y₀ y₁ y₂ y₃ : D} (c₁ : y₀ ⟶ y₁) (c₁' : y₁ ⟶ y₀) (hc₁ : c₁ ≫ c₁' = 𝟙 _) (θ : y₁ ⟶ y₃)
    (E : y₀ ⟶ y₂) (c₂ : y₂ ⟶ y₃) (hθ : θ = c₁' ≫ E ≫ c₂) :
    H.map c₁ ≫ H.map θ = H.map E ≫ H.map c₂ := by
  rw [hθ, ← H.map_comp, reassoc_of% hc₁, H.map_comp]

/-- The diagram chase behind `map_pullbackSquareComparison_hom_app`. -/
private lemma map_square_aux {C : Type*} {_ : Category C} {x₀ x₁ w₀ w₁ w₂ w₃ : C}
    (c₀ : x₀ ⟶ w₀) (m₁ : w₀ ⟶ w₁) (mθ : w₁ ⟶ w₃) (mE : w₀ ⟶ w₂) (m₂ : w₂ ⟶ w₃)
    (hm : m₁ ≫ mθ = mE ≫ m₂) (E' : x₀ ⟶ x₁) (c₀' : x₁ ⟶ w₂) (hN : c₀ ≫ mE = E' ≫ c₀') :
    c₀ ≫ m₁ ≫ mθ = E' ≫ c₀' ≫ m₂ := by
  rw [hm, reassoc_of% hN]

/-- The diagram chase behind `pullbackSquareComparison_hom_app_obj`. -/
private lemma square_app_obj_aux {C : Type*} [Category C]
    {u₁ u₂ u₃ u₄ v₁ v₂ w₁ w₂ z₁ z₂ : C} (p₁₂ : u₁ = u₂) (p₁₃ : u₁ = u₃) (p₃₄ : u₃ = u₄)
    (p₂₄ : u₂ = u₄) (m₁ : u₂ ⟶ v₁) (m₂ : v₁ ⟶ z₁) (a₁ : u₁ ⟶ w₁) (a₂ : w₁ ⟶ z₁)
    (a₂' : z₁ ⟶ w₁) (ha₂ : a₂ ≫ a₂' = 𝟙 _)
    (A₁ : a₁ ≫ a₂ = eqToHom p₁₂ ≫ m₁ ≫ m₂) (θ : z₁ ⟶ z₂) (E₃ : w₁ ⟶ w₂) (b₁ : u₃ ⟶ w₂)
    (b₂ : w₂ ⟶ z₂) (hθ : θ = a₂' ≫ E₃ ≫ b₂) (N : a₁ ≫ E₃ = eqToHom p₁₃ ≫ b₁)
    (n₁ : u₄ ⟶ v₂) (n₂ : v₂ ⟶ z₂) (A₂ : b₁ ≫ b₂ = eqToHom p₃₄ ≫ n₁ ≫ n₂) :
    m₁ ≫ m₂ ≫ θ = eqToHom p₂₄ ≫ n₁ ≫ n₂ := by
  have h : m₁ ≫ m₂ = eqToHom p₁₂.symm ≫ a₁ ≫ a₂ := by
    rw [A₁]
    simp
  rw [reassoc_of% h, hθ, reassoc_of% ha₂, reassoc_of% N, A₂]
  simp

/-- The diagram chase behind `pullbackSquareComparison_cube`: six morphisms `t₁, …, t₆` (the
triple composition isomorphisms of the six paths through the cube) related by the faces. -/
private lemma cube_aux {C : Type*} [Category C]
    {o₁ o₂ o₃ o₄ o₅ o₆ v₁ v₂ v₃ v₄ v₅ v₆ y₁ y₂ y₃ y₄ y₅ y₆ : C}
    (t₁ : o₁ ⟶ v₁) (t₁' : v₁ ⟶ y₁) [IsIso t₁] [IsIso t₁'] (t₂ : o₂ ⟶ v₂) (t₂' : v₂ ⟶ y₂)
    (t₃ : o₃ ⟶ v₃) (t₃' : v₃ ⟶ y₃) (t₄ : o₄ ⟶ v₄) (t₄' : v₄ ⟶ y₄)
    (t₅ : o₅ ⟶ v₅) (t₅' : v₅ ⟶ y₅) (t₆ : o₆ ⟶ v₆) (t₆' : v₆ ⟶ y₆)
    (p₁₂ : o₁ = o₂) (p₂₃ : o₂ = o₃) (p₃₄ : o₃ = o₄) (p₁₅ : o₁ = o₅) (p₅₆ : o₅ = o₆)
    (p₆₄ : o₆ = o₄) (θ₁ : y₁ ⟶ y₂) (θ₂ : y₂ ⟶ y₃) (θ₃ : y₃ ⟶ y₄) (θ₄ : y₁ ⟶ y₅)
    (θ₅ : y₅ ⟶ y₆) (θ₆ : y₆ ⟶ y₄)
    (h₁ : t₁ ≫ t₁' ≫ θ₁ = eqToHom p₁₂ ≫ t₂ ≫ t₂') (h₂ : t₂ ≫ t₂' ≫ θ₂ = eqToHom p₂₃ ≫ t₃ ≫ t₃')
    (h₃ : t₃ ≫ t₃' ≫ θ₃ = eqToHom p₃₄ ≫ t₄ ≫ t₄') (h₄ : t₁ ≫ t₁' ≫ θ₄ = eqToHom p₁₅ ≫ t₅ ≫ t₅')
    (h₅ : t₅ ≫ t₅' ≫ θ₅ = eqToHom p₅₆ ≫ t₆ ≫ t₆')
    (h₆ : t₆ ≫ t₆' ≫ θ₆ = eqToHom p₆₄ ≫ t₄ ≫ t₄') :
    θ₁ ≫ θ₂ ≫ θ₃ = θ₄ ≫ θ₅ ≫ θ₆ := by
  rw [← cancel_epi t₁', ← cancel_epi t₁, reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄,
    reassoc_of% h₅, h₆]
  simp

/-- The monoidality of a pullback comparison, as a diagram chase in a monoidal category. -/
private lemma tensor_aux {C : Type*} [Category C] [MonoidalCategory C]
    {x₀ y₀ z₀ x₁ y₁ z₁ x₂ y₂ z₂ u v w a₁ a₂ : C}
    (cAB : x₀ ≅ x₁) (cA : y₀ ≅ y₁) (cB : z₀ ≅ z₁) (m₀ : x₀ ⟶ y₀ ⊗ z₀)
    (Mg : x₁ ⟶ a₁) (Mp' : a₁ ⟶ y₁ ⊗ z₁)
    (T₁ : m₀ ≫ (cA.hom ⊗ₘ cB.hom) = cAB.hom ≫ Mg ≫ Mp')
    (c'AB : u ≅ x₂) (c'A : v ≅ y₂) (c'B : w ≅ z₂) (m₁ : u ⟶ v ⊗ w)
    (Mp : x₂ ⟶ a₂) (Mg' : a₂ ⟶ y₂ ⊗ z₂)
    (T₂ : m₁ ≫ (c'A.hom ⊗ₘ c'B.hom) = c'AB.hom ≫ Mp ≫ Mg')
    (eAB : x₀ ⟶ u) (eA : y₀ ⟶ v) (eB : z₀ ⟶ w) (hE : m₀ ≫ (eA ⊗ₘ eB) = eAB ≫ m₁)
    (θAB : x₁ ⟶ x₂) (θA : y₁ ⟶ y₂) (θB : z₁ ⟶ z₂) (hAB : θAB = cAB.inv ≫ eAB ≫ c'AB.hom)
    (hA : θA = cA.inv ≫ eA ≫ c'A.hom) (hB : θB = cB.inv ≫ eB ≫ c'B.hom) :
    Mg ≫ Mp' ≫ (θA ⊗ₘ θB) = θAB ≫ Mp ≫ Mg' := by
  rw [← cancel_epi cAB.hom, ← reassoc_of% T₁, hA, hB, hAB, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← tensorHom_comp_tensorHom, reassoc_of% hE, T₂]
  simp

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Composition

variable {R S T : Scheme.{u}}

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The composition isomorphism `L(a ≫ h)^* ≅ Lh^* ⋙ La^*` commutes with the `eqToHom`s induced
by an equality `h = h'`. -/
lemma leftDerivedUpperStarComp_hom_app_map_eqToHom (a : R ⟶ S) {h h' : S ⟶ T} (e : h = h')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (leftDerivedUpperStarComp Λ a h).hom.app K ≫
        L((a)^*⟦Λ⟧).map (eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj K = L((h')^*⟦Λ⟧).obj K)) =
      eqToHom (by rw [e] : L((a ≫ h)^*⟦Λ⟧).obj K = L((a ≫ h')^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ a h').hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, L((a)^*⟦Λ⟧).map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The composition isomorphism `L(h ≫ b)^* ≅ Lb^* ⋙ Lh^*` commutes with the `eqToHom`s induced
by an equality `h = h'`. -/
lemma leftDerivedUpperStarComp_hom_app_eqToHom {h h' : R ⟶ S} (e : h = h') (b : S ⟶ T)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (leftDerivedUpperStarComp Λ h b).hom.app K ≫
        eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj K) =
          L((h')^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj K)) =
      eqToHom (by rw [e] : L((h ≫ b)^*⟦Λ⟧).obj K = L((h' ≫ b)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ h' b).hom.app K := by
  subst e
  rw [eqToHom_refl, eqToHom_refl]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Composition

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- `ProEtale.CondensedRing.pullbackSquareComparison` unfolded. -/
lemma pullbackSquareComparison_eq (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq = (leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (by rw [sq.w]) ≪≫ leftDerivedUpperStarComp Λ g' p :=
  rfl

/-- The components of the pullback comparison. -/
lemma pullbackSquareComparison_hom_app (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarComp Λ p' g).inv.app K ≫
        eqToHom (by rw [sq.w] : L((p' ≫ g)^*⟦Λ⟧).obj K = L((g' ≫ p)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K :=
  (congrArg (fun θ ↦ θ.hom.app K) (pullbackSquareComparison_eq Λ sq)).trans
    (trans_eqToIso_trans_hom_app _ _ _ K)

/-- The pullback comparison of the transposed square is the inverse of the pullback
comparison. -/
lemma pullbackSquareComparison_flip (sq : CommSq g' p' p g) :
    pullbackSquareComparison Λ sq.flip = (pullbackSquareComparison Λ sq).symm :=
  Iso.ext (NatTrans.ext (funext fun K ↦ flip_aux _ _
    ((leftDerivedUpperStarComp Λ p' g).inv_hom_id_app K)
    _ _ ((leftDerivedUpperStarComp Λ g' p).hom_inv_id_app K) _ _ _ _ _
    ((pullbackSquareComparison Λ sq).inv_hom_id_app K) (pullbackSquareComparison_hom_app Λ sq K)
    (pullbackSquareComparison_hom_app Λ sq.flip K)))

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- `L(a)^*` of the pullback comparison, in terms of the triple composition isomorphisms
`L(a ≫ p' ≫ g)^* ≅ Lg^* ⋙ Lp'^* ⋙ La^*` and `L(a ≫ g' ≫ p)^* ≅ Lp^* ⋙ Lg'^* ⋙ La^*`. -/
lemma map_pullbackSquareComparison_hom_app {W : Scheme.{u}} (sq : CommSq g' p' p g)
    (a : W ⟶ X')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarComp Λ a (p' ≫ g)).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ p' g).hom.app K) ≫
        L((a)^*⟦Λ⟧).map ((pullbackSquareComparison Λ sq).hom.app K) =
      eqToHom (by rw [sq.w] : L((a ≫ p' ≫ g)^*⟦Λ⟧).obj K = L((a ≫ g' ≫ p)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ a (g' ≫ p)).hom.app K ≫
        L((a)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g' p).hom.app K) :=
  map_square_aux _ _ _ _ _
    (map_comp_map_aux L((a)^*⟦Λ⟧) _ _ ((leftDerivedUpperStarComp Λ p' g).hom_inv_id_app K) _ _ _
      (pullbackSquareComparison_hom_app Λ sq K)) _ _
    (leftDerivedUpperStarComp_hom_app_map_eqToHom Λ a sq.w.symm K)

/-- The pullback comparison at `L(b)^* K`, in terms of the triple composition isomorphisms
`L(p' ≫ g ≫ b)^* ≅ Lb^* ⋙ Lg^* ⋙ Lp'^*` and `L(g' ≫ p ≫ b)^* ≅ Lb^* ⋙ Lp^* ⋙ Lg'^*`. -/
lemma pullbackSquareComparison_hom_app_obj {V : Scheme.{u}} (sq : CommSq g' p' p g)
    (b : Y ⟶ V)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :
    (leftDerivedUpperStarComp Λ p' (g ≫ b)).hom.app K ≫
        L((p')^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g b).hom.app K) ≫
        (pullbackSquareComparison Λ sq).hom.app (L((b)^*⟦Λ⟧).obj K) =
      eqToHom (by rw [reassoc_of% sq.w] :
          L((p' ≫ g ≫ b)^*⟦Λ⟧).obj K = L((g' ≫ p ≫ b)^*⟦Λ⟧).obj K) ≫
        (leftDerivedUpperStarComp Λ g' (p ≫ b)).hom.app K ≫
        L((g')^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ p b).hom.app K) :=
  square_app_obj_aux _ _ _ _ _ _ _ _ _ ((leftDerivedUpperStarComp Λ p' g).hom_inv_id_app _)
    (leftDerivedUpperStarComp_assoc_app Λ p' g b K) _ _ _ _
    (pullbackSquareComparison_hom_app Λ sq (L((b)^*⟦Λ⟧).obj K))
    (leftDerivedUpperStarComp_hom_app_eqToHom Λ sq.w.symm b K) _ _
    (leftDerivedUpperStarComp_assoc_app Λ g' p b K)
-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The tensor comparison of the derived pullback along `h` commutes with the `eqToHom`s induced
by an equality `h = h'`. -/
lemma leftDerivedUpperStarTensor_app_app_comp_eqToHom {h h' : X' ⟶ Y} (e : h = h')
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    ((leftDerivedUpperStarTensor Λ h).app A).app B ≫
        (eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj A = L((h')^*⟦Λ⟧).obj A) ⊗ₘ
          eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj B = L((h')^*⟦Λ⟧).obj B)) =
      eqToHom (by rw [e] : L((h)^*⟦Λ⟧).obj (A ⊗ B) = L((h')^*⟦Λ⟧).obj (A ⊗ B)) ≫
        ((leftDerivedUpperStarTensor Λ h').app A).app B := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, eqToHom_refl, id_tensorHom_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- **The pullback comparison is monoidal**: it is compatible with the tensor comparisons
`m : Lf^* (K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` of the derived pullbacks. -/
lemma pullbackSquareComparison_tensor (sq : CommSq g' p' p g)
    (A B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((p')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app A).app B) ≫
        ((leftDerivedUpperStarTensor Λ p').app _).app _ ≫
        ((pullbackSquareComparison Λ sq).hom.app A ⊗ₘ (pullbackSquareComparison Λ sq).hom.app B) =
      (pullbackSquareComparison Λ sq).hom.app (A ⊗ B) ≫
        L((g')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ p).app A).app B) ≫
        ((leftDerivedUpperStarTensor Λ g').app _).app _ :=
  tensor_aux ((leftDerivedUpperStarComp Λ p' g).app (A ⊗ B))
    ((leftDerivedUpperStarComp Λ p' g).app A) ((leftDerivedUpperStarComp Λ p' g).app B) _ _ _
    (leftDerivedUpperStarTensor_comp Λ p' g A B)
    ((leftDerivedUpperStarComp Λ g' p).app (A ⊗ B))
    ((leftDerivedUpperStarComp Λ g' p).app A) ((leftDerivedUpperStarComp Λ g' p).app B) _ _ _
    (leftDerivedUpperStarTensor_comp Λ g' p A B) _ _ _
    (leftDerivedUpperStarTensor_app_app_comp_eqToHom Λ sq.w.symm A B) _ _ _
    (pullbackSquareComparison_hom_app Λ sq (A ⊗ B)) (pullbackSquareComparison_hom_app Λ sq A)
    (pullbackSquareComparison_hom_app Λ sq B)

end BaseChange

section Cube

variable {P' M' P₁' M₁' P M P₁ M₁ : Scheme.{u}} {iP : P' ⟶ P} {iM : M' ⟶ M} {iP₁ : P₁' ⟶ P₁}
  {iM₁ : M₁' ⟶ M₁} {f' : P' ⟶ M'} {g' : M' ⟶ M₁'} {k' : P' ⟶ P₁'} {e' : P₁' ⟶ M₁'}
  {f : P ⟶ M} {g : M ⟶ M₁} {k : P ⟶ P₁} {e : P₁ ⟶ M₁}

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- **Cube coherence of the pullback comparisons**: for a commutative cube of schemes with top
face `top`, bottom face `bot` and side faces `sf`, `sg`, `sk`, `se`, the two composites
`Lk'^* Le'^* LiM₁^* ⟶ LiP^* Lf^* Lg^*` of the pullback comparisons of the faces agree. -/
lemma pullbackSquareComparison_cube (top : CommSq f' k' g' e') (bot : CommSq f k g e)
    (sf : CommSq iP f' f iM) (sg : CommSq iM g' g iM₁) (sk : CommSq iP k' k iP₁)
    (se : CommSq iP₁ e' e iM₁)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology M₁) Ab.{u + 1}) (condensedRingObj Λ M₁))) :
    (pullbackSquareComparison Λ top).hom.app (L((iM₁)^*⟦Λ⟧).obj K) ≫
        L((f')^*⟦Λ⟧).map ((pullbackSquareComparison Λ sg).hom.app K) ≫
        (pullbackSquareComparison Λ sf).hom.app (L((g)^*⟦Λ⟧).obj K) =
      L((k')^*⟦Λ⟧).map ((pullbackSquareComparison Λ se).hom.app K) ≫
        (pullbackSquareComparison Λ sk).hom.app (L((e)^*⟦Λ⟧).obj K) ≫
        L((iP)^*⟦Λ⟧).map ((pullbackSquareComparison Λ bot).hom.app K) :=
  cube_aux (h₁ := pullbackSquareComparison_hom_app_obj Λ top iM₁ K)
    (h₂ := map_pullbackSquareComparison_hom_app Λ sg f' K)
    (h₃ := pullbackSquareComparison_hom_app_obj Λ sf g K)
    (h₄ := map_pullbackSquareComparison_hom_app Λ se k' K)
    (h₅ := pullbackSquareComparison_hom_app_obj Λ sk e K)
    (h₆ := map_pullbackSquareComparison_hom_app Λ bot iP K)

end Cube

end AlgebraicGeometry.ProEtale.CondensedRing
