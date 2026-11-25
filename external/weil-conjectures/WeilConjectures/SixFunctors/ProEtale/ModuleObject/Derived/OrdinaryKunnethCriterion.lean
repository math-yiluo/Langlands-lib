/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.CategoryTheory.Adjunction.KunnethTranspose
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!

# A criterion for the ordinary Künneth map of module objects

Let `Λ` be a commutative condensed ring and
```
P ──p₁──▶ X
│ p₂       │ a_X
▼          ▼
Y ──a_Y──▶ S
```
a commutative square of schemes, with `q = p₂ ≫ a_Y`. The ordinary Künneth map
`κ_{A,B} : L(𝟙)^* Ra_{X*} A ⊗ L(𝟙)^* Ra_{Y*} B ⟶ Rq_* (Lp₁^* A ⊗ Lp₂^* B)` of the two squares
over `S` (`ProEtale.CondensedRing.lowerStarKunnethMap'`) is an isomorphism as soon as

* the base change morphism `La_Y^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A` of the square is (generic base
  change),
* the projection morphism `Rp₂_* Lp₁^* A ⊗ B ⟶ Rp₂_* (Lp₁^* A ⊗ Lp₂^* B)` of `p₂` is (the
  relative Künneth formula), and
* the projection morphism `Ra_{Y*} B ⊗ Ra_{X*} A ⟶ Ra_{Y*} (B ⊗ La_Y^* Ra_{X*} A)` of `a_Y` is
  (the projection formula over `S`)

(`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isIso`). This is the abstract
decomposition `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom` of the Künneth map of the
composite `q = p₂ ≫ a_Y`, on the ambient derived categories of module objects, for an arbitrary
coefficient ring; the version on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is
`ProEtale.CondensedRing.isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] DerivedCategory.braidedCategory'

/-- The transpose of `F f ≫ g` along `F ⊣ G` is invertible if `f` and the transpose of `g` are. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_of_eq_map_comp {C D : Type*} [Category C]
    [Category D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {X X' : D} {Y : C} (f : X' ⟶ X)
    (g : F.obj X ⟶ Y) (c : F.obj X' ⟶ Y) (hc : c = F.map f ≫ g) [IsIso f]
    [hg : IsIso (adj.homEquiv _ _ g)] : IsIso (adj.homEquiv _ _ c) := by
  subst hc
  rw [adj.homEquiv_naturality_left]
  infer_instance

/-- The transpose of `F f ≫ ε_B` along `F ⊣ G` is `f`, hence invertible if `f` is. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_map_comp_counit {C D : Type*} [Category C]
    [Category D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {X : D} {B : C} (f : X ⟶ G.obj B)
    [IsIso f] : IsIso (adj.homEquiv _ _ (F.map f ≫ adj.counit.app B)) := by
  rw [adj.homEquiv_naturality_left, adj.homEquiv_unit, adj.right_triangle_components,
    Category.comp_id]
  infer_instance

/-- For `F` compatible with the braidings, the left projection morphism at `(U, A)` is invertible if
the projection morphism at `(A, U')` is, for an isomorphism `U ⟶ U'`. -/
lemma _root_.CategoryTheory.Adjunction.isIso_leftProjectionMorphism_of_isIso {C D : Type*}
    [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C]
    [BraidedCategory D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]
    (h : ∀ X Y : D, Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X)
    (A : C) {U U' : D} (ι : U ⟶ U') [IsIso ι] [hpm : IsIso (adj.projectionMorphism A U')] :
    IsIso (adj.leftProjectionMorphism U A) := by
  have hn := adj.projectionMorphism_natural_right A ι
  have : IsIso (adj.projectionMorphism A U ≫ G.map (A ◁ F.map ι)) := by
    rw [← hn]
    infer_instance
  have := IsIso.of_isIso_comp_right (adj.projectionMorphism A U) (G.map (A ◁ F.map ι))
  exact adj.isIso_leftProjectionMorphism h U A

open Functor.OplaxMonoidal in
/-- `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom` with explicit hypotheses. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory C₃] {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R) {S' : C₃ ⥤ C₂}
    {S : C₂ ⥤ C₃} (adjS : S' ⊣ S) {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
    [R'.OplaxMonoidal] [S'.OplaxMonoidal] [Q'.OplaxMonoidal] (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₂ : S'.obj V ⟶ W) (i₂ : R'.obj W ⟶ A₂) (hc₂ : e.inv.app V ≫ c₂ = R'.map d₂ ≫ i₂)
    (t₁ : IsIso (adjS.homEquiv _ _ d₂)) (t₂ : IsIso (adjS.leftProjectionMorphism U W))
    (t₃ : IsIso (adjR.homEquiv _ _ (e.inv.app U ≫ c₁)))
    (t₄ : IsIso (adjR.projectionMorphism A₁ W)) (t₅ : IsIso i₂) :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) :=
  adjR.isIso_homEquiv_δ_tensorHom adjS adjQ e he c₁ c₂ d₂ i₂ hc₂

/-- Normalize a comparison through an identity pullback using naturality. -/
private lemma pullbackComparison_id_comp_aux {C : Type*} [Category C]
    {I J K L M N O : C} (i : I ⟶ J) (a : J ⟶ K) (e : K ⟶ M) (b : M ⟶ N)
    (m : J ⟶ L) (e' : L ⟶ M) (j : I ⟶ O) (i' : O ⟶ L)
    (u : J ⟶ N) (v : O ⟶ N) (hu : u = a ≫ e ≫ b) (hc : a ≫ e = m ≫ e')
    (hn : j ≫ i' = i ≫ m) (hv : v = i' ≫ e' ≫ b) : i ≫ u = j ≫ v := by
  rw [hu, hv, ← Category.assoc a, hc]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

/-- The same normalization when the final comparison is an inverse pair. -/
private lemma pullbackComparison_id_self_aux {C : Type*} [Category C]
    {I J K L O : C} (i : I ⟶ J) (a : J ⟶ K) (e : K ⟶ L) (b : L ⟶ O)
    (m : J ⟶ L) (j : I ⟶ O) (i' : O ⟶ L) (u : J ⟶ O)
    (hu : u = a ≫ e ≫ b) (hc : a ≫ e = m ≫ 𝟙 L)
    (hn : j ≫ i' = i ≫ m) (hb : i' ≫ b = 𝟙 O) : i ≫ u = j := by
  rw [hu, ← Category.assoc a, hc, Category.comp_id]
  rw [← Category.assoc, ← hn, Category.assoc, hb, Category.comp_id]

/-- Compose a factorization of a mapped morphism with another mapped morphism. -/
private lemma map_comp_of_comp_eq_map_aux {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} {T : D} (i : F.obj X ⟶ T) (u : T ⟶ F.obj Y)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : i ≫ u = F.map f) :
    i ≫ u ≫ F.map g = F.map (f ≫ g) ≫ 𝟙 _ := by
  rw [← Category.assoc, h, ← F.map_comp, Category.comp_id]

open Functor.OplaxMonoidal in
/-- Apply the composite Künneth criterion to counits transported through identity comparisons. -/
private lemma kunneth_of_comparison_counits {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory C₃] [BraidedCategory C₂] [BraidedCategory C₃]
    {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R) {S' : C₃ ⥤ C₂}
    {S : C₂ ⥤ C₃} (adjS : S' ⊣ S) {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
    [R'.OplaxMonoidal] [S'.OplaxMonoidal] [Q'.OplaxMonoidal] (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    (hb : ∀ U V : C₃, δ S' U V ≫ (β_ (S'.obj U) (S'.obj V)).hom =
      S'.map (β_ U V).hom ≫ δ S' V U)
    {U V K : C₃} {W : C₂} {A : C₁} (ι : U ≅ K) (ι' : V ≅ S.obj W)
    (c₁ : Q'.obj U ⟶ A) (c₂ : Q'.obj V ⟶ R'.obj W) (g : R'.obj (S'.obj K) ⟶ A)
    (hc₁ : e.inv.app U ≫ c₁ = R'.map (S'.map ι.hom) ≫ g)
    (hc₂ : e.inv.app V ≫ c₂ = R'.map (S'.map ι'.hom ≫ adjS.counit.app W) ≫ 𝟙 _)
    (h₁ : IsIso (adjR.homEquiv _ _ g)) (h₂ : IsIso (adjR.projectionMorphism A W))
    (h₃ : IsIso (adjS.projectionMorphism W K)) :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) := by
  have t₁ := adjR.isIso_homEquiv_of_eq_map_comp (S'.map ι.hom) g _ hc₁
  have t₂ := adjS.isIso_homEquiv_map_comp_counit ι'.hom
  have t₃ := adjS.isIso_leftProjectionMorphism_of_isIso hb W ι.hom
  exact adjR.isIso_homEquiv_δ_tensorHom_of_isIso adjS adjQ e he c₁ c₂ _ (𝟙 _)
    hc₂ t₂ t₃ t₁ h₂ inferInstance

/-- Transport a morphism identity along a second equality of its target. -/
private lemma comp_eqToHom_transport_aux {C : Type*} [Category C] {A B D T : C}
    (f : A ⟶ B) (g : A ⟶ D) (h : B = D) (w : B = T) (hf : f ≫ eqToHom h = g) :
    f ≫ eqToHom w = g ≫ eqToHom (h.symm.trans w) := by
  rw [← hf, Category.assoc, eqToHom_trans]

/-- Transfer invertibility along an equality without elaborating the category again. -/
private lemma kunneth_isIso_of_eq_aux {C : Type*} [Category C] {X Y : C}
    {f g : X ⟶ Y} (h : f = g) (hg : IsIso g) : IsIso f := by
  rw [h]
  exact hg

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Transpose

variable {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} {g : X ⟶ X₁} {h : Y ⟶ Y₁}
  {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}

/-- The ordinary Künneth map is the transpose along `Lk^* ⊣ Rk_*` of the oplax structure of
`Lk^*` followed by the tensor product of the counits transported along the pullback comparisons
of the two squares. -/
lemma lowerStarKunnethMap'_eq_homEquiv_counit (sq₁ : CommSq f₁ k g e₁) (sq₂ : CommSq f₂ k h e₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    lowerStarKunnethMap' Λ sq₁ sq₂ A B =
      (derivedUpperStarLowerStarAdjunction Λ k).homEquiv _ _
        (Functor.OplaxMonoidal.δ L((k)^*⟦Λ⟧) _ _ ≫
          (((pullbackSquareComparison Λ sq₁).hom.app (R((g)_*⟦Λ⟧).obj A) ≫
              L((f₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ g).counit.app A)) ⊗ₘ
            ((pullbackSquareComparison Λ sq₂).hom.app (R((h)_*⟦Λ⟧).obj B) ≫
              L((f₂)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ h).counit.app B)))) :=
  Adjunction.tensorHom_comp_eq_homEquiv_δ (derivedUpperStarLowerStarAdjunction Λ k)
    (lowerStarTensorMap' Λ k) (lowerStarTensorMap'_comp_counit Λ k) _ _ _ _
    (Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq₁)
      (baseChangeMap Λ sq₁) rfl A)
    (Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq₂)
      (baseChangeMap Λ sq₂) rfl B)

/-- The transpose of the transported counit `Lg'^* ... ⟶ Lp'^*` of a square is its base change
morphism. -/
lemma homEquiv_pullbackSquareComparison_comp_counit {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y}
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (derivedUpperStarLowerStarAdjunction Λ p').homEquiv _ _
        ((pullbackSquareComparison Λ sq).hom.app (R((p)_*⟦Λ⟧).obj A) ≫
          L((g')^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ p).counit.app A)) =
      (baseChangeMap Λ sq).app A := by
  rw [← Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq)
    (baseChangeMap Λ sq) rfl A]
  erw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]

end Transpose

section Criterion

variable {P X Y S : Scheme.{u}}

/-- `L(f ≫ 𝟙)^* ≅ Lf^*` read through the identity isomorphism `L(𝟙)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarComp_inv_app_comp_eqToHom_id {W : Scheme.{u}} (f : W ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) :
    (leftDerivedUpperStarComp Λ f (𝟙 S)).inv.app K ≫ eqToHom (by rw [Category.comp_id]; rfl) =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K) := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, leftDerivedUpperStarComp_id_right_app]

/-- `leftDerivedUpperStarComp_inv_app_comp_eqToHom_id` followed by an arbitrary `eqToHom`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_comp_eqToHom_id' {W : Scheme.{u}} (f : W ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))} (h : L((f ≫ 𝟙 S)^*⟦Λ⟧).obj K = T) :
    (leftDerivedUpperStarComp Λ f (𝟙 S)).inv.app K ≫ eqToHom h =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K) ≫
        eqToHom ((congrArg (fun φ ↦ L((φ)^*⟦Λ⟧).obj K) (Category.comp_id f)).symm.trans h) :=
  comp_eqToHom_transport_aux _ _ _ h (leftDerivedUpperStarComp_inv_app_comp_eqToHom_id Λ f K)

/-- Remove the identity pullback from the comparison of a square over `S`. -/
private lemma leftDerivedUpperStarComp_inv_app_comp_pullbackSquareComparison_id
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {aX : X ⟶ S} {aY : Y ⟶ S}
    (sq : CommSq p₁ (p₂ ≫ aY) aX (𝟙 S)) (w : CommSq p₁ p₂ aX aY)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) :
    (leftDerivedUpperStarComp Λ p₂ aY).inv.app (L((𝟙 S)^*⟦Λ⟧).obj K) ≫
        (pullbackSquareComparison Λ sq).hom.app K =
      L((p₂)^*⟦Λ⟧).map (L((aY)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K)) ≫
        (pullbackSquareComparison Λ w).hom.app K :=
  pullbackComparison_id_comp_aux _ _ _ _ _ _ _ _ _ _
    (pullbackSquareComparison_hom_app Λ sq K)
    (leftDerivedUpperStarComp_inv_app_comp_eqToHom_id' Λ (p₂ ≫ aY) K
      (T := L((p₁ ≫ aX)^*⟦Λ⟧).obj K) (by rw [sq.w]))
    ((leftDerivedUpperStarComp Λ p₂ aY).inv.naturality ((leftDerivedUpperStarId Λ S).hom.app K))
    (pullbackSquareComparison_hom_app Λ w K)

/-- Remove the identity pullback from the comparison of a factorization. -/
private lemma leftDerivedUpperStarComp_inv_app_comp_pullbackSquareComparison_self
    {p₂ : P ⟶ Y} {aY : Y ⟶ S} (sq : CommSq p₂ (p₂ ≫ aY) aY (𝟙 S))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) :
    (leftDerivedUpperStarComp Λ p₂ aY).inv.app (L((𝟙 S)^*⟦Λ⟧).obj K) ≫
        (pullbackSquareComparison Λ sq).hom.app K =
      L((p₂)^*⟦Λ⟧).map (L((aY)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K)) :=
  pullbackComparison_id_self_aux _ _ _ _ _ _ _ _
    (pullbackSquareComparison_hom_app Λ sq K)
    (leftDerivedUpperStarComp_inv_app_comp_eqToHom_id' Λ (p₂ ≫ aY) K
      (T := L((p₂ ≫ aY)^*⟦Λ⟧).obj K) (by rw [Category.comp_id]))
    ((leftDerivedUpperStarComp Λ p₂ aY).inv.naturality ((leftDerivedUpperStarId Λ S).hom.app K))
    ((leftDerivedUpperStarComp Λ p₂ aY).inv_hom_id_app K)

/-- **A criterion for the ordinary Künneth map**: for commutative squares `p₁ ≫ a_X = q ≫ 𝟙`,
`p₂ ≫ a_Y = q ≫ 𝟙` and `p₁ ≫ a_X = p₂ ≫ a_Y`, the Künneth map
`L(𝟙)^* Ra_{X*} A ⊗ L(𝟙)^* Ra_{Y*} B ⟶ Rq_* (Lp₁^* A ⊗ Lp₂^* B)` is an isomorphism if the base
change morphism `La_Y^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A`, the projection morphism of `p₂` at
`(Lp₁^* A, B)` and the projection morphism of `a_Y` at `(B, Ra_{X*} A)` are isomorphisms. -/
theorem isIso_lowerStarKunnethMap'_of_isIso {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {aX : X ⟶ S}
    {aY : Y ⟶ S} {q : P ⟶ S} (sq₁ : CommSq p₁ q aX (𝟙 S)) (sq₂ : CommSq p₂ q aY (𝟙 S))
    (w : CommSq p₁ p₂ aX aY)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((baseChangeMap Λ w).app A))
    (h₂ : IsIso ((derivedUpperStarLowerStarAdjunction Λ p₂).projectionMorphism
      (L((p₁)^*⟦Λ⟧).obj A) B))
    (h₃ : IsIso ((derivedUpperStarLowerStarAdjunction Λ aY).projectionMorphism B
      (R((aX)_*⟦Λ⟧).obj A))) :
    IsIso (lowerStarKunnethMap' Λ sq₁ sq₂ A B) := by
  obtain rfl : q = p₂ ≫ aY := by simpa using sq₂.w.symm
  refine kunneth_isIso_of_eq_aux (lowerStarKunnethMap'_eq_homEquiv_counit Λ sq₁ sq₂ A B) ?_
  refine kunneth_of_comparison_counits (derivedUpperStarLowerStarAdjunction Λ p₂)
    (derivedUpperStarLowerStarAdjunction Λ aY) (derivedUpperStarLowerStarAdjunction Λ (p₂ ≫ aY))
    (leftDerivedUpperStarComp Λ p₂ aY) (fun U V ↦ leftDerivedUpperStarTensor_comp Λ p₂ aY U V)
    (fun U V ↦ (leftDerivedUpperStarTensor_braiding Λ aY U V).symm)
    ((leftDerivedUpperStarId Λ S).app (R((aX)_*⟦Λ⟧).obj A))
    ((leftDerivedUpperStarId Λ S).app (R((aY)_*⟦Λ⟧).obj B)) _ _ _ ?_ ?_
    (kunneth_isIso_of_eq_aux (homEquiv_pullbackSquareComparison_comp_counit Λ w A) h₁) h₂ h₃
  · exact (reassoc_of% (leftDerivedUpperStarComp_inv_app_comp_pullbackSquareComparison_id
      Λ sq₁ w (R((aX)_*⟦Λ⟧).obj A))) _
  · exact map_comp_of_comp_eq_map_aux L((p₂)^*⟦Λ⟧) _ _ _
      ((derivedUpperStarLowerStarAdjunction Λ aY).counit.app B)
      (leftDerivedUpperStarComp_inv_app_comp_pullbackSquareComparison_self
        Λ sq₂ (R((aY)_*⟦Λ⟧).obj B))

end Criterion

end AlgebraicGeometry.ProEtale.CondensedRing
