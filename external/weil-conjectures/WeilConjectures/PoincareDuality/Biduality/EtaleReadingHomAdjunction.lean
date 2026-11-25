/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Monoidal.TensorIso

/-!
# Internal homs along the right adjoint of a functor commuting with tensor products

Let `L : C ⥤ D` be a functor between monoidal closed categories with a right adjoint `G`, and
let `δ : L (X ⊗ Y) ≅ L X ⊗ L Y` be a tensor isomorphism for `L` (`CategoryTheory.Functor.TensorIso`,
no coherence required). Transposing `δ` followed by the counits gives maps
`G A ⊗ G X ⟶ G (A ⊗ X)` (`CategoryTheory.Adjunction.tensorTranspose`), natural in `A` and `X`,
and hence comparison maps `G [A, B] ⟶ [G A, G B]`
(`CategoryTheory.Adjunction.ihomComparison`), natural in `A`
(`CategoryTheory.Adjunction.map_pre_app_comp_ihomComparison`).

The comparison map is an isomorphism as soon as the counit `L G A ⟶ A` is an isomorphism
(`CategoryTheory.Adjunction.isIso_ihomComparison`): for every test object `T`, transposing
`T ⟶ G [A, B] ⟶ [G A, G B]` gives `L (G A ⊗ T) ≅ L G A ⊗ L T ≅ A ⊗ L T ⟶ B`, the uncurried
transpose of `T ⟶ G [A, B]`. This is the internal form of the projection formula
`G [L M, N] ≅ [M, G N]` for objects `A = L M` on which the counit is invertible.
-/

@[expose] public section

namespace CategoryTheory.Functor.TensorIso

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L : C ⥤ D} (δ : L.TensorIso)

/-- Naturality of a tensor isomorphism in the first variable. -/
@[reassoc]
lemma iso_hom_natural_left {X X' : C} (f : X ⟶ X') (Y : C) :
    L.map (f ▷ Y) ≫ (δ.iso X' Y).hom = (δ.iso X Y).hom ≫ L.map f ▷ L.obj Y :=
  NatTrans.congr_app (δ.hom.naturality f) Y

/-- Naturality of a tensor isomorphism in the second variable. -/
@[reassoc]
lemma iso_hom_natural_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    L.map (X ◁ g) ≫ (δ.iso X Y').hom = (δ.iso X Y).hom ≫ L.obj X ◁ L.map g :=
  (δ.hom.app X).naturality g


/-- The tensor isomorphism of the identity functor. -/
noncomputable def id (C : Type*) [Category* C] [MonoidalCategory C] : (𝟭 C).TensorIso :=
  ofComponents (fun X Y ↦ Iso.refl _) (fun _ _ ↦ by simp) (fun _ _ _ _ ↦ by simp)

/-- The tensor isomorphism of the inverse of an equivalence `e`, from a tensor isomorphism of
`e.functor`: `e⁻¹ (A ⊗ B) ≅ e⁻¹ (e e⁻¹ A ⊗ e e⁻¹ B) ≅ e⁻¹ e (e⁻¹ A ⊗ e⁻¹ B) ≅ e⁻¹ A ⊗ e⁻¹ B`. -/
noncomputable def inverse (e : C ≌ D) (τ : e.functor.TensorIso) : e.inverse.TensorIso :=
  ofCompIso e.counitIso τ ((id C).ofIso e.unitIso)

end CategoryTheory.Functor.TensorIso

namespace CategoryTheory.Adjunction

open MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) (δ : L.TensorIso)

/-- The map `G A ⊗ G X ⟶ G (A ⊗ X)` transpose of `L (G A ⊗ G X) ≅ L G A ⊗ L G X ⟶ A ⊗ X`, for an
adjunction `L ⊣ G` and a tensor isomorphism `δ` for `L`. -/
noncomputable def tensorTranspose (A X : D) : G.obj A ⊗ G.obj X ⟶ G.obj (A ⊗ X) :=
  adj.homEquiv _ _ ((δ.iso _ _).hom ≫ (adj.counit.app A ⊗ₘ adj.counit.app X))

/-- The transpose of `tensorTranspose` along `L ⊣ G` is `δ` followed by the counits. -/
lemma homEquiv_symm_tensorTranspose (A X : D) :
    (adj.homEquiv _ _).symm (adj.tensorTranspose δ A X) =
      (δ.iso _ _).hom ≫ (adj.counit.app A ⊗ₘ adj.counit.app X) :=
  Equiv.symm_apply_apply _ _

/-- `tensorTranspose` is natural in the first variable. -/
@[reassoc]
lemma tensorTranspose_natural_left {A A' : D} (f : A ⟶ A') (X : D) :
    G.map f ▷ G.obj X ≫ adj.tensorTranspose δ A' X =
      adj.tensorTranspose δ A X ≫ G.map (f ▷ X) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm,
    homEquiv_symm_tensorTranspose, homEquiv_symm_tensorTranspose, δ.iso_hom_natural_left_assoc]
  dsimp only [Functor.id_obj]
  simp only [tensorHom_def, ← comp_whiskerRight_assoc, Adjunction.counit_naturality]
  simp [whisker_exchange]

/-- `tensorTranspose` is natural in the second variable. -/
@[reassoc]
lemma tensorTranspose_natural_right (A : D) {X X' : D} (g : X ⟶ X') :
    G.obj A ◁ G.map g ≫ adj.tensorTranspose δ A X' =
      adj.tensorTranspose δ A X ≫ G.map (A ◁ g) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm,
    homEquiv_symm_tensorTranspose, homEquiv_symm_tensorTranspose, δ.iso_hom_natural_right_assoc]
  dsimp only [Functor.id_obj]
  simp only [tensorHom_def, whisker_exchange_assoc, ← whiskerLeft_comp,
    Adjunction.counit_naturality]
  simp

variable [MonoidalClosed C] [MonoidalClosed D]

/-- The comparison map `G [A, B] ⟶ [G A, G B]` for an adjunction `L ⊣ G` and a tensor
isomorphism `δ` for `L`: the curried form of
`G A ⊗ G [A, B] ⟶ G (A ⊗ [A, B]) ⟶ G B` (`CategoryTheory.Adjunction.tensorTranspose` followed
by the evaluation). -/
noncomputable def ihomComparison (A B : D) :
    G.obj ((ihom A).obj B) ⟶ (ihom (G.obj A)).obj (G.obj B) :=
  curry (adj.tensorTranspose δ A _ ≫ G.map ((ihom.ev A).app B))

/-- The comparison maps `G [A, B] ⟶ [G A, G B]` are natural in the first variable: for
`f : A' ⟶ A` they commute with precomposition by `f`. -/
@[reassoc]
lemma map_pre_app_comp_ihomComparison {A A' : D} (f : A' ⟶ A) (B : D) :
    G.map ((pre f).app B) ≫ adj.ihomComparison δ A' B =
      adj.ihomComparison δ A B ≫ (pre (G.map f)).app (G.obj B) := by
  apply uncurry_injective
  rw [uncurry_natural_left, ihomComparison, uncurry_curry, uncurry_pre_app, ihomComparison,
    uncurry_curry, tensorTranspose_natural_right_assoc, ← G.map_comp, id_tensor_pre_app_comp_ev,
    G.map_comp, tensorTranspose_natural_left_assoc]

/-- Transposing `g ≫ c` along the tensor-hom adjunction and `L ⊣ G`, for `g : T ⟶ G [A, B]` and
`c` the comparison map, gives `L (G A ⊗ T) ≅ L G A ⊗ L T ⟶ A ⊗ L T ⟶ B`, the last map being the
uncurried transpose of `g`. -/
lemma homEquiv_symm_uncurry_comp_ihomComparison {A B : D} {T : C}
    (g : T ⟶ G.obj ((ihom A).obj B)) :
    (adj.homEquiv _ _).symm (uncurry (g ≫ adj.ihomComparison δ A B)) =
      ((δ.iso _ _).hom ≫ adj.counit.app A ▷ L.obj T) ≫
        uncurry ((adj.homEquiv _ _).symm g) := by
  rw [uncurry_natural_left, ihomComparison, uncurry_curry, ← Category.assoc,
    adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_left_symm,
    homEquiv_symm_tensorTranspose, adj.homEquiv_counit, uncurry_eq]
  simp only [Category.assoc]
  rw [δ.iso_hom_natural_right_assoc]
  simp [tensorHom_def, whisker_exchange_assoc]

/-- **Internal projection formula.** For an adjunction `L ⊣ G` and a tensor isomorphism `δ` for
`L`, the comparison map `G [A, B] ⟶ [G A, G B]` is an isomorphism if the counit `L G A ⟶ A` is
an isomorphism. -/
theorem isIso_ihomComparison (A B : D) [IsIso (adj.counit.app A)] :
    IsIso (adj.ihomComparison δ A B) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have he : Function.Bijective
      (fun h : T ⟶ (ihom (G.obj A)).obj (G.obj B) ↦ (adj.homEquiv _ _).symm (uncurry h)) :=
    ⟨fun a b h ↦ uncurry_injective ((adj.homEquiv _ _).symm.injective h),
      fun y ↦ ⟨curry (adj.homEquiv _ _ y), by simp⟩⟩
  rw [← Function.Bijective.of_comp_iff' he]
  have hc : Function.Bijective (fun g : T ⟶ G.obj ((ihom A).obj B) ↦
      ((δ.iso _ _).hom ≫ adj.counit.app A ▷ L.obj T) ≫ uncurry ((adj.homEquiv _ _).symm g)) :=
    ⟨fun a b h ↦ (adj.homEquiv _ _).symm.injective (uncurry_injective ((cancel_epi _).1 h)),
      fun y ↦ ⟨adj.homEquiv _ _ (curry (inv ((δ.iso _ _).hom ≫ adj.counit.app A ▷ L.obj T) ≫ y)),
        by simp⟩⟩
  convert hc using 1
  funext g
  exact adj.homEquiv_symm_uncurry_comp_ihomComparison δ g

/-- The comparison isomorphism `G [ι A, ι B] ≅ [F A, F B]`
(`CategoryTheory.Adjunction.ihomComparison` followed by `eqToIso`) for a functor `ι : C' ⥤ D`
and a functor `F` equal to `ι ⋙ G`, when the counit `L G ι A ⟶ ι A` is an isomorphism.

Stating it for an abstract `F` with an equation `ι ⋙ G = F` (instead of relying on the
definitional equality `F.obj A = G.obj (ι.obj A)`) keeps the kernel from unfolding `F` and `G`
when checking terms involving this isomorphism. -/
noncomputable def ihomComparisonIsoOfCompEq {C' : Type*} [Category* C'] (ι : C' ⥤ D)
    (F : C' ⥤ C) (hF : ι ⋙ G = F) (A B : C') [hA : IsIso (adj.counit.app (ι.obj A))] :
    G.obj ((ihom (ι.obj A)).obj (ι.obj B)) ≅ (ihom (F.obj A)).obj (F.obj B) :=
  have := adj.isIso_ihomComparison δ (ι.obj A) (ι.obj B)
  asIso (adj.ihomComparison δ (ι.obj A) (ι.obj B)) ≪≫ eqToIso (by subst hF; rfl)

/-- The isomorphisms `CategoryTheory.Adjunction.ihomComparisonIsoOfCompEq` are natural in the
first variable. -/
lemma map_pre_app_comp_ihomComparisonIsoOfCompEq_hom {C' : Type*} [Category* C'] (ι : C' ⥤ D)
    (F : C' ⥤ C) (hF : ι ⋙ G = F) {A A' : C'} (f : A ⟶ A') (B : C')
    [hA : IsIso (adj.counit.app (ι.obj A))] [hA' : IsIso (adj.counit.app (ι.obj A'))] :
    G.map ((pre (ι.map f)).app (ι.obj B)) ≫ (adj.ihomComparisonIsoOfCompEq δ ι F hF A B).hom =
      (adj.ihomComparisonIsoOfCompEq δ ι F hF A' B).hom ≫ (pre (F.map f)).app (F.obj B) := by
  subst hF
  simpa [ihomComparisonIsoOfCompEq] using
    adj.map_pre_app_comp_ihomComparison δ (ι.map f) (ι.obj B)

end CategoryTheory.Adjunction
