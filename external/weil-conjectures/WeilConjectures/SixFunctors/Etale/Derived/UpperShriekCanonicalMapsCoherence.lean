/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!
# Composition of the tensor maps of `Rf^!`

For a morphism `f : X ⟶ Y` admitting a compactification and satisfying the projection formula,
and a right adjoint `G` of `Rf_!` (for a finite coefficient ring, `G = Rf^!`), the *tensor map*
`τ_f(M, N) : G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap`) is the transpose of the inverse
projection map followed by the counit; at `M = Λ_Y` it is the canonical map
`θ_{f,N} : ω_f ⊗ᴸ Lf^* N ⟶ G N`, `ω_f = G Λ_Y`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`).
This file derives, for any coefficient category, the formal properties of `τ` and its behaviour
under composition used for cohomologically smooth morphisms
(`lem-pur-co-smooth-composition`, `lem-pur-co-smooth-etale-locality`), from two coherence
properties of the projection map: its compatibility with the associativity of `⊗ᴸ`
(`AlgebraicGeometry.Etale.ProjectionMapAssociativity`) and with a composition isomorphism
`Rh_! ≅ Rf_! ⋙ Rg_!` (`CategoryTheory.Adjunction.ProjectionCompCompatible`). Both hold for
finite coefficients (`proposition-composition-base-change-rf-shriek--1`).

## Main statements

- `AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap_comp`: the tensor map of a
  composite is the composite of the tensor maps.
- `AlgebraicGeometry.Etale.isIso_lowerShriekRightAdjointUnitTensorMap_comp`: `θ_{f ≫ g, K}` is
  an isomorphism if `θ_{f, Lg^* K}` and `θ_{g, K}` are and `ω_g` is invertible.
- `AlgebraicGeometry.Etale.isIso_map_lowerShriekRightAdjointUnitTensorMap_of_comp`: if
  `θ_{u ≫ f, K}` is an isomorphism and `θ_u` is one everywhere, then `Gu θ_{f, K}` is one.
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map`:
  `Gu` reflects isomorphisms to `Lu^*` when `θ_u` is invertible and `ω_u` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product: otherwise `⊗` and `derivedTensor` use different instances, and unifying them
-- is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- Braid étale sheaves through `Etale.sheafBraidedCategory`, as the generic definitions of the
-- derived tensor product do (see `LowerShriekProjectionExchange`), rather than through the
-- symmetric structure found by the line above.
attribute [local instance 20000] Etale.sheafBraidedCategory

section Predicates

variable (A)

/-- The projection map `PF : Rf_!M ⊗ᴸ N ⟶ Rf_!(M ⊗ᴸ Lf^*N)` of `f` is compatible with the
associativity of the derived tensor product: the two maps
`(Rf_!M ⊗ᴸ N) ⊗ᴸ N' ⟶ Rf_!(M ⊗ᴸ (Lf^*N ⊗ᴸ Lf^*N'))`, applying the projection map twice, or once
to `N ⊗ᴸ N'` followed by the tensor comparison `Lf^*(N ⊗ᴸ N') ≅ Lf^*N ⊗ᴸ Lf^*N'`, agree. -/
structure ProjectionMapAssociativity {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Prop where
  assoc : ∀ (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      ((projectionMap A f).app M).app N ▷ N' ≫
          ((projectionMap A f).app (M ⊗ (L((f)^*[A])).obj N)).app N' ≫
          (R(f)_![A]).map (α_ M _ _).hom =
        (α_ _ N N').hom ≫ ((projectionMap A f).app M).app (N ⊗ N') ≫
          (R(f)_![A]).map (M ◁ (leftDerivedUpperStarTensorIso A f N N').hom)

end Predicates

section Invertible

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The derived pullback of an invertible object is invertible. -/
lemma isInvertible_leftDerivedUpperStar_obj
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hN : IsInvertible N) :
    IsInvertible ((L((f)^*[A])).obj N) := by
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  exact ⟨(L((f)^*[A])).obj N', ⟨(leftDerivedUpperStarTensorIso A f N N').symm ≪≫
      (L((f)^*[A])).mapIso e ≪≫ leftDerivedUpperStarUnitIso A f⟩,
    ⟨(leftDerivedUpperStarTensorIso A f N' N).symm ≪≫ (L((f)^*[A])).mapIso e' ≪≫
      leftDerivedUpperStarUnitIso A f⟩⟩

end Invertible

section TensorMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

lemma projectionMap_app_app_naturality_left
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(f)_![A]).map φ ▷ N ≫ ((projectionMap A f).app M').app N =
      ((projectionMap A f).app M).app N ≫ (R(f)_![A]).map (φ ▷ (L((f)^*[A])).obj N) :=
  NatTrans.congr_app ((projectionMap A f).naturality φ) N

lemma projectionMap_app_app_naturality_right
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (φ : N ⟶ N') :
    (R(f)_![A]).obj M ◁ φ ≫ ((projectionMap A f).app M).app N' =
      ((projectionMap A f).app M).app N ≫ (R(f)_![A]).map (M ◁ (L((f)^*[A])).map φ) :=
  ((projectionMap A f).app M).naturality φ

variable [IsIso (projectionMap A f)] {f}
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(f)_![A] ⊣ G)

lemma lowerShriekRightAdjointUnitTensorMap_eq
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    lowerShriekRightAdjointUnitTensorMap adj K =
      lowerShriekRightAdjointTensorMap adj (𝟙_ _) K ≫ G.map (λ_ K).hom :=
  rfl

lemma isIso_lowerShriekRightAdjointUnitTensorMap_iff
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (lowerShriekRightAdjointUnitTensorMap adj K) ↔
      IsIso (lowerShriekRightAdjointTensorMap adj (𝟙_ _) K) := by
  rw [lowerShriekRightAdjointUnitTensorMap_eq, isIso_comp_right_iff]

/-- The tensor map at an invertible second variable is an isomorphism. -/
lemma isIso_lowerShriekRightAdjointTensorMap_of_isInvertible
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hN : IsInvertible N) :
    IsIso (lowerShriekRightAdjointTensorMap adj M N) :=
  Adjunction.isIso_projectionTensorMap_of_isInvertible _ _
    (projectionMap_app_app_naturality_left f) hN (isInvertible_leftDerivedUpperStar_obj f hN) M

/-- The tensor map at `(M, N')` is an isomorphism if it is one at `(M, N)` for `N ≅ N'`. -/
lemma isIso_lowerShriekRightAdjointTensorMap_of_iso_right
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : N ≅ N')
    [IsIso (lowerShriekRightAdjointTensorMap adj M N)] :
    IsIso (lowerShriekRightAdjointTensorMap adj M N') :=
  Adjunction.isIso_projectionTensorMap_of_iso_right adj _
    (projectionMap_app_app_naturality_right f) e

/-- The tensor map at `(M', N)` is an isomorphism if it is one at `(M, N)` for `M ≅ M'`. -/
lemma isIso_lowerShriekRightAdjointTensorMap_of_iso_left
    {M M' N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : M ≅ M')
    [IsIso (lowerShriekRightAdjointTensorMap adj M N)] :
    IsIso (lowerShriekRightAdjointTensorMap adj M' N) :=
  Adjunction.isIso_projectionTensorMap_of_iso_left adj _
    (projectionMap_app_app_naturality_left f) e

variable {adj} (hassoc : ProjectionMapAssociativity A f)
include hassoc

/-- The tensor map at `(M ⊗ N, N')` is an isomorphism if it is one at `(M, N)` and at
`(M, N ⊗ N')`. -/
lemma isIso_lowerShriekRightAdjointTensorMap_tensor_left
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    [IsIso (lowerShriekRightAdjointTensorMap adj M N)]
    [IsIso (lowerShriekRightAdjointTensorMap adj M (N ⊗ N'))] :
    IsIso (lowerShriekRightAdjointTensorMap adj (M ⊗ N) N') :=
  Adjunction.isIso_projectionTensorMap_tensor_left adj _
    (projectionMap_app_app_naturality_left f)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom) hassoc.assoc

/-- The tensor map at `(M, N ⊗ N')` is an isomorphism if it is one at `(M, N)` and at
`(M ⊗ N, N')`. -/
lemma isIso_lowerShriekRightAdjointTensorMap_tensor_right
    {M N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    [IsIso (lowerShriekRightAdjointTensorMap adj M N)]
    [IsIso (lowerShriekRightAdjointTensorMap adj (M ⊗ N) N')] :
    IsIso (lowerShriekRightAdjointTensorMap adj M (N ⊗ N')) :=
  Adjunction.isIso_projectionTensorMap_tensor_right adj _
    (projectionMap_app_app_naturality_left f)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom) hassoc.assoc

variable (adj) in
/-- If `θ_f` is an isomorphism at every object, then so is every tensor map of `f`. -/
lemma isIso_lowerShriekRightAdjointTensorMap_of_forall
    (hf : ∀ P, IsIso (lowerShriekRightAdjointUnitTensorMap adj P))
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (lowerShriekRightAdjointTensorMap adj M N) := by
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adj M).1 (hf M)
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adj (M ⊗ N)).1 (hf _)
  have := isIso_lowerShriekRightAdjointTensorMap_tensor_left hassoc (adj := adj) (M := 𝟙_ _)
    (N := M) (N' := N)
  exact isIso_lowerShriekRightAdjointTensorMap_of_iso_left adj (λ_ M)

end TensorMap

section Composition

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (w : f ≫ g = h)
  [HasCompactification f] [HasCompactification g] [HasCompactification h]
  [IsIso (projectionMap A f)] [IsIso (projectionMap A g)] [IsIso (projectionMap A h)]
  {Gf : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adjf : R(f)_![A] ⊣ Gf)
  {Gg : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (adjg : R(g)_![A] ⊣ Gg)
  {Gh : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adjh : R(h)_![A] ⊣ Gh)
  (e : R(h)_![A] ≅ R(f)_![A] ⋙ R(g)_![A])
  (he : Adjunction.ProjectionCompCompatible (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M N ↦ ((projectionMap A g).app M).app N) (fun M N ↦ ((projectionMap A h).app M).app N)
    (fun N ↦ (leftDerivedUpperStarComp A f g h w.symm).hom.app N) e)
include he

set_option hygiene false in
/-- The isomorphism `Gh ≅ Gg ⋙ Gf` of right adjoints induced by `e`. -/
local notation "ρ[" e "]" =>
  Adjunction.rightAdjointUniq (adjh.ofNatIsoLeft e) (adjf.comp adjg)

/-- **The tensor map of a composite.** For `h = f ≫ g`, right adjoints `Gf`, `Gg`, `Gh` of
`Rf_!`, `Rg_!`, `Rh_!` (for finite coefficients, `Rf^!`, `Rg^!`, `Rh^!`) and a composition
isomorphism `e : Rh_! ≅ Rf_! ⋙ Rg_!` compatible with the projection maps, the tensor map of `h`
is, through the induced isomorphism `ρ : Gh ≅ Gg ⋙ Gf`, the composite of the tensor map of `f`
at `(Gg M, Lg^* N)` and of `Gf` of the tensor map of `g` at `(M, N)`. -/
theorem lowerShriekRightAdjointTensorMap_comp
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    lowerShriekRightAdjointTensorMap adjh M N ≫ (ρ[e]).hom.app (M ⊗ N) =
      (ρ[e]).hom.app M ▷ (L((h)^*[A])).obj N ≫
        Gf.obj (Gg.obj M) ◁ (leftDerivedUpperStarComp A f g h w.symm).hom.app N ≫
        lowerShriekRightAdjointTensorMap adjf (Gg.obj M) ((L((g)^*[A])).obj N) ≫
        Gf.map (lowerShriekRightAdjointTensorMap adjg M N) :=
  Adjunction.projectionTensorMap_comp_rightAdjointUniq adjf adjg adjh _ _ _
    (projectionMap_app_app_naturality_left f) (projectionMap_app_app_naturality_left g) _ e he M N

/-- **Composition of the canonical maps.** For `h = f ≫ g` with a composition isomorphism
compatible with the projection maps and an associative projection map of `f`: if `ω_g = Gg Λ`
is invertible and `θ_{g, K}` and `θ_{f, Lg^* K}` are isomorphisms, then so is `θ_{h, K}`. The
tensor map of `h` at `(Λ, K)` factors through `τ_f(ω_g, Lg^* K)` and `Gf θ_{g, K}`; the first
is an isomorphism since `ω_g` is invertible and `θ_f` is invertible at
`Lg^* K ⊗ᴸ ω_g ≅ ω_g ⊗ᴸ Lg^* K` (`lem-pur-co-smooth-composition`). -/
theorem isIso_lowerShriekRightAdjointUnitTensorMap_comp (hassoc : ProjectionMapAssociativity A f)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hf : IsIso (lowerShriekRightAdjointUnitTensorMap adjf ((L((g)^*[A])).obj K)))
    (hg : IsIso (lowerShriekRightAdjointUnitTensorMap adjg K))
    (hω : IsInvertible (Gg.obj (𝟙_ _))) :
    IsIso (lowerShriekRightAdjointUnitTensorMap adjh K) := by
  rw [isIso_lowerShriekRightAdjointUnitTensorMap_iff]
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adjg K).1 hg
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adjf _).1 hf
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adjf
    (𝟙_ _ ⊗ (L((g)^*[A])).obj K) (N := Gg.obj (𝟙_ _)) hω
  have := isIso_lowerShriekRightAdjointTensorMap_tensor_right hassoc (adj := adjf) (M := 𝟙_ _)
    (N := (L((g)^*[A])).obj K) (N' := Gg.obj (𝟙_ _))
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip A Y
  have := isIso_lowerShriekRightAdjointTensorMap_of_iso_right adjf (M := 𝟙_ _)
    (N := (L((g)^*[A])).obj K ⊗ Gg.obj (𝟙_ _))
    (N' := Gg.obj (𝟙_ _) ⊗ (L((g)^*[A])).obj K)
    ((β.app ((L((g)^*[A])).obj K)).app (Gg.obj (𝟙_ _)))
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adjf (𝟙_ _)
    (N := Gg.obj (𝟙_ _)) hω
  have := isIso_lowerShriekRightAdjointTensorMap_tensor_left hassoc (adj := adjf) (M := 𝟙_ _)
    (N := Gg.obj (𝟙_ _)) (N' := (L((g)^*[A])).obj K)
  have := isIso_lowerShriekRightAdjointTensorMap_of_iso_left adjf (N := (L((g)^*[A])).obj K)
    (λ_ (Gg.obj (𝟙_ _)))
  have hc := lowerShriekRightAdjointTensorMap_comp w adjf adjg adjh e he (𝟙_ _) K
  have : IsIso (lowerShriekRightAdjointTensorMap adjh (𝟙_ _) K ≫
      (ρ[e]).hom.app (𝟙_ _ ⊗ K)) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ρ[e]).hom.app (𝟙_ _ ⊗ K))

/-- **Descent of the canonical maps along a composite.** For `h = u ≫ f` with a composition
isomorphism compatible with the projection maps and an associative projection map of `u`: if
`θ_u` is an isomorphism at every object and `θ_{h, K}` is an isomorphism, then so is
`Gu θ_{f, K}` (`lem-pur-co-smooth-etale-locality`, step 3). -/
theorem isIso_map_lowerShriekRightAdjointUnitTensorMap_of_comp
    (hassoc : ProjectionMapAssociativity A f)
    (hf : ∀ P, IsIso (lowerShriekRightAdjointUnitTensorMap adjf P))
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hh : IsIso (lowerShriekRightAdjointUnitTensorMap adjh K)) :
    IsIso (Gf.map (lowerShriekRightAdjointUnitTensorMap adjg K)) := by
  rw [isIso_lowerShriekRightAdjointUnitTensorMap_iff] at hh
  have := isIso_lowerShriekRightAdjointTensorMap_of_forall adjf hassoc hf (Gg.obj (𝟙_ _))
    ((L((g)^*[A])).obj K)
  have hc := lowerShriekRightAdjointTensorMap_comp w adjf adjg adjh e he (𝟙_ _) K
  have : IsIso (lowerShriekRightAdjointTensorMap adjh (𝟙_ _) K ≫
      (ρ[e]).hom.app (𝟙_ _ ⊗ K)) :=
    inferInstance
  rw [hc] at this
  have := (isIso_comp_left_iff _ _).1 this
  have := (isIso_comp_left_iff _ _).1 this
  have : IsIso (Gf.map (lowerShriekRightAdjointTensorMap adjg (𝟙_ _) K)) :=
    (isIso_comp_left_iff _ _).1 this
  rw [lowerShriekRightAdjointUnitTensorMap_eq, Functor.map_comp]
  infer_instance

end Composition

section Reflect

variable {U X : Scheme.{u}} {u : U ⟶ X} [HasCompactification u] [IsIso (projectionMap A u)]
  {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)} (adj : R(u)_![A] ⊣ G)

/-- If `θ_u` is an isomorphism at every object and `ω_u = G Λ` is invertible, then the right
adjoint `G` of `Ru_!` (for finite coefficients, `Ru^!`) reflects isomorphisms to `Lu^*`:
`G ≅ ω_u ⊗ᴸ Lu^*(-)`, and tensoring with an invertible object reflects isomorphisms. -/
theorem isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
    (hu : ∀ P, IsIso (lowerShriekRightAdjointUnitTensorMap adj P))
    (hω : IsInvertible (G.obj (𝟙_ _)))
    {P Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : P ⟶ Q)
    (h : IsIso (G.map φ)) : IsIso ((L((u)^*[A])).map φ) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf U.smallEtaleTopology A)
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adj P).1 (hu P)
  have := (isIso_lowerShriekRightAdjointUnitTensorMap_iff adj Q).1 (hu Q)
  have hn := Adjunction.projectionTensorMap_naturality_right
    adj _ (projectionMap_app_app_naturality_right u) (𝟙_ _) φ
  have : IsIso (G.map (𝟙_ _ ◁ φ)) := by
    rw [id_whiskerLeft, Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso (G.obj (𝟙_ _) ◁ (L((u)^*[A])).map φ ≫
      lowerShriekRightAdjointTensorMap adj (𝟙_ _) Q) := by
    erw [hn]
    infer_instance
  have : IsIso (G.obj (𝟙_ _) ◁ (L((u)^*[A])).map φ) :=
    IsIso.of_isIso_comp_right _ (lowerShriekRightAdjointTensorMap adj (𝟙_ _) Q)
  exact hω.isIso_of_isIso_whiskerLeft _

end Reflect

end Etale

end AlgebraicGeometry
