/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.SupportsDerived

/-!
# Functoriality of the supported localization triangle in the pair

Let `e : X' ⟶ X` be a morphism of schemes, `i : Z ⟶ X` and `i' : Z' ⟶ X'` closed immersions with
open complements `j : U ⟶ X` and `j' : U' ⟶ X'`, and suppose that `e` maps `U'` into `U`, i.e.
`e⁻¹(Z) ⊆ Z'`: a *morphism of pairs* `(X', U') ⟶ (X, U)`. For `L` on `X`, `L'` on `X'` and
`τ : Le^* L ⟶ L'`, there is a unique morphism of triangles from the pullback of the supported
localization triangle

`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ (Ri_! Ri^! L)[1]`

to the supported localization triangle of `L'` for the pair `(Z', U')` whose middle component is
`τ` (`AlgebraicGeometry.Etale.existsUnique_triangleHom_supportedLocalizationTriangle`). Indeed the
pullback of `Ri_! Ri^! L` is supported on `e⁻¹(Z) ⊆ Z'`, so it admits no nonzero maps, even
after a shift, to `Rj'_* Lj'^* L'`; this pins down the first and the third components.

Uniqueness makes the morphisms compatible with composition of morphisms of pairs, and for the
base change pair it is `AlgebraicGeometry.Etale.supportedLocalizationTriangleBaseChange`.
Applying a homological functor (for instance `Hom(Λ, -)` or `RΓ` followed by cohomology) and
`CategoryTheory.Functor.homologySequenceδ_naturality`, the long exact sequences of cohomology
with supports are functorial in the pair; with `RΓ_Z(X, -) ≅ RΓ(X, Ri_! Ri^! -)`
(`AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIso`) this is the functoriality in the
pair of blueprint `thm-pur-with-support-exactness` for arbitrary morphisms of schemes.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X X' Z Z' U U' : Scheme.{u}}

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support
(functoriality in the pair, for arbitrary morphisms of pairs).

Let `e : X' ⟶ X` be a morphism mapping the open complement `U'` of the closed immersion
`i' : Z' ⟶ X'` into the open complement `U` of the closed immersion `i : Z ⟶ X` (so that
`e⁻¹(Z) ⊆ Z'`). For `L` on `X`, `L'` on `X'` and `τ : Le^* L ⟶ L'`, there is a unique morphism of
triangles from `Le^*` of the supported localization triangle
`Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶ (Ri_! Ri^! L)[1]` to the supported localization triangle of
`L'` for `(Z', U')` with middle component `τ`. Both triangles are distinguished, so the induced
maps of long exact sequences are compatible with the connecting maps. -/
theorem existsUnique_triangleHom_supportedLocalizationTriangle (e : X' ⟶ X) (i : Z ⟶ X)
    (j : U ⟶ X) (i' : Z' ⟶ X') (j' : U' ⟶ X')
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (he : Set.range (j' ≫ e).base ⊆ Set.range j.base)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ⟶ L') :
    ∃! φ : (L((e)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
        (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L)) ⟶
      supportedLocalizationTriangle Λ i' j' L' (supportedLocalizationBoundary Λ i' j' hij' L'),
      φ.hom₂ = τ := by
  set T := (L((e)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
    (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L))
  set T' := supportedLocalizationTriangle Λ i' j' L' (supportedLocalizationBoundary Λ i' j' hij' L')
  have hT : T ∈ distTriang _ :=
    (L((e)^*[ModuleCat.{u + 1} Λ])).map_distinguished _
        (supportedLocalizationTriangle_mem_distTriang Λ i j hij L)
  have hT' : T' ∈ distTriang _ := supportedLocalizationTriangle_mem_distTriang Λ i' j' hij' L'
  -- the pullback of the supported term is supported on `e⁻¹(Z) ⊆ Z'`
  have hZ : IsZero ((L((j')^*[ModuleCat.{u + 1} Λ])).obj T.obj₁) :=
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i j
      (by rw [hij]; exact disjoint_compl_left) (j' ≫ e) he _).of_iso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j' e).app _).symm
  have : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) :=
    subsingleton_hom_rightDerivedLowerStar_of_isZero (ModuleCat.{u + 1} Λ) j'
      (((shiftFunctor _ (1 : ℤ)).map_isZero hZ).of_iso
        (((L((j')^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app _)) _
  obtain ⟨a, ha, ha'⟩ := existsUnique_comp_counit_of_isZero Λ i' j' hij' hZ (T.mor₁ ≫ τ)
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism T T' hT hT'
    a τ ha.symm
  refine ⟨Triangle.homMk T T' a τ c ha.symm hc₂ hc₃, rfl, fun ψ hψ ↦ ?_⟩
  have h₁ : ψ.hom₁ = a := ha' _ (by
    change ψ.hom₁ ≫ T'.mor₁ = T.mor₁ ≫ τ
    rw [← ψ.comm₁, hψ])
  have h₃ : ψ.hom₃ = c :=
    Triangle.cancel_mor₂_of_subsingleton hT (by rw [ψ.comm₂, hψ, hc₂])
  exact Triangle.hom_ext _ _ h₁ hψ h₃

/-- For the base change pair `(Z ×_X X', U ×_X X')` of `(Z, U)` along `e : X' ⟶ X`, the unique
morphism of triangles of
`AlgebraicGeometry.Etale.existsUnique_triangleHom_supportedLocalizationTriangle` with middle
component `τ` is `AlgebraicGeometry.Etale.supportedLocalizationTriangleBaseChange`, whose first
component is the restriction of supports and whose third component is the derived base change
map. -/
theorem supportedLocalizationTriangleBaseChange_eq_of_hom₂_eq (e : X' ⟶ X) (i : Z ⟶ X)
    (j : U ⟶ X) (i' : Z' ⟶ X') (j' : U' ⟶ X') (g : Z' ⟶ Z) (e₁ : U' ⟶ U)
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (hg : IsPullback g i' i e) (sq : CommSq e₁ j' j e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (τ :
        (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (φ : (L((e)^*[ModuleCat.{u + 1} Λ])).mapTriangle.obj
        (supportedLocalizationTriangle Λ i j L (supportedLocalizationBoundary Λ i j hij L)) ⟶
      supportedLocalizationTriangle Λ i' j' L' (supportedLocalizationBoundary Λ i' j' hij' L'))
    (hφ : φ.hom₂ = τ.hom) :
    φ = supportedLocalizationTriangleBaseChange Λ e i j i' j' g e₁ hij hij' hg sq L L' τ := by
  have he : Set.range (j' ≫ e).base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e₁.base x, by rw [← sq.w]; simp⟩
  exact (existsUnique_triangleHom_supportedLocalizationTriangle Λ e i j i' j' hij hij' he L L'
    τ.hom).unique hφ rfl

end Etale

end AlgebraicGeometry
