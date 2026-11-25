/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition

/-!
# Invertibility is local for jointly surjective étale families

An object `L` of `D(X_ét, Λ)` is ⊗-invertible as soon as its derived pullbacks `Lu_i^* L` along
a jointly surjective family of étale morphisms `u_i : U_i ⟶ X` (for instance an open cover) are
invertible. This is the family version of
`AlgebraicGeometry.Etale.isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale`; it needs
neither a finite family nor a single étale surjection.

## Main statements

- `CategoryTheory.isIso_map_ev_of_isIso_ihomComparison`: a monoidal functor commuting with duals
  sends the evaluation `A ⊗ [A, 𝟙] ⟶ 𝟙` to an isomorphism when it sends `A` to an invertible
  object.
- `AlgebraicGeometry.Etale.isIso_of_forall_isIso_leftDerivedUpperStar_map_of_family`:
  isomorphisms of `D(X_ét, Λ)` are detected by a jointly surjective family of pullbacks.
- `AlgebraicGeometry.Etale.isInvertible_of_forall_isInvertible_leftDerivedUpperStar`
-/

@[expose] public section

universe u

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]

/-- Let `G` be a monoidal functor between closed monoidal categories, `D` braided, and `A` an
object for which the comparison `G [A, 𝟙] ⟶ [G A, G 𝟙]` is an isomorphism. If `G A` is
invertible, then `G` sends the evaluation `A ⊗ [A, 𝟙] ⟶ 𝟙` to an isomorphism: up to the
comparison and the tensorator it is the evaluation of the invertible object `G A`. -/
theorem isIso_map_ev_of_isIso_ihomComparison [MonoidalClosed C] [BraidedCategory D]
    [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal] {A : C}
    [IsIso ((ihomComparison G A).app (𝟙_ C))] (h : IsInvertible (G.obj A)) :
    IsIso (G.map ((ihom.ev A).app (𝟙_ C))) := by
  have := h.isIso_ev (G.obj (𝟙_ C))
  have h₁ := ihomComparison_ev G A (𝟙_ C)
  have : IsIso (μ G A ((ihom A).obj (𝟙_ C)) ≫ G.map ((ihom.ev A).app (𝟙_ C))) := by
    rw [← h₁]
    infer_instance
  exact IsIso.of_isIso_comp_left (μ G A ((ihom A).obj (𝟙_ C))) _

end CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Blueprint `lem-pur-etale-iso-descent`: Isomorphisms descend along étale surjections (family
version).

Let `a i : U i ⟶ X` be a jointly surjective family of morphisms and `φ : M ⟶ N` a morphism of
`D(X_ét, Λ)`. If every `La_i^* φ` is an isomorphism, then so is `φ`: the cohomology sheaves
`ℋʳ(φ)` are isomorphisms, as `a_i^* ℋʳ(φ) ≅ ℋʳ(La_i^* φ)` and every geometric point of `X` lifts
to some `U i`. -/
theorem isIso_of_forall_isIso_leftDerivedUpperStar_map_of_family {X : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X) (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((a i)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha _
    fun i ↦ ?_
  have h' : IsIso (D((a i)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (a i)) φ).1 (h i)
  exact (NatIso.isIso_map_iff
    (((a i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((a i)^*[ModuleCat.{u + 1} Λ]).map φ))

/-- For an étale `u : U ⟶ X` and `L ∈ D(X_ét, Λ)` with `Lu^* L` invertible, the derived pullback
of the evaluation `L ⊗ᴸ RHom(L, Λ) ⟶ Λ` is an isomorphism, the derived pullback along `u`
commuting with the derived internal hom
(`AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedUpperStar_of_etale`). -/
theorem isIso_leftDerivedUpperStar_map_ev_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : DerivedCategory.isInvertible Λ U ((L((u)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    IsIso ((L((u)^*[ModuleCat.{u + 1} Λ])).map ((ihom.ev L).app (𝟙_ _))) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) u
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := isIso_ihomComparison_leftDerivedUpperStar_of_etale Λ u L
  exact isIso_map_ev_of_isIso_ihomComparison L((u)^*[ModuleCat.{u + 1} Λ])
    ((isInvertible_iff_exists_derivedTensor _).2 h)

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality (family version).

Invertibility is local for a jointly surjective family of étale morphisms `a i : U i ⟶ X`: if
every `La_i^* L` is invertible, then so is `L`. The evaluation `L ⊗ᴸ RHom(L, Λ) ⟶ Λ` pulls back
to an isomorphism along every `a i`
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_ev_of_etale`), and isomorphisms are
detected by the family
(`AlgebraicGeometry.Etale.isIso_of_forall_isIso_leftDerivedUpperStar_map_of_family`).
-/
theorem isInvertible_of_forall_isInvertible_leftDerivedUpperStar {X : Scheme.{u}} {ι : Type u}
    {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)]
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ i, DerivedCategory.isInvertible Λ (U i) ((L((a i)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    DerivedCategory.isInvertible Λ X L := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := isIso_of_forall_isIso_leftDerivedUpperStar_map_of_family Λ a ha _
    fun i ↦ isIso_leftDerivedUpperStar_map_ev_of_etale Λ (a i) L (h i)
  exact (isInvertible_iff_exists_derivedTensor _).1
    ((isInvertible_iff_of_braided L).2 ⟨_, ⟨asIso ((ihom.ev L).app (𝟙_ _))⟩⟩)

end Etale

end AlgebraicGeometry
