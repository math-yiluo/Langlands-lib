/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback

/-!

# Reduction of the supported restriction to a punctured restriction

Let `b : B ⟶ T` be a morphism of schemes, `a : G ⟶ T` and `y : Y ⟶ B` closed immersions with
`b⁻¹(G) ⊆ Y`. For a bounded below complex `P` of étale sheaves on `T`, the *supported restriction*
`ρ_{a,b} : RΓ_G(T, P) ⟶ RΓ_Y(B, b^* P)` is the pullback of sections with supports along `b`
(`AlgebraicGeometry.Etale.sectionsWithSupportRestriction`, blueprint
`lemma-local-term-restriction-map--1`, item 2: the ordinary pullback along `b` of the support
object, followed by the exchange to local cohomology with support in the intersection). It is the
first component of the morphism of localization triangles
```
RΓ_G(T, P) ⟶ RΓ(T, P) ⟶ RΓ(T ∖ G, P) ⟶ RΓ_G(T, P)[1]
    ↓ρ           ↓            ↓r
RΓ_Y(B, b^*P) ⟶ RΓ(B, b^*P) ⟶ RΓ(B ∖ Y, b^*P) ⟶ RΓ_Y(B, b^*P)[1]
```
(`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback`). When both middle terms vanish,
the connecting maps are isomorphisms and identify `ρ_{a,b}`, shifted by one, with the ordinary
restriction `r` (blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (iii)); in particular
`ρ_{a,b} = 0` if and only if `r = 0`
(`AlgebraicGeometry.Etale.sectionsWithSupportRestriction_eq_zero_iff`).

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {T B G Y : Scheme.{u}} (b : B ⟶ T) (a : G ⟶ T) [IsClosedImmersion a] (y : Y ⟶ B)
  [IsClosedImmersion y] (h : y.openComplement ≤ b ⁻¹ᵁ a.openComplement)

/-- The **supported restriction** `ρ_{a,b} : RΓ_G(T, P) ⟶ RΓ_Y(B, b^* P)` (blueprint
`lemma-local-term-restriction-map--1`, item 2) along `b : B ⟶ T`, for closed immersions `a : G ⟶ T`
and `y : Y ⟶ B` with `b⁻¹(G) ⊆ Y`: the pullback of sections with supports, the first component of
the morphism of localization triangles `sectionsWithSupportTrianglePullback`. -/
noncomputable def sectionsWithSupportRestriction
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)) :
    ((sectionsWithSupportTriangle A a).obj P).obj₁ ⟶
      ((sectionsWithSupportTriangle A y).obj
        ((Functor.mapDerivedCategoryPlus (b)^*[A]).obj P)).obj₁ :=
  ((sectionsWithSupportTrianglePullback A b a y h).app P).hom₁

/-- The **punctured restriction** `RΓ(T ∖ G, P) ⟶ RΓ(B ∖ Y, b^* P)`: the pullback of sections
over the open complements, the third component of `sectionsWithSupportTrianglePullback`. -/
noncomputable def puncturedRestrictionMap
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)) :
    ((sectionsWithSupportTriangle A a).obj P).obj₃ ⟶
      ((sectionsWithSupportTriangle A y).obj
        ((Functor.mapDerivedCategoryPlus (b)^*[A]).obj P)).obj₃ :=
  ((sectionsWithSupportTrianglePullback A b a y h).app P).hom₃

/-- **Reduction to a punctured restriction** (blueprint `lemma-vanishing-local-term-zero-stalk--1`,
item (iii)): if `RΓ(T, P) = 0` and `RΓ(B, b^* P) = 0`, the localization triangles identify the
supported restriction `ρ_{a,b}`, shifted by one, with the restriction
`RΓ(T ∖ G, P) ⟶ RΓ(B ∖ Y, b^* P)`; in particular `ρ_{a,b} = 0` if and only if this restriction
is zero. -/
theorem sectionsWithSupportRestriction_eq_zero_iff
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A))
    (hT : IsZero ((sectionsWithSupportTriangle A a).obj P).obj₂)
    (hB : IsZero ((sectionsWithSupportTriangle A y).obj
      ((Functor.mapDerivedCategoryPlus (b)^*[A]).obj P)).obj₂) :
    sectionsWithSupportRestriction A b a y h P = 0 ↔ puncturedRestrictionMap A b a y h P = 0 :=
  hom₁_eq_zero_iff_hom₃_eq_zero _ (sectionsWithSupportTriangle_obj_distinguished A a P)
    (sectionsWithSupportTriangle_obj_distinguished A y _) hT hB

end AlgebraicGeometry.Etale
