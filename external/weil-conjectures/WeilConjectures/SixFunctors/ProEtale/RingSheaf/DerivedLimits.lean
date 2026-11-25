/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtensionZeroLimits
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.Limits

/-!
# Extension by zero of complexes of module sheaves preserves products and derived limits

Let `X` be quasi-compact and quasi-separated, `j : U ⟶ X` a quasi-compact open immersion with
closed complement `i : Z ⟶ X`, and `B` a sheaf of `R`-algebras on `X_proét`. On derived
categories of module sheaves, the extension by zero
`j_! : D(U_proét, j^* B) ⥤ D(X_proét, B)` preserves products
(`ProEtale.RingSheaf.preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek`) and
derived limits `R lim` of towers
(`ProEtale.RingSheaf.isHomotopyLimit_mapCone_openImmersionLowerShriek`): part (2) of blueprint
`proposition-extension-zero-restriction-closed-subscheme`, for a general sheaf of rings.

Products of `B`-module sheaves are exact, since they are so on underlying sheaves of `R`-modules
(Bhatt–Scholze, Proposition 3.1.10) and the forgetful functor preserves and reflects finite
colimits and preserves products (`ProEtale.RingSheaf.hasExactLimitsOfShape_discrete`). Hence
derived products are computed by degreewise products, and the exact functor `j_!`, which
preserves products of module sheaves, preserves derived products; the derived limit of a tower
is characterised by the Milnor triangle, preserved by triangulated functors preserving countable
products.

The categories of module sheaves are Grothendieck abelian
(`CategoryTheory.Mod.isGrothendieckAbelian`), so they have K-injective resolutions; the derived
categories are those of arbitrary `HasDerivedCategory` instances.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R]

attribute [local instance high] Mod.instHasLimitsOfShape_weilConjectures

/-- **Bhatt–Scholze, Proposition 3.1.10** for module sheaves over a sheaf of rings: products of
`B`-module sheaves on `T_proét` are exact, since they are so on underlying sheaves. -/
instance hasExactLimitsOfShape_discrete {T : Scheme.{u}}
    (B : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R)) [MonObj B] (β : Type (u + 1)) :
    HasExactLimitsOfShape (Discrete β) (Mod (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R)) B) :=
  HasExactLimitsOfShape.domain_of_functor _ (Mod.forget B)

variable {Z U X : Scheme.{u}} (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- The extension by zero on module sheaves is additive, since it is so on underlying sheaves. -/
instance additive_openImmersionLowerShriek : (openImmersionLowerShriek B i j hij).Additive where
  map_add {_ _ f g} := (Mod.forget B).map_injective <| by
    rw [(Mod.forget B).map_add]
    change (j)_!open[ModuleCat.{u + 1} R].map ((Mod.forget _).map (f + g)) =
      (j)_!open[ModuleCat.{u + 1} R].map ((Mod.forget _).map f) +
        (j)_!open[ModuleCat.{u + 1} R].map ((Mod.forget _).map g)
    rw [Functor.map_add, Functor.map_add]

variable [CompactSpace X] [QuasiSeparatedSpace X]
  [HasDerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B)]
  [HasDerivedCategory (Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))
    ((j)^*[ModuleCat.{u + 1} R].obj B))]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), part (2), products, and the product assertion of
blueprint `proposition-extension-zero-restriction-closed-subscheme`: let `X` be quasi-compact and
quasi-separated, `j : U ⟶ X` a quasi-compact open immersion with closed complement `i`, and `B` a
sheaf of `R`-algebras on `X_proét`. The extension by zero `j_! : D(U_proét, j^* B) ⥤ D(X_proét, B)`
on derived categories of module sheaves preserves products. -/
theorem preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek
    (β : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete β) (openImmersionLowerShriek B i j hij).mapDerivedCategory :=
  have : IsGrothendieckAbelian.{u + 1} (Mod (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} R)) B) := Mod.isGrothendieckAbelian.{u + 1} B
  have : IsGrothendieckAbelian.{u + 1} (Mod (Sheaf (ProEt.topology U)
      (ModuleCat.{u + 1} R)) ((j)^*[ModuleCat.{u + 1} R].obj B)) :=
    Mod.isGrothendieckAbelian.{u + 1} _
  have := preservesLimitsOfShape_discrete_openImmersionLowerShriek B i j hij β
  Functor.preservesLimitsOfShape_discrete_mapDerivedCategory _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), part (2), derived limits, and the derived limit
assertion of blueprint `proposition-extension-zero-restriction-closed-subscheme`: let `X` be
quasi-compact and quasi-separated, `j : U ⟶ X` a quasi-compact open immersion with closed complement
`i`, and `B` a sheaf of `R`-algebras on `X_proét`. The extension by zero
`j_! : D(U_proét, j^* B) ⥤ D(X_proét, B)` preserves derived inverse limits `R lim` of towers: it
carries a homotopy limit cone (one whose legs fit into a distinguished Milnor triangle
`R lim Kₙ ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ (R lim Kₙ)[1]`) to a homotopy limit cone, since it is
triangulated and preserves countable products. -/
theorem isHomotopyLimit_mapCone_openImmersionLowerShriek
    {K : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))
      ((j)^*[ModuleCat.{u + 1} R].obj B))} {c : Cone K} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((openImmersionLowerShriek B i j hij).mapDerivedCategory.mapCone c) :=
  have := preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek B i j hij
    (ULift.{u + 1} ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (openImmersionLowerShriek B i j hij).mapDerivedCategory :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  hc.map _

end AlgebraicGeometry.ProEtale.RingSheaf
