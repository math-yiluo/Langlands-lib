/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleExactProducts
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ExtensionZeroProducts

/-!
# Extension by zero preserves derived products and derived limits

Let `X` be quasi-compact and quasi-separated and `j : U ⟶ X` a quasi-compact open immersion with
closed complement `i : Z ⟶ X`. The extension by zero `j_! : D(U_proét) ⥤ D(X_proét)` preserves
products
(`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek`)
and derived limits `R lim` of towers
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_openImmersionLowerShriek`); this is part (2)
of blueprint `proposition-extension-zero-restriction-closed-subscheme`.

The pro-étale site has enough weakly contractible objects, so products of pro-étale sheaves of
modules are exact (`AlgebraicGeometry.ProEtale.hasExactLimitsOfShape_discrete`), and products in
the derived category are computed by degreewise products of complexes. As `j_!` is exact and
preserves products of sheaves
(`AlgebraicGeometry.ProEtale.isIso_piComparison_openImmersionLowerShriek`),
it preserves derived products. The derived limit of a tower is characterised by the Milnor
triangle `R lim Kₙ ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶`, which is preserved by any triangulated functor
preserving countable products.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- **Bhatt–Scholze, Proposition 3.1.10.** Products of pro-étale sheaves of modules are exact:
the pro-étale site has enough (affine) weakly contractible objects. -/
instance hasExactLimitsOfShape_discrete {T : Scheme.{u}} {R : Type (u + 1)} [Ring R]
    (β : Type (u + 1)) :
    HasExactLimitsOfShape (Discrete β) (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R)) :=
  GrothendieckTopology.hasExactLimitsOfShape_discrete_of_forall_exists.{u + 1, u}
    (fun W : T.ProEt ↦ IsAffine W.left ∧ (ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ ProEt.exists_isWeaklyContractible_cover V) (fun _ h ↦ h.2) β

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- The extension by zero `j_!` of pro-étale sheaves of modules preserves products. -/
lemma preservesLimitsOfShape_discrete_openImmersionLowerShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (β : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete β) (j)_!open[ModuleCat.{u + 1} R] :=
  have (N : β → Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
      PreservesLimit (Discrete.functor N) (j)_!open[ModuleCat.{u + 1} R] :=
    have := isIso_piComparison_openImmersionLowerShriek i j hij N
    PreservesProduct.of_iso_comparison _ _
  preservesLimitsOfShape_of_discrete _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), part (2), products: let `X` be quasi-compact and
quasi-separated and `j : U ⟶ X` a quasi-compact open immersion with closed complement `i`. The
extension by zero `j_! : D(U_proét) ⥤ D(X_proét)` preserves products. -/
theorem preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (β : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete β) D((j)_!open[ModuleCat.{u + 1} R]) :=
  have := preservesLimitsOfShape_discrete_openImmersionLowerShriek (R := R) i j hij β
  Functor.preservesLimitsOfShape_discrete_mapDerivedCategory _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`lemma-local-cohomology-right-adjoint--1`), part (2), derived limits: let `X` be quasi-compact and
quasi-separated and `j : U ⟶ X` a quasi-compact open immersion with closed complement `i`. The
extension by zero `j_! : D(U_proét) ⥤ D(X_proét)` preserves derived inverse limits `R lim` of
towers: it carries a homotopy limit cone (one whose legs fit into a distinguished Milnor triangle
`R lim Kₙ ⟶ ∏ Kₙ ──1 - t──▶ ∏ Kₙ ⟶ (R lim Kₙ)[1]`) to a homotopy limit cone, since it is
triangulated and preserves countable products. -/
theorem isHomotopyLimit_mapCone_openImmersionLowerShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))} {c : Cone K}
    (hc : IsHomotopyLimit c) :
    IsHomotopyLimit (D((j)_!open[ModuleCat.{u + 1} R]).mapCone c) :=
  have := preservesLimitsOfShape_mapDerivedCategory_openImmersionLowerShriek (R := R) i j hij
    (ULift.{u + 1} ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ) D((j)_!open[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  hc.map _

end ProEtale

end AlgebraicGeometry
