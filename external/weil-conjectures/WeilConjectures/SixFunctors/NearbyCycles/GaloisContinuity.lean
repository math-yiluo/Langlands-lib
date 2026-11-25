/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerContinuity

/-!

# Continuity of nearby cycles along the finite Galois layers, torsion coefficients

Let `N` be a model of `X` with special fibre `X'` and `j : N.generic ⟶ N.total` quasi-compact and
quasi-separated, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois extension, `T₀` a finite discrete ring
and `Λ = C(-, T₀)`. Let `K` be a bounded below complex of `Λ`-module objects on the generic fibre
whose terms are of étale origin (e.g. a representative of `Lε^* C` for `C` bounded below of étale
origin, `ProEtale.exists_complex_of_plusEtaleOrigin`).

Then the cohomology sheaves of `Li^* Rj_* (g_* g^* K)`, `g : N.generic ×_L Ω ⟶ N.generic`, are the
filtered colimits over the finite Galois subextensions `L'` of those of
`Li^* Rj_* (g_{L'*} g_{L'}^* K)`
(`NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`). Up to the canonical
identifications `g_* g^* K ≅ Rg_* Lg^* K` (the terms of `g^* K` are `g_*`-acyclic) and
`Li^* Rj_* Rg_* Lg^* Lε^* ≅ Ψ_{N_Ω}` (`NearbyCyclesModel.galoisLayerExchangeIso`), the colimit is
`Hᵠ Ψ_{N_Ω}` and the terms are the `Hᵠ Ψ_{N_{L'}}`: the nearby cycles of the geometric generic fibre
are the colimit of those of the finite layers (continuity of the inertia action; SGA 7 XIII 1.3).
In particular every local section of `Hᵠ Ψ_{N_Ω}` over a quasi-compact quasi-separated object comes
from a finite layer `L'`, on whose image the subgroup `Gal(Ω/L')` acts trivially
(`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

/-- `Hᵠ ∘ Li^* ≅ i^* ∘ Hᵠ`: the derived pullback is the levelwise exact pullback. -/
noncomputable def homologyLeftDerivedUpperStarIso {Y Z : Scheme.{u}} (i : Y ⟶ Z)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] (q : ℤ) :
    L((i)^*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ (i)^*⟦Λ⟧ :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ i) _ ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso _ q).symm

/-- **Continuity of nearby cycles along the finite Galois layers** (torsion coefficients). For a
bounded below complex `K` on the generic fibre whose terms are of étale origin, the cohomology
sheaves of `Li^* Rj_* (g_* g^* K)` are the filtered colimits of those of the finite layers
`Li^* Rj_* (g_{L'*} g_{L'}^* K)`, along the maps induced by the projections. -/
theorem nonempty_isColimit_homology_nearbyCycles_galoisTower [QuasiCompact N.j]
    [QuasiSeparated N.j]
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) N.generic)) ℤ)
    (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, (comparisonUpperStar AddCommGrpCat.{u + 1} N.generic).essImage (K.X n).X)
    (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      L((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        ((galoisTower Ω h).complexCocone (Profinite.continuousMapRingObj T₀) K))) := by
  obtain ⟨hc⟩ := (galoisTower Ω h).isColimit_homology_rightDerivedLowerStar_complexCocone T₀ K
    (fun n ↦ (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h (K.X n).X (hK n)).some) a
    N.j q
  have hc' := isColimitOfPreserves ((N.i)^*⟦Profinite.continuousMapRingObj T₀⟧) hc
  exact ⟨IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft
    (DerivedCategory.Q ⋙ R((N.j)_*⟦Profinite.continuousMapRingObj T₀⟧))
    (homologyLeftDerivedUpperStarIso N.i (Profinite.continuousMapRingObj T₀) q).symm) hc'⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
