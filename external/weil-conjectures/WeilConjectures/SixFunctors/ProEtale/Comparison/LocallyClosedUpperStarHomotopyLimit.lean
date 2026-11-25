/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStarHomotopyLimit
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb

/-!
# Pullback to a locally closed stratum commutes with derived limits of towers

The pullback `g^*` of abelian pro-étale sheaves is exact; as soon as it also preserves limits,
it sends homotopy limit cones in the derived category (`R lim` of towers) to homotopy limit cones
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_of_preserves`).
This applies to:

- closed immersions with quasi-compact open complement in a quasi-compact quasi-separated
  scheme (`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab_of_isCompl`);
- weakly étale monomorphisms, such as open immersions;
- hence to a locally closed immersion `i ≫ o : S ⟶ U ⟶ Y`, a closed immersion `i` followed by an
  open immersion `o` with `U` quasi-compact and quasi-separated
  (`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_comp`): the
  pullback to a stratum commutes with `R lim`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- An exact pullback of abelian pro-étale sheaves preserving limits commutes with derived limits
of towers. -/
lemma isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_of_preserves
    [PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[Ab.{u + 1}])]
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})} {c : Cone F}
    (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((ProEtale.upperStar Ab.{u + 1} g).mapDerivedCategory.mapCone c) :=
  have : PreservesLimitsOfSize.{0, 0} ((g)^*[Ab.{u + 1}]) := preservesLimitsOfSize_shrink _
  (ProEtale.upperStar Ab.{u + 1} g).isHomotopyLimit_mapDerivedCategory_mapCone hc

/-- The pullback of abelian pro-étale sheaves along a weakly étale monomorphism (e.g. an open
immersion) preserves limits. -/
lemma preservesLimitsOfSize_upperStar_ab_of_mono (g : X ⟶ Y) [WeaklyEtale g] [Mono g] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[Ab.{u + 1}]) :=
  have := preservesLimitsOfSize_upperStar_of_mono (R := ULift.{u + 1} ℤ) g
  preservesLimitsOfSize_upperStar_ab_of_moduleCat g

/-- **Pullback to a locally closed stratum commutes with derived limits of towers**: for a
closed immersion `i : S ⟶ U` with quasi-compact open complement, `U` quasi-compact and
quasi-separated, and an open immersion `o : U ⟶ Y`, the pullback `(i ≫ o)^*` of complexes of
abelian pro-étale sheaves sends homotopy limit cones to homotopy limit cones. -/
lemma isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_comp {S U V : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] (i : S ⟶ U) [IsClosedImmersion i] (j : V ⟶ U)
    [IsOpenImmersion j] [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (o : U ⟶ Y) [IsOpenImmersion o]
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (ProEt.topology Y) Ab.{u + 1})} {c : Cone F}
    (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((ProEtale.upperStar Ab.{u + 1} (i ≫ o)).mapDerivedCategory.mapCone c) :=
  have := preservesLimitsOfSize_upperStar_ab_of_isCompl i j hij
  have := preservesLimitsOfSize_upperStar_ab_of_mono o
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((i ≫ o)^*[Ab.{u + 1}]) :=
    preservesLimits_of_natIso (upperStarComp Ab.{u + 1} i o).symm
  isHomotopyLimit_upperStar_mapDerivedCategory_mapCone_of_preserves (i ≫ o) hc

end AlgebraicGeometry.ProEtale
