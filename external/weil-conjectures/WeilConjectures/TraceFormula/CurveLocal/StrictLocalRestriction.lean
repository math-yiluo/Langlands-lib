/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionStrictlyLocal

/-!

# Restriction of derived global sections to a closed subscheme of a strictly local scheme

Let `T ≅ Spec R` with `R` strictly henselian local, and `f : Z ⟶ T` a closed immersion through
which a geometric point `t` of `T` over the closed point factors. Then for every complex `K` of
étale sheaves of `Λ`-modules on `T`, the restriction map `RΓ(T, K) ⟶ RΓ(Z, f^* K)`
(`AlgebraicGeometry.Etale.globalSectionsRestriction`) is an isomorphism.

## Proof

The restriction map is `RΓ(T, -)` of the unit `η : K ⟶ Rf_* f^* K` followed by the Leray
isomorphism. As `Rf_*` is fully faithful, `f^* η` is an isomorphism, so the cone `C` of `η`
satisfies `f^* C = 0`, hence `t^* C = 0`. The global sections functor of `T` being exact and
computing the stalk at `t`, `RΓ(T, C) = 0`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerivedGlobalSections_of_isZero_mapDerivedCategory`:
  `RΓ(T, P) = 0` if `t^* P = 0`, for an unbounded complex `P`.
- `AlgebraicGeometry.Etale.isIso_globalSectionsRestriction_of_isStrictlyHenselianLocalRing`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {R : Type u} [CommRing R]
  [IsStrictlyHenselianLocalRing R] {T : Scheme.{u}}

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, let `t` be a geometric point over
the closed point and `P` a complex of étale sheaves of `Λ`-modules on `T` with `t^* P = 0`. Then
`RΓ(T, P) = 0`: the global sections functor is exact, so `H^q RΓ(T, P) = Γ(T, H^q P)`, the stalk
of `H^q P` at `t`, that is `H^q(t^* P) = 0`. -/
theorem isZero_rightDerivedGlobalSections_of_isZero_mapDerivedCategory
    (e : T ≅ Spec (.of R)) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (P : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hP : IsZero (((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj P)) :
    IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj P) := by
  have := preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (Λ := Λ) e
  refine IsZero.of_iso ?_
    ((Sheaf.Γ T.smallEtaleTopology _).rightDerivedFunctorIsoMapDerivedCategory.app _)
  rw [DerivedCategory.isZero_iff]
  intro q
  refine IsZero.of_iso ?_
    (((Sheaf.Γ T.smallEtaleTopology _).mapDerivedCategoryHomologyFunctorIso q).app _).symm
  refine IsZero.of_iso ?_ ((Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).app _)
  refine isZero_obj_of_isZero_sheafFiber e t ht _ (IsZero.of_iso ?_
    ((upperStarCompSectionsIsoSheafFiber Λ t).app _).symm)
  refine Functor.map_isZero ((sheafSections _ (ModuleCat.{u + 1} Λ)).obj _) (IsZero.of_iso ?_
    ((((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app P))
  exact Functor.map_isZero (DerivedCategory.homologyFunctor _ q) hP

/-- **Restriction to a closed subscheme of a strictly local scheme.** Let `T ≅ Spec R` with `R`
strictly henselian local and `f : Z ⟶ T` a closed immersion through which a geometric point
`s ≫ f` of `T` over the closed point factors. Then the restriction map
`RΓ(T, K) ⟶ RΓ(Z, f^* K)` is an isomorphism for every complex `K` of étale sheaves of
`Λ`-modules on `T`. -/
theorem isIso_globalSectionsRestriction_of_isStrictlyHenselianLocalRing
    (e : T ≅ Spec (.of R)) {Z : Scheme.{u}} (f : Z ⟶ T) [IsClosedImmersion f] {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (hs : (s ≫ f ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (globalSectionsRestriction f K) := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have hη : IsIso (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map (adj.unit.app K)) :=
    isIso_of_comp_hom_eq_id (adj.counit.app _) (adj.left_triangle_components K)
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).IsTriangulated :=
    inferInstanceAs ((Sheaf.Γ T.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated)
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app K)
  have hC := (Triangle.isZero₃_iff_isIso₁ _
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map_distinguished _ hT)).2 (by
      dsimp
      exact hη)
  have hsC : IsZero (((s ≫ f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj C) :=
    IsZero.of_iso ((((s)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory).map_isZero hC)
      ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) s f) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
          (upperStar (ModuleCat.{u + 1} Λ) s)).symm).app C)
  have : IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map (adj.unit.app K)) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map_distinguished _ hT)).1
      (isZero_rightDerivedGlobalSections_of_isZero_mapDerivedCategory e (s ≫ f)
        (by rwa [Category.assoc]) C hsC)
  unfold globalSectionsRestriction
  infer_instance

end AlgebraicGeometry.Etale
