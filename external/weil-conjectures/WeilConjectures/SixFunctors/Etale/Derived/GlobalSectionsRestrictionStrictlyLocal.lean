/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion

/-!
# Restriction of derived global sections to the closed point of a strictly local scheme

Let `R` be a strictly henselian local ring with residue field `κ` and closed geometric point
`s : Spec κ ⟶ Spec R`. For every complex `K` of étale sheaves of `Λ`-modules on `Spec R`, the
restriction map `RΓ(Spec R, K) ⟶ RΓ(Spec κ, s^* K)` is an isomorphism.

## Proof

The restriction map is `RΓ(Spec R, -)` applied to the unit `η : K ⟶ Rs_* s^* K`, followed by
the Leray isomorphism. Complete `η` to a distinguished triangle `K ⟶ Rs_* s^* K ⟶ C ⟶ K[1]`.

* As `s` is a closed immersion, `Rs_*` is fully faithful, so the counit of `s^* ⊣ Rs_*` is an
  isomorphism and, by a triangle identity, so is `s^* η`. Hence `s^* C = 0`.
* The global sections functor on `Spec R` is exact, so
  `Hⁿ(RΓ(Spec R, C)) ≅ Γ(Spec R, Hⁿ(C))`,
  and `Γ(Spec R, Hⁿ(C)) ≅ Γ(Spec κ, s^* Hⁿ(C)) ≅ Γ(Spec κ, Hⁿ(s^* C)) = 0` by the
  degree-zero comparison over a henselian ring. Hence `RΓ(Spec R, C) = 0` and `RΓ(Spec R, η)`
  is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.isIso_globalSectionsRestriction_closedGeometricPoint`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated ZeroObject

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (R : Type u) [CommRing R]
  [IsStrictlyHenselianLocalRing R]

/-- Over a strictly henselian local ring `R`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec R` preserves epimorphisms: an epimorphism of sheaves is surjective on
sections over the terminal object, every covering sieve of which contains the identity. -/
instance preservesEpimorphisms_Γ_of_isStrictlyHenselianLocalRing :
    (Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    let e := Sheaf.ΓNatIsoSheafSections (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (isTerminalEtaleTerminal R)
    have h : (Sheaf.Γ _ _).map φ =
        e.hom.app F ≫ ((sheafSections _ _).obj _).map φ ≫ e.inv.app G := by
      rw [← reassoc_of% (e.hom.naturality φ)]
      simp
    have : Epi (((sheafSections (Spec (.of R)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj (op (etaleTerminal R))).map φ) :=
      (ModuleCat.epi_iff_surjective _).2
        (surjective_app_of_epi_of_isStrictlyHenselianLocalRing R φ)
    rw [h]
    infer_instance

/-- Over a strictly henselian local ring `R`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec R` is exact. -/
instance preservesFiniteColimits_Γ_of_isStrictlyHenselianLocalRing :
    PreservesFiniteColimits
      (Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  have h := (Functor.preservesFiniteLimits_tfae
    (Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 4 1
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 1 4
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

/-- The closed geometric point `Spec κ ⟶ Spec R` of a local ring is a closed immersion. -/
instance isClosedImmersion_closedGeometricPoint : IsClosedImmersion (closedGeometricPoint R) :=
  IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective

/-- Over a strictly henselian local ring `R`, restriction of global sections
`Γ(Spec R, F) ⟶ Γ(Spec κ, F|)` to the closed geometric point is an isomorphism
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing` for the henselian
pair `(R, 𝔪)`). -/
instance isIso_globalSectionsUpperStarMap_closedGeometricPoint
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (closedGeometricPoint R) F) :=
  isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal R) (𝟙 _)
    (closedGeometricPoint R) (𝟙 _) IsPullback.of_id_snd F

/-- Over a strictly henselian local ring `R`, a complex `C` of étale sheaves on `Spec R` whose
pullback to the closed geometric point vanishes has vanishing derived global sections:
`Hⁿ(RΓ(Spec R, C)) ≅ Γ(Spec R, Hⁿ(C)) ≅ Γ(Spec κ, Hⁿ(s^* C)) = 0`. -/
lemma isZero_rightDerivedGlobalSections_of_isZero_upperStar_closedGeometricPoint
    (C : DerivedCategory (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : IsZero (((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj C)) :
    IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).obj C) := by
  have : IsIso (0 : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).obj C ⟶
      0) := (DerivedCategory.isIso_iff _ _).2 fun n ↦ by
    have hn : IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).obj C)) := by
      refine IsZero.of_iso ?_
        ((Functor.rightDerivedFunctorHomologyFunctorIso
          (Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).app C).symm
      refine IsZero.of_iso ?_ (asIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
        (closedGeometricPoint R) ((DerivedCategory.homologyFunctor _ n).obj C)))
      refine Functor.map_isZero _ (IsZero.of_iso ?_
        ((Functor.mapDerivedCategoryHomologyFunctorIso
          ((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]) n).app C))
      exact (DerivedCategory.homologyFunctor _ n).map_isZero hC
    exact isIso_of_source_target_iso_zero _ hn.isoZero
      ((Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact IsZero.of_iso (isZero_zero _) (asIso (0 :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).obj C ⟶ 0))

/-- **Derived global sections of a strictly local scheme are computed at the closed point.**
Over a strictly henselian local ring `R` with closed geometric point `s : Spec κ ⟶ Spec R`, the
restriction map `RΓ(Spec R, K) ⟶ RΓ(Spec κ, s^* K)` is an isomorphism for every complex `K` of
étale sheaves of `Λ`-modules on `Spec R`. -/
theorem isIso_globalSectionsRestriction_closedGeometricPoint
    (K : DerivedCategory (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (globalSectionsRestriction (closedGeometricPoint R) K) := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (closedGeometricPoint R)
  have hη : IsIso (((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map
      (adj.unit.app K)) :=
    isIso_of_comp_hom_eq_id (adj.counit.app _) (adj.left_triangle_components K)
  have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).IsTriangulated :=
    inferInstanceAs ((Sheaf.Γ (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated)
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app K)
  have hC := (Triangle.isZero₃_iff_isIso₁ _
    (((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map_distinguished _
      hT)).2 (by dsimp; exact hη)
  have : IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).map
      (adj.unit.app K)) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of R))).map_distinguished _
        hT)).1
      (isZero_rightDerivedGlobalSections_of_isZero_upperStar_closedGeometricPoint R C hC)
  unfold globalSectionsRestriction
  infer_instance

end AlgebraicGeometry.Etale
