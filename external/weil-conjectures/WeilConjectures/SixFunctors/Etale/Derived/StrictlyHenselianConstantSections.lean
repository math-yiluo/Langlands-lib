/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianSections
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionStrictlyLocal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Sections of locally constant sheaves on strictly local schemes

Let `R` be a strictly henselian local ring and `t : Spec Ω ⟶ Spec R` a geometric point.

- The global sections functor on étale sheaves of `Λ`-modules on `Spec R` is exact
  (`AlgebraicGeometry.Etale.preservesFiniteColimits_Γ_of_isStrictlyHenselianLocalRing`).
- A locally constant sheaf on `Spec R` is constant: a trivializing étale cover has a section
  (`AlgebraicGeometry.Scheme.isConstant_of_isLocallyConstantSheaf`).
- For a constant (hence for a locally constant) sheaf `F` of `Λ`-modules on `Spec R`, the
  restriction `Γ(Spec R, F) ⟶ Γ(Spec Ω, t^* F)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_isLocallyConstantSheaf`).
- Every sheaf on the spectrum of a separably closed field is constant, so the restriction of
  sections along any geometric point of it is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_isSepClosed`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

namespace Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- **A locally constant sheaf on a strictly local scheme is constant**: some member of a
trivializing étale cover contains a point over the closed point, hence has a section. -/
theorem isConstant_of_isLocallyConstantSheaf (F : Sheaf (Spec (.of R)).smallEtaleTopology A)
    [IsLocallyConstantSheaf F] : F.IsConstant (Spec (.of R)).smallEtaleTopology := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint R)
  have : AlgebraicGeometry.Etale (𝒰.f j) := 𝒰.map_prop j
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing (𝒰.f j) y hy
  have h₁ : ((Etale.upperStar A (𝒰.f j)).obj F).IsConstant (𝒰.X j).smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have h₂ : ((Etale.upperStar A σ).obj ((Etale.upperStar A (𝒰.f j)).obj F)).IsConstant
      (Spec (.of R)).smallEtaleTopology :=
    have := h₁
    Sheaf.IsConstant.upperStar A _ _
  exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _ (((Etale.upperStarComp A σ (𝒰.f j)).app F).symm ≪≫
    eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F) hσ) ≪≫
    (Etale.upperStarId A _).app F) h₂

end Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (R : Type u) [CommRing R]
  [IsStrictlyHenselianLocalRing R]

variable {R}

/-- Over a strictly henselian local ring `R`, the restriction of global sections of a constant
sheaf of `Λ`-modules on `Spec R` to a geometric point `t : Spec Ω ⟶ Spec R` is an
isomorphism. -/
theorem isIso_globalSectionsUpperStarMap_constantSheaf {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R)) (M : ModuleCat.{u + 1} Λ) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have := Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit R t _
    (Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing Λ R t M) 0
  exact Etale.isIso_globalSectionsUpperStarMap_of_iso
    (F := (DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) t
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app _)

/-- Over a strictly henselian local ring `R`, the restriction of global sections of a constant
sheaf of `Λ`-modules on `Spec R` to a geometric point is an isomorphism. -/
theorem isIso_globalSectionsUpperStarMap_of_isConstant {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [F.IsConstant (Spec (.of R)).smallEtaleTopology] :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t F) := by
  obtain ⟨M, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  have := isIso_globalSectionsUpperStarMap_constantSheaf t M
  exact Etale.isIso_globalSectionsUpperStarMap_of_iso t e

/-- Over a strictly henselian local ring `R`, the restriction of global sections of a locally
constant sheaf of `Λ`-modules on `Spec R` to a geometric point is an isomorphism. -/
theorem isIso_globalSectionsUpperStarMap_of_isLocallyConstantSheaf {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    (F : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t F) := by
  have := isConstant_of_isLocallyConstantSheaf R F
  exact isIso_globalSectionsUpperStarMap_of_isConstant t F

/-- Over a separably closed field `k`, the restriction of global sections of any sheaf of
`Λ`-modules on `Spec k` to a geometric point is an isomorphism: every such sheaf is
constant. -/
theorem isIso_globalSectionsUpperStarMap_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t F) := by
  have := IsStrictlyHenselianLocalRing.of_isSepClosed k
  have := isIso_globalSectionsUpperStarMap_constantSheaf t
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).objPreimage F)
  exact Etale.isIso_globalSectionsUpperStarMap_of_iso t
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).objObjPreimageIso F)

end Etale

end AlgebraicGeometry
