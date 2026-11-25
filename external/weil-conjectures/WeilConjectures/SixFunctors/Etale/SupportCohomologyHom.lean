/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleCoyoneda
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Cohomology with support as morphisms

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. The sections of an étale
sheaf `M` on `X` with support in `Z` are the global sections of the subsheaf
`𝒢_Z M = s_* s^! M` of sections supported on `Z`:

`Γ_Z(X, M) ≅ Γ(X, 𝒢_Z M) ≅ Γ(Z, i^! M)`

(`AlgebraicGeometry.Etale.closedUpperShriekCompΓIso`). Since `i^!` is right adjoint to the
exact functor `i_*`, it preserves K-injective complexes, and so `RΓ_Z(X, -) ≅ RΓ(Z, -) ∘ Ri^!`.
With the adjunctions `i_* ⊣ Ri^!` and `Λ_Z ⊣ RΓ(Z, -)`, this identifies the cohomology with
support with morphisms in the derived category:

`H^a_Z(X, K) ≅ Hom_{D(X)}(i_* Λ_Z, K[a])`.

## Main definitions

- `AlgebraicGeometry.Etale.sectionsWithSupportCompΓIso`: `Γ(X, 𝒢_Z -) ≅ Γ_Z(X, -)`.
- `AlgebraicGeometry.Etale.closedUpperShriekCompΓIso`: `Γ(Z, i^! -) ≅ Γ_Z(X, -)`.
- `AlgebraicGeometry.Etale.rightDerivedClosedUpperShriekCompIso`:
  `RΓ(Z, Ri^! -) ≅ RΓ_Z(X, -)`.
- `AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`:
  `Hom(i_* Λ_Z, K[a]) ≃ H^a_Z(X, K)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Sections

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a sheaf `G` on `U`, the restriction `Γ(X, j_* G) ⟶ (j_* G)(U)` is an isomorphism. -/
instance isIso_ΓRes_lowerStar_obj (G : Sheaf U.smallEtaleTopology A) :
    IsIso (((j)_*[A].obj G).ΓRes (op (Scheme.Etale.mk j))) := by
  rw [ΓRes_eq]
  infer_instance

/-- The sections over `U` of the inclusion `𝒢_Z M ⟶ M` of the supported sections vanish, so the
global sections of the inclusion restrict to zero on `U`. -/
@[reassoc]
lemma ΓMap_sectionsWithSupportι_app_comp_ΓRes (M : Sheaf X.smallEtaleTopology A) :
    (Sheaf.Γ X.smallEtaleTopology A).map ((sectionsWithSupportι A j).app M) ≫
      M.ΓRes (op (Scheme.Etale.mk j)) = 0 := by
  erw [Sheaf.ΓRes_naturality]
  have : IsZero (((sectionsWithSupport A j).obj M).obj.obj (op (Scheme.Etale.mk j))) :=
    isZero_obj_of_isZero_upperStar (isZero_upperStar_sectionsWithSupport A j M) _
      subset_rfl
  rw [this.eq_of_tgt (Sheaf.ΓRes _ _) 0, zero_comp]

/-- The global sections of the unit `M ⟶ j_* j^* M` are the restriction `Γ(X, M) ⟶ M(U)`
followed by the identification `M(U) ≅ (j_* j^* M)(U) ≅ Γ(X, j_* j^* M)`. -/
lemma ΓMap_unit_app_eq (M : Sheaf X.smallEtaleTopology A) :
    (Sheaf.Γ X.smallEtaleTopology A).map ((upperStarLowerStarAdjunction A j).unit.app M) =
      M.ΓRes (op (Scheme.Etale.mk j)) ≫
        ((openImmersionRestrictionLowerStarAdjunction A j).unit.app M).hom.app
          (op (Scheme.Etale.mk j)) ≫
        inv (((j)_*[A].obj ((openImmersionRestriction A j).obj M)).ΓRes
          (op (Scheme.Etale.mk j))) ≫
        (Sheaf.Γ X.smallEtaleTopology A).map ((j)_*[A].map
          (((upperStarLowerStarAdjunction A j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction A j)).inv.app M)) := by
  have h₁ := Sheaf.ΓRes_naturality ((openImmersionRestrictionLowerStarAdjunction A j).unit.app M)
    (op (Scheme.Etale.mk j))
  rw [← reassoc_of% h₁, IsIso.hom_inv_id_assoc, ← Functor.map_comp]
  congr 1
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A j)
    (openImmersionRestrictionLowerStarAdjunction A j), assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp

/-- The global sections of the inclusion `𝒢_Z M ⟶ M` of the sections supported on the closed
complement `Z` of `j` form a kernel of the restriction `Γ(X, M) ⟶ M(U)`: `Γ` preserves the kernel
`𝒢_Z M` of `M ⟶ j_* j^* M`, and `Γ(X, M) ⟶ Γ(X, j_* j^* M)` is the restriction `Γ(X, M) ⟶ M(U)`
followed by an isomorphism (`AlgebraicGeometry.Etale.ΓMap_unit_app_eq`). -/
noncomputable def isLimitΓMapSectionsWithSupportι (M : Sheaf X.smallEtaleTopology A) :
    IsLimit (KernelFork.ofι _ (ΓMap_sectionsWithSupportι_app_comp_ΓRes A j M)) :=
  isKernelOfComp _ _ (KernelFork.mapIsLimit _
    (kernelIsKernel ((upperStarLowerStarAdjunction A j).unit.app M))
      (Sheaf.Γ X.smallEtaleTopology A)) (ΓMap_sectionsWithSupportι_app_comp_ΓRes A j M)
    (ΓMap_unit_app_eq A j M).symm

end Sections

section SupportCohomology

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The sections with support `Γ_Z(X, M) ⟶ Γ(X, M)` form a kernel of the restriction
`Γ(X, M) ⟶ M(U)`. -/
noncomputable def isLimitSectionsWithSupport (M : Sheaf X.smallEtaleTopology A) :
    IsLimit (KernelFork.ofι _ (Sheaf.ΓSupportι_app_comp_ΓRes X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι)) M)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι)))) ((evaluation _ A).obj M)

/-- The sections with support in `Z` are the global sections of the subsheaf of sections
supported on `Z`: `Γ(X, 𝒢_Z M) ≅ Γ_Z(X, M)`, compatibly with the inclusions into `Γ(X, M)`. -/
noncomputable def sectionsWithSupportCompΓIso :
    sectionsWithSupport A i.openComplement.ι ⋙ Sheaf.Γ X.smallEtaleTopology A ≅
      globalSectionsWithSupport A i :=
  NatIso.ofComponents
    (fun M ↦ (isLimitΓMapSectionsWithSupportι A i.openComplement.ι M).conePointUniqueUpToIso
      (isLimitSectionsWithSupport A i M))
    (fun {M N} f ↦ by
      rw [← cancel_mono ((Sheaf.ΓSupportι X.smallEtaleTopology A _).app N)]
      have h₁ := (isLimitΓMapSectionsWithSupportι A i.openComplement.ι
        M).conePointUniqueUpToIso_hom_comp (isLimitSectionsWithSupport A i M) .zero
      have h₂ := (isLimitΓMapSectionsWithSupportι A i.openComplement.ι
        N).conePointUniqueUpToIso_hom_comp (isLimitSectionsWithSupport A i N) .zero
      simp only [KernelFork.ofι, Fork.ofι_π_app] at h₁ h₂
      simp only [Functor.comp_map, assoc, h₂]
      erw [(Sheaf.ΓSupportι X.smallEtaleTopology A _).naturality f, reassoc_of% h₁]
      erw [← Functor.map_comp, ← Functor.map_comp,
        ← (sectionsWithSupportι A i.openComplement.ι).naturality f])

@[reassoc (attr := simp)]
lemma sectionsWithSupportCompΓIso_hom_app_comp (M : Sheaf X.smallEtaleTopology A) :
    (sectionsWithSupportCompΓIso A i).hom.app M ≫
        (Sheaf.ΓSupportι X.smallEtaleTopology A _).app M =
      (Sheaf.Γ X.smallEtaleTopology A).map ((sectionsWithSupportι A _).app M) := by
  have h := (isLimitΓMapSectionsWithSupportι A i.openComplement.ι M).conePointUniqueUpToIso_hom_comp
    (isLimitSectionsWithSupport A i M) WalkingParallelPair.zero
  simp only [KernelFork.ofι, Fork.ofι_π_app] at h
  exact h

/-- `Γ_Z(X, M) ≅ Γ(Z, i^! M)`: the sections with support in `Z` are the global sections of the
exceptional inverse image `i^! M` (`AlgebraicGeometry.Etale.closedUpperShriek`), through
`Γ(Z, i^! M) ≅ Γ(X, i_* i^! M) ≅ Γ(X, 𝒢_Z M)`. -/
noncomputable def closedUpperShriekCompΓIso :
    closedUpperShriek A i i.openComplement.ι ⋙ Sheaf.Γ Z.smallEtaleTopology A ≅
      globalSectionsWithSupport A i :=
  Functor.isoWhiskerLeft _ (lowerStarCompGlobalSectionsIso A i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (closedUpperShriekCompLowerStarIso A i _
      i.range_eq_compl_range_openComplement_ι) _ ≪≫
    sectionsWithSupportCompΓIso A i

instance : PreservesFiniteColimits ((i)_*[A]) :=
  have := (lowerStarClosedUpperShriekAdjunction A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).leftAdjoint_preservesColimits
  inferInstance

instance : ((i)_*[A]).PreservesHomology where

/-- The exceptional inverse image `i^!` of a closed immersion preserves K-injective complexes,
being right adjoint to the exact functor `i_*`. -/
instance : (closedUpperShriek A i i.openComplement.ι).PreservesKInjectiveComplexes :=
  (lowerStarClosedUpperShriekAdjunction A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).preservesKInjectiveComplexes

/-- `RΓ(Z, Ri^! K) ≅ RΓ_Z(X, K)`: the derived sections with support in `Z` are the derived
global sections of the derived exceptional inverse image `Ri^!` of the sheaf functor `i^!`. -/
noncomputable def rightDerivedClosedUpperShriekCompIso :
    (closedUpperShriek A i i.openComplement.ι).rightDerivedFunctor ⋙
        (Sheaf.Γ Z.smallEtaleTopology A).rightDerivedFunctor ≅
      rightDerivedSectionsWithSupport A i :=
  Functor.rightDerivedFunctorCompIso' _ _ (closedUpperShriekCompΓIso A i)

end SupportCohomology

section Hom

variable (Λ : Type (u + 1)) [CommRing Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

instance : Projective (ModuleCat.of Λ Λ) :=
  ModuleCat.projective_of_free (Module.Basis.singleton Unit Λ)

/-- The derived sections with support commute with shifts, as every right derived functor does. -/
noncomputable instance (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] :
    (rightDerivedSectionsWithSupport A i).CommShift ℤ :=
  inferInstanceAs ((globalSectionsWithSupport A i).rightDerivedFunctor.CommShift ℤ)

/-- The functor `K ↦ Hom_{D(X)}(i_* Λ_Z, K[a])` to abelian groups is `K ↦ H^a_Z(X, K)`:

`Hom(i_* Λ_Z, K[a]) ≅ Hom(Λ_Z, Ri^!(K[a])) ≅ Hom(Λ, RΓ(Z, Ri^!(K[a]))) ≅ Hom(Λ, RΓ_Z(X, K)[a])
  ≅ H^a(RΓ_Z(X, K))`,

by the adjunctions `i_* ⊣ Ri^!` and `Λ_Z ⊣ RΓ(Z, -)` (both left adjoints being exact), the
identification `RΓ(Z, Ri^! -) ≅ RΓ_Z(X, -)`
(`AlgebraicGeometry.Etale.rightDerivedClosedUpperShriekCompIso`), and `Hom(Λ[0], M[a]) ≅ H^a(M)`
for complexes of `Λ`-modules. -/
noncomputable def shiftFunctorCompPreadditiveCoyonedaLowerStarConstantIso (a : ℤ) :
    shiftFunctor (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) a ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj
          ((i)_*[ModuleCat.{u + 1} Λ].obj ((constantSheaf Z.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))))) ≅
      derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat :=
  let C := ModuleCat.{u + 1} Λ
  let adj₁ := (lowerStarClosedUpperShriekAdjunction C i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).mapDerivedCategoryRightDerivedAdjunction
  let adj₂ := (constantSheafΓAdj Z.smallEtaleTopology C).mapDerivedCategoryRightDerivedAdjunction
  let e₁ := ((i)_*[C].mapDerivedCategorySingleFunctor 0).app
    ((constantSheaf Z.smallEtaleTopology C).obj (ModuleCat.of Λ Λ))
  let e₂ := ((constantSheaf Z.smallEtaleTopology C).mapDerivedCategorySingleFunctor 0).app
    (ModuleCat.of Λ Λ)
  Functor.isoWhiskerLeft _
      (preadditiveCoyoneda.mapIso e₁.op ≪≫ adj₁.preadditiveCoyonedaObjIso _ ≪≫
        Functor.isoWhiskerLeft _ (preadditiveCoyoneda.mapIso e₂.op ≪≫
          adj₂.preadditiveCoyonedaObjIso _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (rightDerivedClosedUpperShriekCompIso C i) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((rightDerivedSectionsWithSupport C i).commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
        (ModuleCat.of Λ Λ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.preadditiveCoyonedaObjSelfIso Λ)

/-- Blueprint `lemma-sections-support-closed-subscheme--1`: Supported cohomology as morphisms

For a closed immersion `i : Z ⟶ X` and a complex `K` of étale sheaves of `Λ`-modules on `X`, the
cohomology with support has a natural identification

`H^a_Z(X, K) ≅ Hom_{D(X, Λ)}(i_* Λ_Z, K[a])`

(naturality: `AlgebraicGeometry.Etale.shiftFunctorCompPreadditiveCoyonedaLowerStarConstantIso`).
Here `H^a_Z(X, K)` is `AlgebraicGeometry.Etale.derivedSupportCohomology` and `i_* Λ_Z` is the
pushforward of the constant sheaf, placed in degree `0`. -/
noncomputable def derivedSupportCohomologyAddEquiv
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K ≃+
      ((DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) ⟶
          K⟦a⟧) :=
  ((shiftFunctorCompPreadditiveCoyonedaLowerStarConstantIso Λ i a).app
    K).symm.addCommGroupIsoToAddEquiv

end Hom

end Etale

end AlgebraicGeometry
