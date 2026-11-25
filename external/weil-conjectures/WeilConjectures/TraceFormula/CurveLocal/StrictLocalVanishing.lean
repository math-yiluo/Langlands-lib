/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!

# Derived global sections over a strictly local scheme

Let `T ≅ Spec R` be the spectrum of a strictly henselian local ring and `t : Spec Ω ⟶ T` a
geometric point over the closed point. The global sections functor on `T_ét` is exact and
computes the stalk at `t`. Consequently, for a bounded below complex `P` of étale sheaves of
`Λ`-modules on `T` whose pullback `t^* P` vanishes, the derived global sections `RΓ(T, P)`
vanish (blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (ii)).

## Main results

- `AlgebraicGeometry.Etale.preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing`: the
  global sections functor of `T_ét` is exact.
- `AlgebraicGeometry.Etale.isZero_rightDerivedGlobalSections_of_isStrictlyHenselianLocalRing`:
  `RΓ(T, P) = 0` if `t^* P = 0`.
- `AlgebraicGeometry.Etale.isZero_sectionsWithSupportTriangle_obj₂_of_isStrictlyHenselianLocalRing`:
  the middle term `RΓ(T, P)` of the localization triangle of a closed immersion into `T`
  vanishes if `t^* P = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R] {T : Scheme.{u}}

/-- An étale morphism `f : U ⟶ T` to a scheme `T ≅ Spec R`, `R` strictly henselian local, whose
image contains the closed point has a section. -/
lemma exists_section_of_etale_of_isStrictlyHenselianLocalRing (e : T ≅ Spec (.of R))
    {U : Scheme.{u}} (f : U ⟶ T) [AlgebraicGeometry.Etale f] (y : U)
    (hy : (f ≫ e.hom) y = IsLocalRing.closedPoint R) : ∃ σ : T ⟶ U, σ ≫ f = 𝟙 T := by
  obtain ⟨σ, hσ⟩ := Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing (f ≫ e.hom)
    y hy
  refine ⟨e.hom ≫ σ, ?_⟩
  rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hσ]
  simp

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, every covering sieve of the
terminal object of the small étale site contains the identity. -/
lemma id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing (e : T ≅ Spec (.of R))
    (S : Sieve (Scheme.Etale.mk (𝟙 T)))
    (hS : S ∈ T.smallEtaleTopology (Scheme.Etale.mk (𝟙 T))) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hS
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq (e.inv (IsLocalRing.closedPoint R))
  have : AlgebraicGeometry.Etale (𝒰.f j) := 𝒰.map_prop j
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing e (𝒰.f j) y
    ((congrArg e.hom.base hy).trans (by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl))
  have hmem : S.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  convert S.downward_closed hmem (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (𝟙 T))
    (B := (𝒰.X j).asOverProp _ (p j)) σ
    (by
      rw [← comp_over (𝒰.f j), ← Category.assoc, hσ, Category.id_comp]
      rfl :
      σ ≫ (𝒰.X j ↘ T) = 𝟙 T))
  exact MorphismProperty.Over.Hom.ext hσ.symm

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, an epimorphism of étale sheaves of
`Λ`-modules on `T` is surjective on global sections. -/
lemma surjective_app_of_epi_of_isStrictlyHenselianLocalRing (e : T ≅ Spec (.of R))
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Scheme.Etale.mk (𝟙 T)))) := by
  have := (Sheaf.isLocallySurjective_iff_epi' _ φ).2 inferInstance
  intro s
  obtain ⟨t, ht⟩ := id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing e _
    (Presheaf.imageSieve_mem T.smallEtaleTopology φ.hom (U := op (Scheme.Etale.mk (𝟙 T))) s)
  exact ⟨t, ht.trans (by simp)⟩

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, the global sections functor on
étale sheaves of `Λ`-modules is exact. -/
lemma preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (e : T ≅ Spec (.of R)) :
    PreservesFiniteColimits (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  have : ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 T)))).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ (ModuleCat.epi_iff_surjective _).2
      (surjective_app_of_epi_of_isStrictlyHenselianLocalRing e φ)⟩
  have : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm
  have : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact (Sheaf.Γ _ _).preservesFiniteColimits_of_preservesHomology

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, an étale sheaf of `Λ`-modules
whose stalk at a geometric point `t` over the closed point vanishes has no nonzero global
sections: the germ at `t` is injective, since every pointed étale neighbourhood of `t` has a
section. -/
lemma isZero_obj_of_isZero_sheafFiber (e : T ≅ Spec (.of R)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : IsZero ((pointSmallEtale t).sheafFiber.obj H)) :
    IsZero (H.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hsub := ModuleCat.isZero_iff_subsingleton.1 hH
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  obtain ⟨Y, f, y, _, heq⟩ := ((pointSmallEtale t).toPresheafFiber_eq_iff' (P := H.obj)
    (Scheme.Etale.mk (𝟙 T)) (CategoryTheory.Over.homMk t (Category.comp_id t)) a b).mp
    (hsub.elim _ _)
  obtain ⟨g, hg⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing e Y.hom
    (y.left (IsLocalRing.closedPoint Ω))
    ((congrArg (fun g ↦ (g ≫ e.hom) (IsLocalRing.closedPoint Ω)) (Over.w y)).trans ht)
  let g' : Scheme.Etale.mk (𝟙 T) ⟶ Y := MorphismProperty.Over.homMk g hg
  have hgf : g' ≫ f = 𝟙 _ :=
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).hom_ext _ _
  have h := congrArg (H.obj.map g'.op) heq
  simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h

/-- Over a scheme `T ≅ Spec R`, `R` strictly henselian local, let `t` be a geometric point over
the closed point and `P` a bounded below complex of étale sheaves of `Λ`-modules on `T` with
`t^* P = 0`. Then the global sections of every cohomology sheaf of `P` vanish. -/
lemma isZero_Γ_homology_of_isZero_mapDerivedCategoryPlus_upperStar
    (e : T ≅ Spec (.of R)) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hP : IsZero ((Functor.mapDerivedCategoryPlus (t)^*[ModuleCat.{u + 1} Λ]).obj P)) (q : ℤ) :
    IsZero ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj P)) := by
  refine IsZero.of_iso ?_ ((Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).app _)
  refine isZero_obj_of_isZero_sheafFiber e t ht _ (IsZero.of_iso ?_
    ((upperStarCompSectionsIsoSheafFiber Λ t).app _).symm)
  refine Functor.map_isZero ((sheafSections _ (ModuleCat.{u + 1} Λ)).obj _) (IsZero.of_iso ?_
    (((t)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app P))
  exact Functor.map_isZero (DerivedCategory.Plus.homologyFunctor _ q) hP

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (ii): **derived global sections over
a strictly local scheme.** Let `T ≅ Spec R` with `R` strictly henselian local, `t : Spec Ω ⟶ T`
a geometric point over the closed point and `P` a bounded below complex of étale sheaves of
`Λ`-modules on `T` with `t^* P = 0`. Then `RΓ(T, P) = 0`: the global sections functor is exact,
so `H^q RΓ(T, P) = Γ(T, H^q P)`, which is the stalk of `H^q P` at `t`, that is `H^q(t^* P) = 0`. -/
theorem isZero_rightDerivedGlobalSections_of_isStrictlyHenselianLocalRing
    (e : T ≅ Spec (.of R)) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hP : IsZero ((Functor.mapDerivedCategoryPlus (t)^*[ModuleCat.{u + 1} Λ]).obj P)) :
    IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
      (DerivedCategory.Plus.ι.obj P)) := by
  have := preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (Λ := Λ) e
  refine IsZero.of_iso ?_
    ((Sheaf.Γ T.smallEtaleTopology _).rightDerivedFunctorIsoMapDerivedCategory.app _)
  rw [DerivedCategory.isZero_iff]
  intro q
  exact IsZero.of_iso (isZero_Γ_homology_of_isZero_mapDerivedCategoryPlus_upperStar e t ht P hP q)
    (((Sheaf.Γ T.smallEtaleTopology _).mapDerivedCategoryHomologyFunctorIso q).app _).symm

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (ii): for a closed immersion
`i : Z ⟶ T` into a strictly local scheme `T ≅ Spec R` and a bounded below complex `P` of étale
sheaves of `Λ`-modules on `T` whose pullback to a geometric point `t` over the closed point
vanishes, the middle term `RΓ(T, P)` of the localization triangle
`RΓ_Z(T, P) ⟶ RΓ(T, P) ⟶ RΓ(T ∖ Z, P) ⟶ RΓ_Z(T, P)[1]` vanishes. -/
theorem isZero_sectionsWithSupportTriangle_obj₂_of_isStrictlyHenselianLocalRing {Z : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (e : T ≅ Spec (.of R)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (P : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hP : IsZero ((Functor.mapDerivedCategoryPlus (t)^*[ModuleCat.{u + 1} Λ]).obj P)) :
    IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) i).obj P).obj₂ :=
  isZero_rightDerivedGlobalSections_of_isStrictlyHenselianLocalRing e t ht P hP

end AlgebraicGeometry.Etale
