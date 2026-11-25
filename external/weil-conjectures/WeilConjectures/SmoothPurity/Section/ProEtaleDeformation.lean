/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Coordinates
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalCone
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso
public import WeilConjectures.SmoothPurity.Section.ProEtaleSectionInvariant

/-!
# Pro-étale deformation to the normal cone

Let `Λ` be a finite coefficient ring and `g : V ⟶ B` smooth of relative dimension `d` with a
closed section `s`, over a base `B` separated and locally of finite type over a field on which
the characteristic of `Λ` is invertible. The deformation to the normal cone `g̃ : 𝒟_s V ⟶ 𝔸¹_B`
with its section `s̃` gives the pro-étale *family object* `F = Ls̃^* ω_{g̃}` on `𝔸¹_B`, whose fibres
at `t = 1` and `t = 0` are the pro-étale section invariants `𝒞(g, s)` and `𝒞(π_N, 0_N)`
(`prose-09-12` (1)). The family is constant along `𝔸¹_B`,
`κ : F ≅ La^* 𝒞(g, s)` (`lemma-section-normal-bundle--1`), and restricting `κ` to `t = 0` gives the
DNC isomorphism `𝒞(g, s) ≅ 𝒞(π_N, 0_N)` (blueprint `lemma-section-normal-bundle`,
`lemma-section-normal-bundle--1`).

## Implementation notes

The pro-étale section invariants are the comparison pullbacks `ν^*` of the étale ones,
canonically (`AlgebraicGeometry.ProEtale.sectionInvariantComparisonIso`). Every datum of this
file is the image under `ν^*` of the corresponding étale datum of
`WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso`, read through these
identifications; so its properties are those of the étale datum. In particular the DNC
isomorphism restricts along every base change `u : B' ⟶ B` to the image of the restricted étale
DNC isomorphism (`leftDerivedUpperStar_map_proEtaleSectionInvariantIso_hom`), which is the
identity of the standard object in every system of coordinates
(`leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso`).

The Tate twist datum is the genuine one, `Λ(1) = μₙ ⊗ Λ`, which is normalized
(`AlgebraicGeometry.Etale.hasKummerClass_isNormalized`), so no hypothesis on `Λ` beyond
finiteness is needed.

## Main definitions

In the list below, `DeformationToNormalConeData` abbreviates
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`.

- `DeformationToNormalConeData.proEtaleFamilyObject`: the pro-étale family object `F`.
- `DeformationToNormalConeData.proEtaleOneFibreIso`,
  `DeformationToNormalConeData.proEtaleZeroFibreIso`: its fibres at `t = 1` and `t = 0`.
- `DeformationToNormalConeData.proEtaleFamilyObjectIso`: the constancy comparison `κ`.
- `DeformationToNormalConeData.proEtaleSectionInvariantIso`: the DNC isomorphism.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_iso_sectionInvariant_normalCone`: DNC invariance of the
  pro-étale section invariant, for a deformation datum.
- `AlgebraicGeometry.ProEtale.nonempty_iso_sectionInvariant_normalConeProj`: the same for the
  normal cone `N_s = Spec (⨁ I^r / I^{r+1})` of the section.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Etale.neZero_ringChar_of_finite

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)

/-- Blueprint `definition-deformation-normal-bundle`: the pro-étale *family object*
`F = Ls̃^* ω_{g̃}` on `𝔸¹_B` of a deformation datum, the pro-étale section invariant of
`g̃ : 𝒟_s V ⟶ 𝔸¹_B` and its section `s̃`. -/
noncomputable abbrev proEtaleFamilyObject :
    _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology 𝔸(ULift.{u} (Fin 1); B)) (ModuleCat.{u + 1} Λ)) :=
  ProEtale.sectionInvariant Λ D.proj D.sect

variable [HasInvertibleExponent Λ B] [QuasiSeparatedSpace B]

/-- Blueprint `prose-09-12` (1): the fibre of the pro-étale family object at
`t = 1` is the section invariant of `(g, s)`, `θ₁ : Li₁^* F ≅ 𝒞(g, s)`, by base change for the
smooth `g̃` along the unit section. -/
noncomputable def proEtaleOneFibreIso [HasCompactification g] [QuasiCompact g] :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
      (D.proEtaleFamilyObject Λ) ≅ ProEtale.sectionInvariant Λ g s :=
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_oneFibre
  sectionInvariantBaseChangeIso Λ D.isPullback_oneFibre D.sect s D.comp_oneFibre

/-- Blueprint `prose-09-12` (1): the fibre of the pro-étale family object at
`t = 0` is the section invariant of the normal cone, `θ₀ : Li₀^* F ≅ 𝒞(π_N, 0_N)`, by base change
for the smooth `g̃` along the zero section. -/
noncomputable def proEtaleZeroFibreIso [HasCompactification N.proj] [QuasiCompact N.proj] :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
      (D.proEtaleFamilyObject Λ) ≅ ProEtale.sectionInvariant Λ N.proj N.zeroSection :=
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_zeroFibre
  sectionInvariantBaseChangeIso Λ D.isPullback_zeroFibre D.sect N.zeroSection D.comp_zeroFibre

/-- The fibre identification at `t = 1` is the image under `ν^*` of the étale one. -/
theorem proEtaleOneFibreIso_eq_comparison [HasCompactification g] [QuasiCompact g] :
    D.proEtaleOneFibreIso Λ =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
        (ProEtale.sectionInvariantComparisonIso Λ D.proj D.sect) ≪≫
      (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) _).app _ ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.mapIso
        (D.oneFibreIso Λ) ≪≫
      (ProEtale.sectionInvariantComparisonIso Λ g s).symm :=
  rfl

/-- The fibre identification at `t = 0` is the image under `ν^*` of the étale one. -/
theorem proEtaleZeroFibreIso_eq_comparison [HasCompactification N.proj] [QuasiCompact N.proj] :
    D.proEtaleZeroFibreIso Λ =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
        (ProEtale.sectionInvariantComparisonIso Λ D.proj D.sect) ≪≫
      (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) _).app _ ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.mapIso
        (D.zeroFibreIso Λ) ≪≫
      (ProEtale.sectionInvariantComparisonIso Λ N.proj N.zeroSection).symm :=
  rfl

omit [QuasiSeparatedSpace B]

variable [HasCompactification g] {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [QuasiCompact D.proj]

/-- Blueprint `lemma-section-normal-bundle--1` (2), (3): the constancy comparison
`κ : F ≅ La^* 𝒞(g, s)` of the pro-étale family object, the image under `ν^*` of the étale
comparison normalized against the fibre identification at `t = 1`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObjectIso`). -/
noncomputable def proEtaleFamilyObjectIso :
    D.proEtaleFamilyObject Λ ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).leftDerivedFunctor.obj
        (ProEtale.sectionInvariant Λ g s) :=
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  ProEtale.sectionInvariantComparisonIso Λ D.proj D.sect ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) _).mapDerivedCategory.mapIso
      (D.familyObjectIso Λ aB (D.oneFibreIso Λ)) ≪≫
    ((derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) _).app _).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); B) ↘ B)).leftDerivedFunctor.mapIso
      (ProEtale.sectionInvariantComparisonIso Λ g s).symm

variable [HasCompactification N.proj]

/-- Blueprint `lemma-section-normal-bundle`, `lemma-section-normal-bundle--1`: the pro-étale DNC
isomorphism `δ_{g,s} : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)`, the image under `ν^*` of the étale DNC isomorphism
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.sectionInvariantIso`, that is, the
restriction to `t = 0` of the constancy comparison normalized at `t = 1`. -/
noncomputable def proEtaleSectionInvariantIso :
    ProEtale.sectionInvariant Λ g s ≅ ProEtale.sectionInvariant Λ N.proj N.zeroSection :=
  ProEtale.sectionInvariantComparisonIso Λ g s ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) B).mapDerivedCategory.mapIso
      (D.sectionInvariantIso Λ aB) ≪≫
    (ProEtale.sectionInvariantComparisonIso Λ N.proj N.zeroSection).symm

/-- Blueprint `lemma-section-normal-bundle--1`: *compatibility with base change.* Along every
`u : B' ⟶ B` the pro-étale DNC isomorphism restricts to the image under `ν^*` of the restricted
étale DNC isomorphism, through the identifications `Lu^* ν^* ≅ ν^* Lu^*` and
`𝒞 ≅ ν^* 𝒞_ét`. The restricted étale DNC isomorphism is the identity of the standard object in
every system of coordinates over `B'`
(`leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso`). -/
theorem leftDerivedUpperStar_map_proEtaleSectionInvariantIso_hom {B' : Scheme.{u}} (u : B' ⟶ B) :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
        (D.proEtaleSectionInvariantIso Λ aB).hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
          (ProEtale.sectionInvariantComparisonIso Λ g s).hom ≫
        (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) u).hom.app _ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) B').mapDerivedCategory.map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
            (D.sectionInvariantIso Λ aB).hom) ≫
        (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) u).inv.app _ ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) u).leftDerivedFunctor.map
          (ProEtale.sectionInvariantComparisonIso Λ N.proj N.zeroSection).inv := by
  have h := (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) u).hom.naturality
    (D.sectionInvariantIso Λ aB).hom
  simp only [Functor.comp_obj, Functor.comp_map] at h
  simp only [proEtaleSectionInvariantIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp]
  congr 1
  rw [← reassoc_of% h, Iso.hom_inv_id_app_assoc]

end Scheme.Hom.DeformationToNormalConeData

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}}

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line, pro-étale

Let `Λ` be a finite coefficient ring, `g : V ⟶ B` smooth of pure relative dimension `d` with a
closed section `s`, over a base `B` separated and locally of finite type over a field `k` on
which the characteristic of `Λ` is invertible, and let `g̃ : 𝒟_s V ⟶ 𝔸¹_B` be a deformation to the
normal cone `N_s ⟶ B` (the situation of `prose-09-12`). Then the pro-étale section
invariants are isomorphic,

`𝒞(g, s) ≅ 𝒞(π_N, 0_N)`,

by the DNC isomorphism
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.proEtaleSectionInvariantIso`. -/
theorem nonempty_iso_sectionInvariant_normalCone (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g] (s : B ⟶ V)
    (N : Scheme.Hom.NormalConeData d s) [HasCompactification N.proj]
    (D : Scheme.Hom.DeformationToNormalConeData d g s N) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] [QuasiCompact D.proj] :
    Nonempty (sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection) :=
  ⟨D.proEtaleSectionInvariantIso Λ aB⟩

/-- Blueprint `lemma-section-normal-bundle`: DNC invariance of the section dualizing line,
pro-étale, for the normal cone of the section

Let `g : V ⟶ B` be separated, quasi-compact and smooth of pure relative dimension `d` with a
closed section `s`, over a base `B` quasi-compact, separated and locally of finite type over a
field on which the characteristic of the finite coefficient ring `Λ` is invertible. Then the
pro-étale section invariant of `(g, s)` is isomorphic to that of the normal cone
`π_N : N_s = Spec (⨁ I^r / I^{r+1}) ⟶ B` with its zero section, through the deformation
`D_s V = Spec_V 𝒪_V[t, I t⁻¹]` (`AlgebraicGeometry.Scheme.Hom.deformationToNormalConeData`).
The compactifiability hypotheses hold by Nagata's theorem, see
`AlgebraicGeometry.Scheme.Hom.hasCompactification_normalConeProj` for `π_N`. -/
theorem nonempty_iso_sectionInvariant_normalConeProj (d : ℕ)
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.normalConeProj g s)] {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB] [CompactSpace B]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ g s ≅
      sectionInvariant Λ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) :=
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have : HasCompactification (Scheme.Hom.normalConeData d hs).proj :=
    ‹HasCompactification (Scheme.Hom.normalConeProj g s)›
  have : QuasiCompact (Scheme.Hom.deformationToNormalConeData d g s hs).proj :=
    inferInstanceAs (QuasiCompact (Scheme.Hom.deformationSpaceProj g s))
  nonempty_iso_sectionInvariant_normalCone Λ d g s (Scheme.Hom.normalConeData d hs)
    (Scheme.Hom.deformationToNormalConeData d g s hs) aB

end ProEtale

end AlgebraicGeometry
