/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ZeroSection

/-!

# The zero-section map and the defect of the specialization

Let `X` be a `k`-scheme, `I` an ideal sheaf on `X` with closed subscheme `i : Z = V(I) ⟶ X`, and
`k'` a field over `k`. The deformation to the normal cone `𝒟_Z X` of `Z` over the trait
`S = Spec k'⟦t⟧` (`ProEtale.CondensedRing.deformationModel X I k'`) receives the deformation of the
zero ideal of `Z`, the *constant family* `Z × S` (`ProEtale.CondensedRing.deformationModel` of
`⊥`), through the morphism of models `ẽ : Z × S ⟶ 𝒟_Z X` induced by `i`
(`ProEtale.CondensedRing.zeroSectionDeformationModelHom`, blueprint `prose-E-04`). Its
special fibre is the zero section `e : Z ⊗ k' ⟶ N_Z X ⊗ k'`.

This file defines (blueprint `prose-E-04`)
* the *zero-section map* `ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)`, the pullback exchange
  along `ẽ` (`ProEtale.CondensedRing.zeroSectionMap`);
* the *defect* `C_{X,Z}(L)`, a cone of `ε_{X,Z}(L)`
  (`ProEtale.CondensedRing.specializationDefect`).

The blueprint composes `ε_{X,Z}(L)` with the inverse of the specialization unit
`σ_Z(Li^* L) : Li^* L ⟶ Ψ_{Z × S}(Li^* L)` of the constant family, which is an isomorphism
(blueprint `lemma-nearby-cycles-constant-family--1`); this does not change the cone up to
isomorphism, and the vanishing statements below do not depend on it.

## Main results

- `ProEtale.CondensedRing.isZero_specializationDefect_iff`: the defect vanishes if and only if
  the zero-section map is an isomorphism.
- `ProEtale.CondensedRing.nonempty_specializationDefect_iso`: the defect is invariant under
  isomorphisms of complexes.

## Implementation notes

The blueprint forms the cofibre in a derived enhancement, so that `C_{X,Z}` is a functor. Here the
defect is a chosen cone in the triangulated derived category, so it is only defined up to
non-unique isomorphism; all statements about it are invariant under isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The centre `Z = V(I)` of the deformation, as a `k`-scheme. -/
noncomputable def centre : Over (Spec (.of k)) :=
  Over.mk (I.subschemeι ≫ X.hom)

/-- The closed immersion `i : Z = V(I) ⟶ X`. -/
noncomputable def centreι : centre X I ⟶ X :=
  Over.homMk I.subschemeι rfl

@[simp]
lemma centreι_left : (centreι X I).left = I.subschemeι :=
  rfl

instance : IsClosedImmersion (centreι X I).left :=
  inferInstanceAs (IsClosedImmersion I.subschemeι)

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (centre X I).hom :=
  inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ X.hom))

instance [QuasiCompact X.hom] : QuasiCompact (centre X I).hom :=
  inferInstanceAs (QuasiCompact (I.subschemeι ≫ X.hom))

instance [IsSeparated X.hom] : IsSeparated (centre X I).hom :=
  inferInstanceAs (IsSeparated (I.subschemeι ≫ X.hom))

/-- The zero ideal of `V(I)` contains the pullback of `I`, chart by chart. -/
lemma siteIdeal_map_appLE_le_bot ⦃U' : (centre X I).left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ (centreι X I).left ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map ((centreι X I).left.appLE U.1 U'.1 hU).hom ≤
      (⊥ : (centre X I).left.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map I.le_map_bot_subschemeι hU

/-- The zero section `e : N_⊥ Z ⟶ N_I X` of the special fibre of the deformation to the normal
cone, where `N_⊥ Z ≅ Z ⊗ k'` is the special fibre of the constant family. -/
noncomputable def zeroSectionSpecialFibreMap :
    deformationSpecialFibre (centre X I) ⊥ k' ⟶ deformationSpecialFibre X I k' :=
  deformationSpecialFibreMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k'

/-- The morphism of models `ẽ : Z × S ⟶ 𝒟_Z X` from the constant family of `Z = V(I)` (the
deformation of the zero ideal of `Z`) to the deformation to the normal cone of `Z` in `X`, over
`i : Z ⟶ X` and the zero section `e` (blueprint `prose-E-04`). -/
noncomputable def zeroSectionDeformationModelHom :
    (deformationModel (centre X I) ⊥ k').Hom (deformationModel X I k') (centreι X I).left
      (zeroSectionSpecialFibreMap X I k').left :=
  deformationModelHom (centreι X I) (siteIdeal_map_appLE_le_bot X I) k'

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The *zero-section map* `ε_{X,Z}(L) : Le^* Sp_{X,Z}(L) ⟶ Ψ_{Z × S}(Li^* L)` (blueprint
`prose-E-04` (2)): the pullback exchange along `ẽ : Z × S ⟶ 𝒟_Z X`. -/
noncomputable def zeroSectionMap
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj L) ⟶
      ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
        (L(((centreι X I).left)^*⟦Λ⟧).obj L) :=
  ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ).app L

/-- The zero-section map `ε_{X,Z}` is natural in `L`. -/
lemma zeroSectionMap_naturality
    {L L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))} (φ : L ⟶ L') :
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        (((deformationModel X I k').nearbyCycles Λ).map φ) ≫ zeroSectionMap X I k' Λ L' =
      zeroSectionMap X I k' Λ L ≫ ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map
        (L(((centreι X I).left)^*⟦Λ⟧).map φ) :=
  ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ).naturality φ

/-- The zero-section map `ε_{X,Z}(L)` has a cone: it is the first morphism of a distinguished
triangle. -/
lemma exists_distTriang_zeroSectionMap
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    ∃ (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (deformationSpecialFibre (centre X I) ⊥ k').left) Ab.{u + 1})
        (condensedRingObj Λ (deformationSpecialFibre (centre X I) ⊥ k').left)))
      (g : _ ⟶ C) (h : C ⟶ _), Triangle.mk (zeroSectionMap X I k' Λ L) g h ∈ distTriang _ :=
  distinguished_cocone_triangle _

/-- The *defect* `C_{X,Z}(L)` of the specialization (blueprint `prose-E-04` (3)):
a cone of the zero-section map `ε_{X,Z}(L)`. -/
noncomputable def specializationDefect
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (deformationSpecialFibre (centre X I) ⊥ k').left) Ab.{u + 1})
      (condensedRingObj Λ (deformationSpecialFibre (centre X I) ⊥ k').left)) :=
  (exists_distTriang_zeroSectionMap X I k' Λ L).choose

/-- The defect `C_{X,Z}(L)` is the third object of a distinguished triangle on the zero-section map
`ε_{X,Z}(L)`. -/
lemma exists_distTriang_specializationDefect
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    ∃ (g : _ ⟶ specializationDefect X I k' Λ L) (h : specializationDefect X I k' Λ L ⟶ _),
      Triangle.mk (zeroSectionMap X I k' Λ L) g h ∈ distTriang _ :=
  (exists_distTriang_zeroSectionMap X I k' Λ L).choose_spec

/-- The defect vanishes if and only if the zero-section map is an isomorphism. -/
theorem isZero_specializationDefect_iff
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    IsZero (specializationDefect X I k' Λ L) ↔ IsIso (zeroSectionMap X I k' Λ L) := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  exact Triangle.isZero₃_iff_isIso₁ _ hT

/-- The defect is invariant under isomorphisms of complexes. -/
theorem nonempty_specializationDefect_iso
    {L L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))} (e : L ≅ L') :
    Nonempty (specializationDefect X I k' Λ L ≅ specializationDefect X I k' Λ L') := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  obtain ⟨g', h', hT'⟩ := exists_distTriang_specializationDefect X I k' Λ L'
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_iso_of_arrow_iso _ _ hT hT'
    (Arrow.isoMk (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).mapIso
      (((deformationModel X I k').nearbyCycles Λ).mapIso e))
      (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).mapIso
        (L(((centreι X I).left)^*⟦Λ⟧).mapIso e))
      (zeroSectionMap_naturality X I k' Λ e.hom))
  exact ⟨Triangle.π₃.mapIso φ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
