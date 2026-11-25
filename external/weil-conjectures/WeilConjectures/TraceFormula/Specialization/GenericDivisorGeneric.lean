/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ConstructibleGeneration
public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreBaseChange
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorTriangulated
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethEquivariant
public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.TraceFormula.Correspondence
public import WeilConjectures.TraceFormula.Specialization.TraitProduct
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange

/-!

# Generic vanishing of the defect is a triangulated condition

Let `X` be a `k`-scheme, `Z = V(I) ⊆ X` a closed subscheme and `C_{X,Z}(L)` the defect of the
specialization (`ProEtale.CondensedRing.specializationDefect`), a complex on the special fibre
`N_⊥ Z ≅ Z ⊗ k'` of the constant family of `Z`. The defect *vanishes generically* on `Z` if its
restriction to the inverse image of some dense open `U ⊆ Z` is zero
(`ProEtale.CondensedRing.genericallyVanishingDefect`); this is the conclusion of blueprint
`lemma-vanishing-generic-points-principal-divisor--1`.

This file shows that the complexes with generically vanishing defect form a triangulated
subcategory, stable under retracts
(`ProEtale.CondensedRing.isTriangulated_genericallyVanishingDefect`). Over a fixed open `W` of
`N_⊥ Z`, the restricted defect vanishes exactly on the isomorphism locus of the restricted
zero-section map, a natural transformation of triangulated functors commuting with the shifts
(`ProEtale.CondensedRing.restrictedZeroSectionNatTrans`); since two dense opens meet in a dense
open, the union of these loci over the dense opens of `Z` is still triangulated.

Consequently, for `ℚ̄_ℓ`-coefficients, the generic vanishing of the defect for every bounded
constructible complex reduces to the lisse generators `Rg_! Rj_! L`
(`ProEtale.CondensedRing.genericallyVanishingDefect_of_lisseGenerator`,
`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect_of_lisseGenerator`); note that no
hypothesis `Li^* L = 0` is needed.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Restriction to smaller opens -/

section Restriction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If the restriction of a morphism `f` of complexes on a scheme `T` to an open `W` is an
isomorphism, so is its restriction to any smaller open `W' ≤ W`. -/
lemma isIso_leftDerivedUpperStar_ι_map_of_le {T : Scheme.{u}} {W W' : T.Opens} (hW : W' ≤ W)
    {A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (f : A ⟶ B) [IsIso (L((W.ι)^*⟦Λ⟧).map f)] :
    IsIso (L((W'.ι)^*⟦Λ⟧).map f) := by
  rw [← T.homOfLE_ι hW, NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ (T.homOfLE hW) W.ι),
    Functor.comp_map]
  infer_instance

/-- If the restriction of a complex on a scheme `T` to an open `W` is zero, so is its restriction
to any smaller open `W' ≤ W`. -/
lemma isZero_leftDerivedUpperStar_ι_obj_of_le {T : Scheme.{u}} {W W' : T.Opens} (hW : W' ≤ W)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hA : IsZero (L((W.ι)^*⟦Λ⟧).obj A)) :
    IsZero (L((W'.ι)^*⟦Λ⟧).obj A) := by
  rw [← T.homOfLE_ι hW]
  exact (Functor.map_isZero _ hA).of_iso
    ((leftDerivedUpperStarComp Λ (T.homOfLE hW) W.ι).app A)

/-- The vanishing of the pullback of a complex along a morphism only depends on the morphism. -/
lemma isZero_leftDerivedUpperStar_obj_of_eq {T T' : Scheme.{u}} {a b : T' ⟶ T} (hab : a = b)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hA : IsZero (L((a)^*⟦Λ⟧).obj A)) :
    IsZero (L((b)^*⟦Λ⟧).obj A) := by
  subst hab
  exact hA

/-- For an open immersion `c : T' ⟶ T` and an open `W' ⊆ T'`, if the restriction to `W'` of the
pullback `c^* A` of a complex `A` on `T` vanishes, so does the restriction of `A` to the image
`c(W')`. -/
lemma isZero_leftDerivedUpperStar_image_ι_obj {T T' : Scheme.{u}} (c : T' ⟶ T)
    [IsOpenImmersion c] (W' : T'.Opens)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hA : IsZero (L((W'.ι)^*⟦Λ⟧).obj (L((c)^*⟦Λ⟧).obj A))) :
    IsZero (L(((c ''ᵁ W').ι)^*⟦Λ⟧).obj A) :=
  isZero_leftDerivedUpperStar_obj_of_eq Λ (c.isoImage_inv_ι W')
    ((Functor.map_isZero _ (hA.of_iso ((leftDerivedUpperStarComp Λ W'.ι c).app A))).of_iso
      ((leftDerivedUpperStarComp Λ _ _).app A))

end Restriction

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The restricted zero-section map -/

/-- The zero-section map `ε_{X,Z}` restricted to an open `W` of the special fibre `N_⊥ Z` of the
constant family of the centre, as a natural transformation `L ↦ ε_{X,Z}(L)|_W`. -/
noncomputable def restrictedZeroSectionNatTrans
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :=
  Functor.whiskerRight ((zeroSectionDeformationModelHom X I k').pullbackExchange Λ)
    L((W.ι)^*⟦Λ⟧)

instance (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :
    NatTrans.CommShift (restrictedZeroSectionNatTrans X I k' Λ W) ℤ := by
  unfold restrictedZeroSectionNatTrans
  infer_instance

/-- The restriction of the defect `C_{X,Z}(L)` to an open `W` of `N_⊥ Z` vanishes if and only if
the restriction of the zero-section map `ε_{X,Z}(L)` to `W` is an isomorphism. -/
theorem isZero_restrict_specializationDefect_iff
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    IsZero ((L((W.ι)^*⟦Λ⟧)).obj (specializationDefect X I k' Λ L)) ↔
      (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus L := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  exact Triangle.isZero₃_iff_isIso₁ _ ((L((W.ι)^*⟦Λ⟧)).map_distinguished _ hT)

/-- The isomorphism loci of the restricted zero-section maps decrease with the open. -/
lemma isoLocus_restrictedZeroSectionNatTrans_mono
    {W W' : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens} (hW : W' ≤ W)
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (hL : (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus L) :
    (restrictedZeroSectionNatTrans X I k' Λ W').isoLocus L := by
  have : IsIso ((L((W.ι)^*⟦Λ⟧)).map (zeroSectionMap X I k' Λ L)) := hL
  exact isIso_leftDerivedUpperStar_ι_map_of_le Λ hW (zeroSectionMap X I k' Λ L)

/-! ### Generic vanishing of the defect -/

/-- The complexes `L` on `X` whose defect `C_{X,Z}(L)` *vanishes generically* on the centre: the
restriction of `C_{X,Z}(L)` to the inverse image in `N_⊥ Z ≅ Z ⊗ k'` of some dense open `U ⊆ Z`
is zero. -/
def genericallyVanishingDefect :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :=
  fun L ↦ ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
    IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦Λ⟧)).obj
      (specializationDefect X I k' Λ L))

/-- Generic vanishing of the defect in terms of the restricted zero-section maps. -/
lemma genericallyVanishingDefect_iff
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    genericallyVanishingDefect X I k' Λ L ↔
      ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
        (restrictedZeroSectionNatTrans X I k' Λ
          ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)).isoLocus L := by
  simp only [genericallyVanishingDefect, isZero_restrict_specializationDefect_iff]

/-- A complex whose defect vanishes has generically vanishing defect. -/
lemma genericallyVanishingDefect_of_isZero
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))} (hL : IsZero (specializationDefect X I k' Λ L)) :
    genericallyVanishingDefect X I k' Λ L :=
  ⟨⊤, dense_univ, Functor.map_isZero _ hL⟩

/-- Two dense opens of the centre meet in a dense open whose inverse image in `N_⊥ Z` is
contained in both inverse images. -/
lemma genericallyVanishingDefect_of_two
    {L₁ L₂ L₃ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (h : ∀ W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens,
      (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus L₁ →
      (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus L₂ →
      (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus L₃)
    (h₁ : genericallyVanishingDefect X I k' Λ L₁) (h₂ : genericallyVanishingDefect X I k' Λ L₂) :
    genericallyVanishingDefect X I k' Λ L₃ := by
  rw [genericallyVanishingDefect_iff] at h₁ h₂ ⊢
  obtain ⟨U₁, hU₁, hL₁⟩ := h₁
  obtain ⟨U₂, hU₂, hL₂⟩ := h₂
  refine ⟨U₁ ⊓ U₂, hU₁.inter_of_isOpen_left hU₂ U₁.isOpen, h _ ?_ ?_⟩
  · exact isoLocus_restrictedZeroSectionNatTrans_mono X I k' Λ
      (Hom.preimage_mono _ inf_le_left) hL₁
  · exact isoLocus_restrictedZeroSectionNatTrans_mono X I k' Λ
      (Hom.preimage_mono _ inf_le_right) hL₂

instance : (genericallyVanishingDefect X I k' Λ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨U, hU, hL⟩ ↦
    ⟨U, hU, hL.of_iso (Functor.mapIso _
      (nonempty_specializationDefect_iso X I k' Λ e).some.symm)⟩

instance : (genericallyVanishingDefect X I k' Λ).IsStableUnderRetracts where
  of_retract r := fun ⟨U, hU, hL⟩ ↦ by
    rw [isZero_restrict_specializationDefect_iff] at hL
    exact ⟨U, hU, (isZero_restrict_specializationDefect_iff X I k' Λ _ _).2
      ((restrictedZeroSectionNatTrans X I k' Λ _).isoLocus.prop_of_retract r hL)⟩

/-- **The complexes with generically vanishing defect form a triangulated subcategory.** -/
instance isTriangulated_genericallyVanishingDefect :
    (genericallyVanishingDefect X I k' Λ).IsTriangulated where
  exists_zero := by
    obtain ⟨Z, hZ, hQ⟩ :=
      (restrictedZeroSectionNatTrans X I k' Λ ⊤).isoLocus.exists_prop_of_containsZero
    exact ⟨Z, hZ, (genericallyVanishingDefect_iff X I k' Λ Z).2 ⟨⊤, dense_univ,
      isoLocus_restrictedZeroSectionNatTrans_mono X I k' Λ le_top hQ⟩⟩
  isStableUnderShiftBy n :=
    { le_shift L hL := by
        rw [ObjectProperty.prop_shift_iff]
        exact genericallyVanishingDefect_of_two X I k' Λ (L₁ := L) (L₂ := L)
          (fun W h _ ↦ (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus.le_shift n _ h) hL hL }
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    genericallyVanishingDefect_of_two X I k' Λ
      (fun W h₁' h₃' ↦ (restrictedZeroSectionNatTrans X I k' Λ W).isoLocus
        |>.ext_of_isTriangulatedClosed₂ T hT h₁' h₃') h₁ h₃

/-! ### Reduction to the lisse generators -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Reduction of generic vanishing to the lisse generators**: if the defect `C_{X,Z}` vanishes
generically on the lisse generators `Rg_! Rj_! L` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, it vanishes generically on
every bounded constructible complex. -/
theorem genericallyVanishingDefect_of_lisseGenerator
    (h : ∀ N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧, lisseGenerator ℓ X N →
      genericallyVanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ) N.obj)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    genericallyVanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj := by
  let Q := (genericallyVanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ)).inverseImage
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB ↦ (genericallyVanishingDefect X I k' _).prop_of_retract
      (r.map (boundedConstructible _).ι) hB⟩
  exact (ObjectProperty.triangEnvelope_le_iff (Q := Q) _).mpr (fun N hN ↦ h N hN) _
    (triangEnvelope_lisseGenerator ℓ X L)

/-- **Reduction of blueprint `lemma-vanishing-generic-points-principal-divisor--1` to the lisse
generators**: if the defect `C_{X,Z}` vanishes generically on the lisse generators `Rg_! Rj_! L` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, then for every bounded constructible `L` there is a dense open `U ⊆ Z` over which
`C_{X,Z}(L)` vanishes. -/
theorem exists_dense_isZero_specializationDefect_of_lisseGenerator
    (h : ∀ N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧, lisseGenerator ℓ X N →
      genericallyVanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ) N.obj)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) :=
  genericallyVanishingDefect_of_lisseGenerator X I k' h L


instance : (vanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ)).IsStableUnderRetracts where
  of_retract {A B} r hB := by
    rw [vanishingDefect_eq_isoLocus] at hB ⊢
    exact ((zeroSectionDeformationModelHom X I k').pullbackExchange _).isoLocus.prop_of_retract r hB

instance : (vanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ)).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso (nonempty_specializationDefect_iso X I k' _ e).some.symm

/-- **Reduction of the vanishing of the defect to the lisse generators**: if the defect `C_{X,Z}`
vanishes on the lisse generators `Rg_! Rj_! L` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, it vanishes on every bounded
constructible complex. -/
theorem isZero_specializationDefect_of_lisseGenerator
    (h : ∀ N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧, lisseGenerator ℓ X N →
      IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) N.obj))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  let Q := (vanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ)).inverseImage
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB ↦ (vanishingDefect X I k' _).prop_of_retract (r.map (boundedConstructible _).ι) hB⟩
  exact (ObjectProperty.triangEnvelope_le_iff (Q := Q) _).mpr (fun N hN ↦ h N hN) _
    (triangEnvelope_lisseGenerator ℓ X L)

end AlgebraicGeometry.ProEtale.CondensedRing
