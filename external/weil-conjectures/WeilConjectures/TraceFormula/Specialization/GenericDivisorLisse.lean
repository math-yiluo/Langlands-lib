/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorPointwise

/-!

# Vanishing of the restricted specialization near a point: reduction to lisse generators

Let `X` be a `k`-scheme, `Z = V(I) ⊆ X` a closed subscheme, `e : N_⊥ Z ⟶ N_Z X` the zero section
of the special fibre of the deformation to the normal cone and `ζ ∈ Z`. The restriction
`Le^* Ψ_X(L)` of the specialization of a complex `L` on `X` *vanishes near* `ζ` if it is zero over
the inverse image in `N_⊥ Z ≅ Z ⊗ k'` of an open neighbourhood of `ζ` in `Z`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear`). These complexes form a triangulated
subcategory stable under retracts
(`ProEtale.CondensedRing.isTriangulated_nearbyCyclesVanishNear`).

Consequently, for `ℚ̄_ℓ`-coefficients and a complex `L` with `Li^* L = 0`, which is the extension
by zero `j_! Lj^* L` of its restriction to the complement `j : X ∖ Z ⟶ X`, the vanishing of
`Le^* Ψ_X(L)` near `ζ` reduces to the extensions by zero `j_! N` of the lisse generators `N` of
`Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧` (`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_of_lowerShriek`).

For a lisse generator `N ≅ Rg_! Rj'_! M` supported on the closed subscheme `g : Z₀ ⟶ X ∖ Z`, the
vanishing holds near every point `ζ` of `Z` outside the closure in `X` of the image of `Z₀`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_of_notMem_closure`):
`j_! N` vanishes on the complement of this closure, hence so does the defect, which is
`Le^* Ψ_X(j_! N)[1]` since `Li^* j_! N = 0`
(`ProEtale.CondensedRing.nonempty_specializationDefect_iso_shift`).

## Unfinished

The case of a lisse generator at a generic point of a principal divisor of a normal scheme lying in
the closure of the support of the generator,
`exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure`, is `sorry`ed.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- A retract of a zero object is zero. -/
lemma isZero_of_retract {C : Type*} [Category C] [Preadditive C] {A B : C} (r : Retract B A)
    (hA : IsZero A) : IsZero B :=
  (IsZero.iff_id_eq_zero _).2 (by rw [← r.retract, hA.eq_of_src r.r 0, Limits.comp_zero])

section Abstract

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The restriction `L ↦ (Le^* Ψ_X(L))|_W` of the specialization of a complex on `X` to the zero
section `N_⊥ Z ⟶ N_Z X`, further restricted to an open `W` of `N_⊥ Z`. -/
noncomputable def restrictedZeroSectionNearbyCycles
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :=
  (deformationModel X I k').nearbyCycles Λ ⋙
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧) ⋙ L((W.ι)^*⟦Λ⟧)

noncomputable instance (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).CommShift ℤ := by
  unfold restrictedZeroSectionNearbyCycles
  infer_instance

instance (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).IsTriangulated := by
  unfold restrictedZeroSectionNearbyCycles
  infer_instance

/-- Unfolding of `restrictedZeroSectionNearbyCycles`. -/
lemma restrictedZeroSectionNearbyCycles_obj
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    (restrictedZeroSectionNearbyCycles X I k' Λ W).obj L =
      L((W.ι)^*⟦Λ⟧).obj (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj L)) :=
  rfl

/-- The complexes `L` on `X` whose specialization restricted to the zero section, `Le^* Ψ_X(L)`,
*vanishes near* a point `ζ` of the centre: its restriction to the inverse image in
`N_⊥ Z ≅ Z ⊗ k'` of some open neighbourhood of `ζ` in `Z` is zero. -/
def nearbyCyclesVanishNear (ζ : (centre X I).left) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :=
  fun L ↦ ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
    IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ
      ((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U)).obj L)

/-- If the vanishing over an open `W` of `N_⊥ Z` of the restricted specialization of `L₁` and `L₂`
implies that of `L₃`, then the vanishing near `ζ` for `L₁` and `L₂` implies that of `L₃`: two
neighbourhoods of `ζ` meet in a neighbourhood of `ζ`. -/
lemma nearbyCyclesVanishNear_of_two {ζ : (centre X I).left}
    {L₁ L₂ L₃ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))}
    (h : ∀ W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens,
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₁) →
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₂) →
      IsZero ((restrictedZeroSectionNearbyCycles X I k' Λ W).obj L₃))
    (h₁ : nearbyCyclesVanishNear X I k' Λ ζ L₁) (h₂ : nearbyCyclesVanishNear X I k' Λ ζ L₂) :
    nearbyCyclesVanishNear X I k' Λ ζ L₃ := by
  obtain ⟨U₁, hζ₁, hL₁⟩ := h₁
  obtain ⟨U₂, hζ₂, hL₂⟩ := h₂
  rw [restrictedZeroSectionNearbyCycles_obj] at hL₁ hL₂
  refine ⟨U₁ ⊓ U₂, ⟨hζ₁, hζ₂⟩, h _ ?_ ?_⟩
  · rw [restrictedZeroSectionNearbyCycles_obj]
    exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ (Hom.preimage_mono _ inf_le_left) hL₁
  · rw [restrictedZeroSectionNearbyCycles_obj]
    exact isZero_leftDerivedUpperStar_ι_obj_of_le Λ (Hom.preimage_mono _ inf_le_right) hL₂

instance (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨U, hU, hL⟩ ↦ ⟨U, hU, hL.of_iso (Functor.mapIso _ e.symm)⟩

instance (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsStableUnderRetracts where
  of_retract r := fun ⟨U, hU, hL⟩ ↦ ⟨U, hU, isZero_of_retract (r.map _) hL⟩

/-- **The complexes whose restricted specialization vanishes near `ζ` form a triangulated
subcategory.** -/
instance isTriangulated_nearbyCyclesVanishNear (ζ : (centre X I).left) :
    (nearbyCyclesVanishNear X I k' Λ ζ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨⊤, trivial, Functor.map_isZero _ (isZero_zero _)⟩⟩
  isStableUnderShiftBy n :=
    { le_shift L hL := by
        rw [ObjectProperty.prop_shift_iff]
        exact nearbyCyclesVanishNear_of_two X I k' Λ (L₁ := L) (L₂ := L)
          (fun W h _ ↦ ((shiftFunctor _ n).map_isZero h).of_iso
            (((restrictedZeroSectionNearbyCycles X I k' Λ W).commShiftIso n).app L)) hL hL }
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    nearbyCyclesVanishNear_of_two X I k' Λ
      (fun W h₁' h₃' ↦ Triangle.isZero₂_of_isZero₁₃ _
        ((restrictedZeroSectionNearbyCycles X I k' Λ W).map_distinguished _ hT) h₁' h₃') h₁ h₃

/-- A functor commuting with the shifts kills `B ≅ A[1]` if it kills `A`. -/
lemma isZero_obj_of_iso_shift_aux {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] (F : C ⥤ D)
    [F.CommShift ℤ] {A B : C} (e : B ≅ (shiftFunctor C (1 : ℤ)).obj A) (h : IsZero (F.obj A)) :
    IsZero (F.obj B) :=
  (((shiftFunctor D (1 : ℤ)).map_isZero h).of_iso ((F.commShiftIso (1 : ℤ)).app A)).of_iso
    (F.mapIso e)

/-- If the target `Ψ_Z(Li^* L)` of the zero-section map vanishes, the defect is
`Le^* Ψ_X(L)[1]`. -/
theorem nonempty_specializationDefect_iso_shift
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hL : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj L))) :
    Nonempty (specializationDefect X I k' Λ L ≅ (shiftFunctor _ (1 : ℤ)).obj
      (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
        (((deformationModel X I k').nearbyCycles Λ).obj L))) := by
  obtain ⟨g, h, hT⟩ := exists_distTriang_specializationDefect X I k' Λ L
  obtain ⟨φ, -, -⟩ := exists_iso_of_arrow_iso _ _ hT (contractible_distinguished₂ _)
    (Arrow.isoMk (Iso.refl _) (hL.iso (isZero_zero _)) ((isZero_zero _).eq_of_tgt _ _))
  exact ⟨Triangle.π₃.mapIso φ⟩

/-- If `Ψ_Z(Li^* L) = 0`, the restriction of the defect to an open `W` of `N_⊥ Z` vanishes as soon
as the restriction of `Le^* Ψ_X(L)` does. -/
theorem isZero_restrict_specializationDefect_of_isZero
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hL : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj L)))
    (hW : IsZero ((L((W.ι)^*⟦Λ⟧)).obj (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
      (((deformationModel X I k').nearbyCycles Λ).obj L)))) :
    IsZero ((L((W.ι)^*⟦Λ⟧)).obj (specializationDefect X I k' Λ L)) := by
  exact isZero_obj_of_iso_shift_aux _
    (nonempty_specializationDefect_iso_shift X I k' Λ L hL).some hW

/-- The defect of a zero complex vanishes: its zero-section map is a morphism between zero
objects. -/
theorem isZero_specializationDefect_of_isZero
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))} (hL : IsZero L) :
    IsZero (specializationDefect X I k' Λ L) := by
  rw [isZero_specializationDefect_iff]
  have hs := (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧)).map_isZero
    (NearbyCyclesModel.isZero_nearbyCycles_obj Λ (deformationModel X I k') hL)
  have ht := NearbyCyclesModel.isZero_nearbyCycles_obj Λ (deformationModel (centre X I) ⊥ k')
    ((L(((centreι X I).left)^*⟦Λ⟧)).map_isZero hL)
  exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩


/-- A functor commuting with the shifts kills `A` if it kills `B ≅ A[1]`. -/
lemma isZero_obj_of_iso_shift_of_isZero {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] {A B : C}
    (e : B ≅ (shiftFunctor C (1 : ℤ)).obj A) (h : IsZero (F.obj B)) :
    IsZero (F.obj A) :=
  IsZero.of_full_of_faithful_of_isZero (shiftFunctor D (1 : ℤ)) _
    ((h.of_iso (F.mapIso e.symm)).of_iso ((F.commShiftIso (1 : ℤ)).app A).symm)

/-- If `Ψ_Z(Li^* L) = 0`, the restriction of `Le^* Ψ_X(L)` to an open `W` of `N_⊥ Z` vanishes as
soon as the restriction of the defect does. -/
theorem isZero_restrict_of_isZero_restrict_specializationDefect
    (W : (deformationSpecialFibre (centre X I) ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hL : IsZero (((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).obj
      (L(((centreι X I).left)^*⟦Λ⟧).obj L)))
    (hW : IsZero ((L((W.ι)^*⟦Λ⟧)).obj (specializationDefect X I k' Λ L))) :
    IsZero ((L((W.ι)^*⟦Λ⟧)).obj (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).obj
      (((deformationModel X I k').nearbyCycles Λ).obj L))) :=
  isZero_obj_of_iso_shift_of_isZero _
    (nonempty_specializationDefect_iso_shift X I k' Λ L hL).some hW

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Reduction to the lisse generators**: if the restricted specialization `Le^* Ψ_X(j_! N)`
vanishes near `ζ` for the extensions by zero `j_! N` along the complement `j : X ∖ Z ⟶ X` of the
lisse generators `N` of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧`, it does for every extension by zero `j_! N`. -/
theorem nearbyCyclesVanishNear_lowerShriek_of_lisseGenerator {I : X.left.IdealSheafData}
    (ζ : (centre X I).left)
    (h : ∀ N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      lisseGenerator ℓ (overRestrict X I.support.compl) N →
      nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N).obj)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X I.support.compl)).obj N).obj := by
  let Q := (nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ).inverseImage
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X I.support.compl) ⋙
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι)
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB ↦ (nearbyCyclesVanishNear X I k' _ ζ).prop_of_retract (r.map _) hB⟩
  exact (ObjectProperty.triangEnvelope_le_iff (Q := Q) _).mpr (fun N hN ↦ h N hN) _
    (triangEnvelope_lisseGenerator ℓ _ N)

/-- **The defect vanishes near a point where `L` vanishes**: if `L` restricts to zero on an open
neighbourhood `U` in `X` of a point `ζ` of the centre, then `C_{X,Z}(L)` vanishes near `ζ`. Indeed
`C_{U, Z ∩ U}(L|_U) = 0`, and vanishing near a point is local on `X`
(`defectVanishesNear_of_isOpenImmersion`). -/
theorem defectVanishesNear_of_isZero_restrict [IsSepClosed k'] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] {I : X.left.IdealSheafData}
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (ζ : (centre X I).left) (U : X.left.Opens)
    (hU : I.subschemeι ζ ∈ U)
    (hLU : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X U)).obj L)) :
    defectVanishesNear X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ζ := by
  have hζ : ζ ∈ Set.range (centreMap (overRestrictι X U) I).left := by
    rw [range_centreMap, Set.mem_preimage, range_overRestrictι]
    exact hU
  obtain ⟨ζ', rfl⟩ := hζ
  exact defectVanishesNear_of_isOpenImmersion I k' (overRestrictι X U) L ζ'
    ⟨⊤, trivial, Functor.map_isZero _ (isZero_specializationDefect_of_isZero _ _ k' _
      ((boundedConstructible _).ι.map_isZero hLU))⟩

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The restriction `V ∩ W ⟶ W` of the open immersion of an open `V` of `X` over another open
`W`. -/
noncomputable def overRestrictInterι (V W : X.left.Opens) :
    overRestrict (overRestrict X V) ((overRestrictι X V).left ⁻¹ᵁ W) ⟶ overRestrict X W :=
  Over.homMk ((overRestrictι X V).left ∣_ W) (by simp [morphismRestrict_ι_assoc])

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
instance (V W : X.left.Opens) : IsOpenImmersion (overRestrictInterι V W).left :=
  inferInstanceAs (IsOpenImmersion ((overRestrictι X V).left ∣_ W))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The restriction to the open `W` of `X` of an open `V` of `X` is a base change of `V ⟶ X`:
```
V ∩ W ⟶ W
  │      │
  V  ⟶   X
```
-/
lemma isPullback_overRestrictInterι (V W : X.left.Opens) :
    IsPullback (overRestrictInterι V W)
      (overRestrictι (overRestrict X V) ((overRestrictι X V).left ⁻¹ᵁ W))
      (overRestrictι X W) (overRestrictι X V) := by
  have w : overRestrictInterι V W ≫ overRestrictι X W =
      overRestrictι (overRestrict X V) ((overRestrictι X V).left ⁻¹ᵁ W) ≫ overRestrictι X V := by
    ext1
    exact morphismRestrict_ι _ _
  exact IsPullback.of_map (Over.forget _) w
    (isPullback_morphismRestrict (overRestrictι X V).left W)

/-- **Extensions by zero of closed pushforwards vanish away from the support**: let `j : W ⟶ X`
be an open immersion and `g : Z₀ ⟶ W` a closed immersion. The restriction of `j_! Rg_! K` to an
open `V` of `X` missing the image of `j ∘ g` is zero. Indeed `j_!` commutes with the restriction
to `V`, and `Rg_! = Rg_*` restricts to zero on `V ∩ W`, which misses the image of `g`. -/
theorem isZero_upperStar_overRestrictι_openImmersionLowerShriek_lowerShriek {W : X.left.Opens}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X W) [IsClosedImmersion g.left]
    (K : Dᵇc(Z₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (V : X.left.Opens)
    (hV : Disjoint (V : Set X.left) (Set.range (g ≫ overRestrictι X W).left.base)) :
    IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X V)).obj
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X W)).obj ((boundedConstructibleLowerShriek ℓ g).obj K))) := by
  have sq := isPullback_overRestrictInterι V W
  set w := overRestrictInterι V W
  have hdisj : Disjoint (Set.range w.left.base) (Set.range g.left.base) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h := congrArg (overRestrictι X W).left.base hb
    have hw := congrArg (fun f ↦ f.left.base a) sq.w
    refine hV.ne_of_mem (a := (overRestrictι X W).left.base (w.left.base a)) ?_ ⟨b, h⟩ rfl
    simp only [Over.comp_left, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.comp_apply] at hw
    rw [hw, ← range_overRestrictι X V]
    exact ⟨_, rfl⟩
  refine ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
    (overRestrictι (overRestrict X V) ((overRestrictι X V).left ⁻¹ᵁ W))).map_isZero
      ((isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ w g hdisj K).of_iso
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ w).mapIso
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).app K)))).of_iso
    ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' _ ℓ sq).app _)

/-- **The restricted specialization of a lisse generator vanishes away from its support**: let
`N ≅ j_! Rg_! K` with `g : Z₀ ⟶ X ∖ Z` a closed immersion, and `ζ` a point of the centre outside
the closure in `X` of the image of `Z₀`. Then `Le^* Ψ_X(j_! N)` vanishes near `ζ`. Indeed `j_! N`
vanishes on the open complement `V` of this closure, so the defect vanishes near `ζ`
(`defectVanishesNear_of_isZero_restrict`); since `Li^* j_! N = 0`, the defect is
`Le^* Ψ_X(j_! N)[1]`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_notMem_closure [IsSepClosed k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {I : X.left.IdealSheafData}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    (K : Dᵇc(Z₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj K) (ζ : (centre X I).left)
    (hζ : I.subschemeι ζ ∉ closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  let V : X.left.Opens := ⟨(closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base))ᶜ,
    isClosed_closure.isOpen_compl⟩
  have hLV := (isZero_upperStar_overRestrictι_openImmersionLowerShriek_lowerShriek g K V
    (Set.disjoint_compl_left_iff_subset.2 subset_closure)).of_iso
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (overRestrictι X V)).mapIso
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).mapIso e))
  have hL := isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ
    (overRestrictι X I.support.compl) (centreι X I)
    (isCompl_range_overRestrictι_centreι I).disjoint N
  have hΨ := NearbyCyclesModel.isZero_nearbyCycles_obj (Profinite.padicAlgClRingObj ℓ)
    (deformationModel (centre X I) ⊥ k')
    (((boundedConstructible _).ι.map_isZero hL).of_iso
      ((boundedConstructibleUpperStarCompatibility _ ℓ (centreι X I)).symm.app _))
  obtain ⟨U, hζU, hU⟩ := defectVanishesNear_of_isZero_restrict k' _ ζ V hζ hLV
  exact ⟨U, hζU, isZero_restrict_of_isZero_restrict_specializationDefect X I k' _ _ _ hΨ hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing
