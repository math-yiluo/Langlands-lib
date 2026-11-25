/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction

/-!
# Naturality of the restriction triangle inside a closed support

The two maps of the restriction triangle

`RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F) ⟶ RΓ_{B ∩ C}(T, F)[1]`

of `AlgebraicGeometry.Etale.exists_distTriang_supportRestriction` (blueprint
`proposition-purity-vector-bundles`) are natural in `F`. Both are built from maps of supported
terms `Ri_! Ri^! F` which are characterised by their composite with a counit of `Ri_! ⊣ Ri^!`;
naturality follows from the uniqueness of these factorisations.

## Main statements

- `AlgebraicGeometry.Etale.supportedRestriction_naturality`
- `AlgebraicGeometry.Etale.supportedInclusion_naturality`
- `AlgebraicGeometry.Etale.supportInclusionMap_naturality`
- `AlgebraicGeometry.Etale.supportRestrictionMap_naturality`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Restriction

variable {U X Z Z' : Scheme.{u}}

/-- The pullback along `e : U ⟶ X` of a supported term `Ri_! Ri^! L` is supported on the base
change `Z'` of `Z`: it vanishes on the open complement of `i'`. -/
lemma isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_supported (e : U ⟶ X)
    (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))))
          := by
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ)
      i
    i.openComplement.ι (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    (i'.openComplement.ι ≫ e) ?_ _).of_iso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i'.openComplement.ι e).app _).symm
  rw [← compl_compl (Set.range i.openComplement.ι), ← i.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.range_snd_of_isPullback hg]
  exact ⟨z, hx.symm⟩

/-- **Naturality of the restriction of supports.** For `φ : L₁ ⟶ L₂` on `X`, `φ' : L₁' ⟶ L₂'`
on `U` and identifications `τₖ : Le^* Lₖ ≅ Lₖ'` compatible with `φ` and `φ'`, the restrictions
of supports `Le^* (Ri_! Ri^! Lₖ) ⟶ Ri'_! Ri'^! Lₖ'`
(`AlgebraicGeometry.Etale.supportedRestriction`) commute with the maps induced by `φ` and
`φ'`. -/
theorem supportedRestriction_naturality (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i']
 (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L₁ L₂ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L₁' L₂' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ₁ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L₁ ≅ L₁') (τ₂ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L₂
        ≅ L₂')
    (φ : L₁ ⟶ L₂) (φ' : L₁' ⟶ L₂') (h : (L((e)^*[ModuleCat.{u + 1} Λ])).map φ ≫ τ₂.hom = τ₁.hom ≫
        φ') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map ((R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map φ)) ≫
        supportedRestriction Λ e i i' g hg L₂ L₂' τ₂ =
      supportedRestriction Λ e i i' g hg L₁ L₁' τ₁ ≫
        (R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map φ') := by
  have hε : (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map φ) ≫
      (rightDerivedUpperShriekAdjunction Λ i).counit.app L₂ =
        (rightDerivedUpperShriekAdjunction Λ i).counit.app L₁ ≫ φ :=
    (rightDerivedUpperShriekAdjunction Λ i).counit.naturality φ
  have hε' : (R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map φ') ≫
      (rightDerivedUpperShriekAdjunction Λ i').counit.app L₂' =
        (rightDerivedUpperShriekAdjunction Λ i').counit.app L₁' ≫ φ' :=
    (rightDerivedUpperShriekAdjunction Λ i').counit.naturality φ'
  have h₁ := (existsUnique_supportedRestriction Λ e i i' g hg L₁ L₁' τ₁).exists.choose_spec
  have h₂ := (existsUnique_supportedRestriction Λ e i i' g hg L₂ L₂' τ₂).exists.choose_spec
  change supportedRestriction Λ e i i' g hg L₁ L₁' τ₁ ≫ _ = _ at h₁
  change supportedRestriction Λ e i i' g hg L₂ L₂' τ₂ ≫ _ = _ at h₂
  refine (existsUnique_comp_counit_of_isZero Λ i' i'.openComplement.ι
    i'.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_supported Λ e i i' g hg L₁)
    ((L((e)^*[ModuleCat.{u + 1} Λ])).map ((rightDerivedUpperShriekAdjunction Λ i).counit.app L₁) ≫
      τ₁.hom ≫ φ')).unique ?_ ?_
  · rw [assoc, h₂, ← Functor.map_comp_assoc, hε, Functor.map_comp_assoc, h]
  · rw [assoc, hε', reassoc_of% h₁]

end Restriction

variable {T B C D : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) (d : D ⟶ T)
  [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
  (hd : Set.range d.base = Set.range b.base ∩ Set.range c.base)

omit [IsClosedImmersion c] in
/-- The map of supported terms `Rd_! Rd^! F ⟶ Rb_! Rb^! F` for `D ⊆ B`
(`AlgebraicGeometry.Etale.supportedInclusion`) is natural in `F`. -/
theorem supportedInclusion_naturality {F F' : DerivedCategory (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))}
    (φ : F ⟶ F') :
    supportedInclusion Λ b c d hd F ≫ (R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ) =
      (R(d)_![ModuleCat.{u + 1} Λ]).map ((R(d)^![Λ]).map φ) ≫ supportedInclusion Λ b c d hd F' := by
  have hεb : (R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ) ≫
      (rightDerivedUpperShriekAdjunction Λ b).counit.app F' =
        (rightDerivedUpperShriekAdjunction Λ b).counit.app F ≫ φ :=
    (rightDerivedUpperShriekAdjunction Λ b).counit.naturality φ
  have hεd : (R(d)_![ModuleCat.{u + 1} Λ]).map ((R(d)^![Λ]).map φ) ≫
      (rightDerivedUpperShriekAdjunction Λ d).counit.app F' =
        (rightDerivedUpperShriekAdjunction Λ d).counit.app F ≫ φ :=
    (rightDerivedUpperShriekAdjunction Λ d).counit.naturality φ
  refine (existsUnique_comp_counit_of_isZero Λ b b.openComplement.ι
    b.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_supported_of_inter Λ b c d hd F)
    ((rightDerivedUpperShriekAdjunction Λ d).counit.app F ≫ φ)).unique ?_ ?_
  · rw [assoc, hεb, supportedInclusion_comp_counit_assoc]
  · rw [assoc, supportedInclusion_comp_counit, hεd]

omit [IsClosedImmersion c] in
/-- Blueprint `proposition-purity-vector-bundles`: Restriction triangle inside a closed
support (naturality of the first map).

The inclusion of supports `RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F)`
(`AlgebraicGeometry.Etale.supportInclusionMap`) is natural in `F`. -/
theorem supportInclusionMap_naturality {F F' : DerivedCategory (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))}
    (φ : F ⟶ F') :
    supportInclusionMap Λ b c d hd F ≫ (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).map
        φ =
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) d).map φ ≫ supportInclusionMap Λ b c d
          hd F' := by
  have h₁ : (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) d).map φ ≫
      ((rightDerivedSectionsWithSupportIso Λ d).app F').hom =
        ((rightDerivedSectionsWithSupportIso Λ d).app F).hom ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map ((R(d)_![ModuleCat.{u + 1}
              Λ]).map ((R(d)^![Λ]).map φ)) :=
    (rightDerivedSectionsWithSupportIso Λ d).hom.naturality φ
  have h₂ : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map ((R(b)_![ModuleCat.{u + 1}
      Λ]).map ((R(b)^![Λ]).map φ)) ≫
      ((rightDerivedSectionsWithSupportIso Λ b).app F').inv =
        ((rightDerivedSectionsWithSupportIso Λ b).app F).inv ≫
          (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).map φ :=
    (rightDerivedSectionsWithSupportIso Λ b).inv.naturality φ
  unfold supportInclusionMap
  rw [assoc, assoc, ← h₂, ← Functor.map_comp_assoc, supportedInclusion_naturality,
    Functor.map_comp_assoc, reassoc_of% h₁]

/-- The identification `supportRestrictionIso₃` of the last term of the restriction triangle is
natural in `F`. -/
theorem supportRestrictionIso₃_hom_naturality
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : F ⟶ F') :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) (pullback.snd b c.openComplement.ι)).map
        ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).map φ) ≫ (supportRestrictionIso₃ Λ b c
            F').hom =
      (supportRestrictionIso₃ Λ b c F).hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
          T).map
        ((R((c.openComplement.ι)_*[ModuleCat.{u + 1} Λ])).map
            ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).map
          ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ)))) := by
  set v := c.openComplement.ι
  set b' := pullback.snd b v
  have hpb := IsPullback.of_hasPullback b v
  have := isIso_supportedRestriction_of_isOpenImmersion Λ v b b' (pullback.fst b v) hpb F _
    (Iso.refl _)
  have := isIso_supportedRestriction_of_isOpenImmersion Λ v b b' (pullback.fst b v) hpb F' _
    (Iso.refl _)
  have hS := supportedRestriction_naturality Λ v b b' (pullback.fst b v) hpb (Iso.refl _)
    (Iso.refl _) φ ((L((v)^*[ModuleCat.{u + 1} Λ])).map φ) (by simp)
  have hS' : inv (supportedRestriction Λ v b b' (pullback.fst b v) hpb F _ (Iso.refl _)) ≫
      (L((v)^*[ModuleCat.{u + 1} Λ])).map ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ)) =
      (R(b')_![ModuleCat.{u + 1} Λ]).map ((R(b')^![Λ]).map ((L((v)^*[ModuleCat.{u + 1} Λ])).map φ))
          ≫
        inv (supportedRestriction Λ v b b' (pullback.fst b v) hpb F' _ (Iso.refl _)) := by
    rw [IsIso.inv_comp_eq, ← assoc, ← hS, assoc, IsIso.hom_inv_id, comp_id]
  have h₁ : (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b').map ((L((v)^*[ModuleCat.{u +
      1} Λ])).map φ) ≫
      ((rightDerivedSectionsWithSupportIso Λ b').app _).hom =
        ((rightDerivedSectionsWithSupportIso Λ b').app _).hom ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
            ((R(b')_![ModuleCat.{u + 1} Λ]).map ((R(b')^![Λ]).map ((L((v)^*[ModuleCat.{u + 1}
                Λ])).map φ))) :=
    (rightDerivedSectionsWithSupportIso Λ b').hom.naturality ((L((v)^*[ModuleCat.{u + 1} Λ])).map φ)
  have h₃ : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
      ((L((v)^*[ModuleCat.{u + 1} Λ])).map ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ)))
          ≫
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) v).app _).inv =
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) v).app _).inv
            ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map ((R((v)_*[ModuleCat.{u + 1}
              Λ])).map ((L((v)^*[ModuleCat.{u + 1} Λ])).map
            ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ)))) :=
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) v).inv.naturality
        _
  have hdef : ∀ (G : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      [IsIso (supportedRestriction Λ v b b' (pullback.fst b v) hpb G _ (Iso.refl _))],
      (supportRestrictionIso₃ Λ b c G).hom =
        ((rightDerivedSectionsWithSupportIso Λ b').app _).hom ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
            (inv (supportedRestriction Λ v b b' (pullback.fst b v) hpb G _ (Iso.refl _))) ≫
          ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) v).app
              _).inv :=
    fun _ _ ↦ rfl
  rw [hdef, hdef, assoc, assoc]
  rw [← h₃, ← Functor.map_comp_assoc, hS', Functor.map_comp_assoc, reassoc_of% h₁]

/-- Blueprint `proposition-purity-vector-bundles`: Restriction triangle inside a closed
support (naturality of the second map).

The restriction `RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F)` to the open complement `V` of `C`
(`AlgebraicGeometry.Etale.supportRestrictionMap`) is natural in `F`. -/
theorem supportRestrictionMap_naturality
    {F F' : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : F ⟶ F') :
    supportRestrictionMap Λ b c F ≫
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) (pullback.snd b
            c.openComplement.ι)).map
          ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).map φ) =
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).map φ ≫ supportRestrictionMap Λ b c
          F' := by
  set v := c.openComplement.ι
  have h₁ : (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).map φ ≫
      ((rightDerivedSectionsWithSupportIso Λ b).app F').hom =
        ((rightDerivedSectionsWithSupportIso Λ b).app F).hom ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map ((R(b)_![ModuleCat.{u + 1}
              Λ]).map ((R(b)^![Λ]).map φ)) :=
    (rightDerivedSectionsWithSupportIso Λ b).hom.naturality φ
  have h₂ : (R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app ((R(b)_![ModuleCat.{u +
          1} Λ]).obj ((R(b)^![Λ]).obj F')) =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app
            ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F)) ≫
          (R((v)_*[ModuleCat.{u + 1} Λ])).map ((L((v)^*[ModuleCat.{u + 1} Λ])).map
              ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ))) :=
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.naturality _
  have h₃ : (supportRestrictionIso₃ Λ b c F).inv ≫
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) (pullback.snd b v)).map
          ((L((v)^*[ModuleCat.{u + 1} Λ])).map φ) =
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map ((R((v)_*[ModuleCat.{u + 1}
            Λ])).map ((L((v)^*[ModuleCat.{u + 1} Λ])).map
          ((R(b)_![ModuleCat.{u + 1} Λ]).map ((R(b)^![Λ]).map φ)))) ≫ (supportRestrictionIso₃ Λ b c
              F').inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% (supportRestrictionIso₃_hom_naturality Λ b c φ),
      Iso.hom_inv_id, comp_id]
  have hdef : ∀ G : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      supportRestrictionMap Λ b c G = ((rightDerivedSectionsWithSupportIso Λ b).app G).hom ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app
          ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj G))) ≫ (supportRestrictionIso₃ Λ b c
              G).inv :=
    fun _ ↦ rfl
  rw [hdef, hdef, assoc, assoc, h₃,← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc,
    reassoc_of% h₁]

end Etale

end AlgebraicGeometry
