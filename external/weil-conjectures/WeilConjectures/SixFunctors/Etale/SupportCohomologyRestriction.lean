/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom

/-!
# The restriction triangle inside a closed support

Let `b : B ⟶ T` and `c : C ⟶ T` be closed immersions, `v : V ⟶ T` the open complement of `C`,
`d : D ⟶ T` a closed immersion onto `B ∩ C` and `b' : B ×_T V ⟶ V` the base change of `b`. For
a complex `F` of étale sheaves on `T` there is a distinguished triangle

`RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F) ⟶ RΓ_{B ∩ C}(T, F)[1]`.

## The argument

The derived sections with support are computed by the exceptional formalism:
`RΓ_B(T, -) ≅ RΓ(T, Rb_! Rb^! -)` (`AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIso`),
because `RΓ_B(T, -) ≅ RΓ(B, Rb^!_{sh} -)` for the derived functor of the sheaf functor `b^!`
(`AlgebraicGeometry.Etale.rightDerivedClosedUpperShriekCompIso`), which is right adjoint to
`b_* = Rb_!`, hence is `Rb^!`.

Put `E = Rb_! Rb^! F`. The supported localization triangle of `E` for the pair `(C, V)` is

`Rc_! Rc^! E ⟶ E ⟶ Rv_* Lv^* E ⟶ (Rc_! Rc^! E)[1]`,

and `Rc_! Rc^! E ≅ Rd_! Rd^! F` over `E`: both are supported on `D` and represent maps to `F`
out of objects supported on `D`. Applying `RΓ(T, -)`, the last term is
`RΓ(V, Lv^* E) ≅ RΓ(V, Rb'_! Rb'^! Lv^* F) ≅ RΓ_{B ∩ V}(V, v^* F)`, as restriction to an open
commutes with supports (`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIso`
- `AlgebraicGeometry.Etale.supportRestrictionTriangle_distinguished`
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

section UpperShriek

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The derived pushforward `Ri_!` along a closed immersion is the functor induced by the exact
functor `i_*`. -/
noncomputable def mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek :
    ((i)_*[A]).mapDerivedCategory ≅ R(i)_![A] :=
  ((i)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).symm

/-- `i_* ⊣ Ri^!_{sh}`: the derived adjunction of `i_* ⊣ i^!`. -/
noncomputable def mapDerivedCategoryLowerStarClosedUpperShriekAdjunction :
    ((i)_*[A]).mapDerivedCategory ⊣
      (closedUpperShriek A i i.openComplement.ι).rightDerivedFunctor :=
  (lowerStarClosedUpperShriekAdjunction A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).mapDerivedCategoryRightDerivedAdjunction

/-- For a closed immersion `i`, the derived lower shriek `Ri_!` is a left adjoint, with right
adjoint the derived functor of the sheaf functor `i^!` of sections supported on `Z`. -/
instance isLeftAdjoint_rightDerivedLowerShriek_of_isClosedImmersion :
    (R(i)_![A]).IsLeftAdjoint :=
  ((mapDerivedCategoryLowerStarClosedUpperShriekAdjunction A i).ofNatIsoLeft
    (mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek A i)).isLeftAdjoint

/-- For a closed immersion `i`, the exceptional inverse image `Ri^!` is the right derived functor
of the sheaf functor `i^!` of sections supported on `Z`, both being right adjoint to
`Ri_! ≅ i_*`. -/
noncomputable def rightDerivedClosedUpperShriekIso :
    (closedUpperShriek (ModuleCat.{u + 1} Λ) i i.openComplement.ι).rightDerivedFunctor ≅ R(i)^![Λ]
        :=
  ((mapDerivedCategoryLowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).ofNatIsoLeft
    (mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek (ModuleCat.{u + 1} Λ)
        i)).rightAdjointUniq
      (rightDerivedUpperShriekAdjunction Λ i)

/-- `RΓ_Z(X, K) ≅ RΓ(X, Ri_! Ri^! K)`: the derived sections with support in `Z` are the derived
global sections of the supported term of the localization triangle. -/
noncomputable def rightDerivedSectionsWithSupportIso :
    rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i ≅
      R(i)^![Λ] ⋙ R(i)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
          :=
  (rightDerivedClosedUpperShriekCompIso (ModuleCat.{u + 1} Λ) i).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedClosedUpperShriekIso Λ i) _ ≪≫
    Functor.isoWhiskerLeft _ ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u
        + 1} Λ) i).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
          i).symm _)

end UpperShriek

section Triangle

/-- `Ri^!` of a zero object is zero. -/
lemma isZero_rightDerivedUpperShriek_obj {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
 {Y : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hY : IsZero Y) : IsZero ((R(i)^![Λ]).obj Y) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((rightDerivedUpperShriekAdjunction Λ i).homEquiv _ _).symm.injective
  exact hY.eq_of_tgt _ _

variable {T B C D : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) (d : D ⟶ T)
  [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
  (hd : Set.range d.base = Set.range b.base ∩ Set.range c.base)

lemma disjoint_range_openComplement_ι_of_subset {Z Z' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T)
    [IsClosedImmersion i'] (h : Set.range i.base ⊆ Set.range i'.base) :
    Disjoint (Set.range i.base) (Set.range i'.openComplement.ι.base) := by
  refine Set.disjoint_of_subset_left h ?_
  rw [i'.range_eq_compl_range_openComplement_ι]
  exact disjoint_compl_left

omit [IsClosedImmersion c] in
include hd in
/-- The supported term of `D` is supported on `B`. -/
lemma isZero_leftDerivedUpperStar_openComplement_supported_of_inter
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((b.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(d)_![ModuleCat.{u + 1} Λ]).obj
        ((R(d)^![Λ]).obj F))) :=
  isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) d _
    (disjoint_range_openComplement_ι_of_subset d b (by rw [hd]; exact Set.inter_subset_left))
    _ subset_rfl _

/-- The map `Rd_! Rd^! F ⟶ Rb_! Rb^! F` of supported terms for `D ⊆ B`: the unique lift of the
counit of `d` through the counit of `b`. It is *defined* as `Classical.choose`. -/
noncomputable def supportedInclusion (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
    + 1} Λ))) :
    (R(d)_![ModuleCat.{u + 1} Λ]).obj ((R(d)^![Λ]).obj F) ⟶ (R(b)_![ModuleCat.{u + 1} Λ]).obj
        ((R(b)^![Λ]).obj F) :=
  (existsUnique_comp_counit_of_isZero Λ b b.openComplement.ι
    b.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_supported_of_inter Λ b c d hd F)
    ((rightDerivedUpperShriekAdjunction Λ d).counit.app F)).exists.choose

omit [IsClosedImmersion c] in
@[reassoc (attr := simp)]
lemma supportedInclusion_comp_counit (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
    + 1} Λ))) :
    supportedInclusion Λ b c d hd F ≫ (rightDerivedUpperShriekAdjunction Λ b).counit.app F =
      (rightDerivedUpperShriekAdjunction Λ d).counit.app F :=
  (existsUnique_comp_counit_of_isZero Λ b b.openComplement.ι
    b.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_supported_of_inter Λ b c d hd F)
    ((rightDerivedUpperShriekAdjunction Λ d).counit.app F)).exists.choose_spec

include hd in
/-- `Rc_! Rc^! (Rb_! Rb^! F)` is supported on `D = B ∩ C`: on the open complement `W` of `D`,
it vanishes on the complement of `C` and, restriction to an open commuting with supports, on the
complement of `B`; these two opens cover `W`. -/
lemma isZero_leftDerivedUpperStar_openComplement_supported_supported
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((d.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(c)_![ModuleCat.{u + 1} Λ]).obj
        ((R(c)^![Λ]).obj
      ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F))))) := by
  set ud := d.openComplement.ι
  have hcd : Disjoint (Set.range (pullback.snd c ud).base)
      (Set.range (pullback.snd b ud).base) := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, Set.disjoint_left]
    intro x hx₁ hx₂
    have : ud.base x ∈ Set.range d.base := by rw [hd]; exact ⟨hx₂, hx₁⟩
    exact Set.disjoint_left.mp (disjoint_range_openComplement_ι_of_subset d d subset_rfl) this
      ⟨x, rfl⟩
  refine isZero_of_isZero_leftDerivedUpperStar_of_disjoint Λ (pullback.snd c ud)
    (pullback.snd b ud) _ _ (Scheme.Hom.range_eq_compl_range_openComplement_ι _)
    (Scheme.Hom.range_eq_compl_range_openComplement_ι _) hcd ?_ ?_
  · exact (isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) c ud _).of_iso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ ud).app _).symm
  · set o := (pullback.snd b ud).openComplement.ι ≫ ud
    have hE : IsZero ((L((o)^*[ModuleCat.{u + 1} Λ])).obj ((R(b)_![ModuleCat.{u + 1} Λ]).obj
        ((R(b)^![Λ]).obj F))) :=
      isZero_leftDerivedUpperStar_openComplement_comp_obj_rightDerivedLowerShriek
        (ModuleCat.{u + 1} Λ) b ud _
    have := isIso_supportedRestriction_of_isOpenImmersion Λ o c (pullback.snd c o)
      (pullback.fst c o) (IsPullback.of_hasPullback c o)
      ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F)) _ (Iso.refl _)
    refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) _ ud).app _).symm
    exact ((R(pullback.snd c o)_![ModuleCat.{u + 1} Λ]).map_isZero
      (isZero_rightDerivedUpperShriek_obj Λ _ hE)).of_iso (asIso (supportedRestriction Λ o c
        (pullback.snd c o) (pullback.fst c o) (IsPullback.of_hasPullback c o) _ _
          (Iso.refl _)))

/-- `Rd_! Rd^! F ≅ Rc_! Rc^! (Rb_! Rb^! F)` over `Rb_! Rb^! F`: both are supported on `D` and
the maps to `F` lift uniquely. -/
theorem exists_iso_supported_supported (F : DerivedCategory (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))) :
    ∃ e : (R(d)_![ModuleCat.{u + 1} Λ]).obj ((R(d)^![Λ]).obj F) ≅
        (R(c)_![ModuleCat.{u + 1} Λ]).obj ((R(c)^![Λ]).obj ((R(b)_![ModuleCat.{u + 1} Λ]).obj
            ((R(b)^![Λ]).obj F))),
      e.hom ≫ (rightDerivedUpperShriekAdjunction Λ c).counit.app _ =
        supportedInclusion Λ b c d hd F := by
  set E := (R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F)
  set εb := (rightDerivedUpperShriekAdjunction Λ b).counit.app F
  set εc := (rightDerivedUpperShriekAdjunction Λ c).counit.app E
  set εd := (rightDerivedUpperShriekAdjunction Λ d).counit.app F
  have hDC : IsZero ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(d)_![ModuleCat.{u + 1}
      Λ]).obj ((R(d)^![Λ]).obj F))) :=
    isZero_leftDerivedUpperStar_openComplement_supported_of_inter Λ c b d
      (hd.trans (Set.inter_comm _ _)) F
  have hX := isZero_leftDerivedUpperStar_openComplement_supported_supported Λ b c d hd F
  have hXc : IsZero ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(c)_![ModuleCat.{u + 1}
      Λ]).obj ((R(c)^![Λ]).obj E))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) c _
      (disjoint_range_openComplement_ι_of_subset c c subset_rfl) _ subset_rfl _
  have hXb : IsZero ((L((b.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(c)_![ModuleCat.{u + 1}
      Λ]).obj ((R(c)^![Λ]).obj E))) := by
    have hE : IsZero ((L((b.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj E) :=
      isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) b _
        (disjoint_range_openComplement_ι_of_subset b b subset_rfl) _ subset_rfl _
    set o := b.openComplement.ι
    have := isIso_supportedRestriction_of_isOpenImmersion Λ o c (pullback.snd c o)
      (pullback.fst c o) (IsPullback.of_hasPullback c o) E _ (Iso.refl _)
    exact ((R(pullback.snd c o)_![ModuleCat.{u + 1} Λ]).map_isZero
      (isZero_rightDerivedUpperShriek_obj Λ _ hE)).of_iso (asIso (supportedRestriction Λ o c
        (pullback.snd c o) (pullback.fst c o) (IsPullback.of_hasPullback c o) _ _ (Iso.refl _)))
  have hDd : IsZero ((L((d.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(d)_![ModuleCat.{u + 1}
      Λ]).obj ((R(d)^![Λ]).obj F))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) d _
      (disjoint_range_openComplement_ι_of_subset d d subset_rfl) _ subset_rfl _
  obtain ⟨ψ, hψ, -⟩ := existsUnique_comp_counit_of_isZero Λ c c.openComplement.ι
    c.range_eq_compl_range_openComplement_ι hDC (supportedInclusion Λ b c d hd F)
  obtain ⟨φ, hφ, -⟩ := existsUnique_comp_counit_of_isZero Λ d d.openComplement.ι
    d.range_eq_compl_range_openComplement_ι hX (εc ≫ εb)
  have h₁ : ψ ≫ φ = 𝟙 _ :=
    (existsUnique_comp_counit_of_isZero Λ d d.openComplement.ι
      d.range_eq_compl_range_openComplement_ι hDd εd).unique
      (by rw [assoc, hφ, reassoc_of% hψ, supportedInclusion_comp_counit]) (id_comp _)
  have h₂ : φ ≫ supportedInclusion Λ b c d hd F = εc :=
    (existsUnique_comp_counit_of_isZero Λ b b.openComplement.ι
      b.range_eq_compl_range_openComplement_ι hXb (εc ≫ εb)).unique
      (by rw [assoc]; erw [supportedInclusion_comp_counit]; exact hφ) rfl
  have h₃ : φ ≫ ψ = 𝟙 _ :=
    (existsUnique_comp_counit_of_isZero Λ c c.openComplement.ι
      c.range_eq_compl_range_openComplement_ι hXc εc).unique
      (by rw [assoc]; erw [hψ]; exact h₂) (id_comp _)
  exact ⟨⟨ψ, φ, h₁, h₃⟩, hψ⟩

/-- The triangle `Rd_! Rd^! F ⟶ Rb_! Rb^! F ⟶ Rv_* Lv^* (Rb_! Rb^! F) ⟶ [1]` is distinguished: it
is the supported localization triangle of `Rb_! Rb^! F` for the pair `(C, V)`, its first term
being identified with `Rd_! Rd^! F` (`AlgebraicGeometry.Etale.exists_iso_supported_supported`). -/
theorem exists_distTriang_supportedInclusion
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ δ, Triangle.mk (supportedInclusion Λ b c d hd F)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.openComplement.ι).unit.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F))) δ ∈ distTriang _ := by
  obtain ⟨e, he⟩ := exists_iso_supported_supported Λ b c d hd F
  have hT := supportedLocalizationTriangle_mem_distTriang Λ c c.openComplement.ι
    c.range_eq_compl_range_openComplement_ι ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F))
  refine ⟨supportedLocalizationBoundary Λ c c.openComplement.ι
    c.range_eq_compl_range_openComplement_ι ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F))
        ≫
      (e.inv)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simp [he]
  · simp
  · simp [← Functor.map_comp]

instance (X : Scheme.{u}) : (rightDerivedGlobalSections A X).IsTriangulated :=
  inferInstanceAs ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.IsTriangulated)

/-- The identification of the last term: for `E = Rb_! Rb^! F`,
`RΓ_{B ∩ V}(V, Lv^* F) ≅ RΓ(V, Rb'_! Rb'^! Lv^* F) ≅ RΓ(V, Lv^* E) ≅ RΓ(T, Rv_* Lv^* E)`. -/
noncomputable def supportRestrictionIso₃ (F : DerivedCategory (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))) :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) (pullback.snd b c.openComplement.ι)).obj
        ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj F) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj
          ((R((c.openComplement.ι)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj ((R(b)_![ModuleCat.{u + 1} Λ]).obj
            ((R(b)^![Λ]).obj F)))) :=
  haveI := isIso_supportedRestriction_of_isOpenImmersion Λ c.openComplement.ι b
    (pullback.snd b c.openComplement.ι) (pullback.fst b c.openComplement.ι)
    (IsPullback.of_hasPullback b c.openComplement.ι) F _ (Iso.refl _)
  (rightDerivedSectionsWithSupportIso Λ (pullback.snd b c.openComplement.ι)).app _ ≪≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).mapIso (asIso (supportedRestriction Λ
        c.openComplement.ι b
      (pullback.snd b c.openComplement.ι) (pullback.fst b c.openComplement.ι)
      (IsPullback.of_hasPullback b c.openComplement.ι) F _ (Iso.refl _))).symm ≪≫
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ)
        c.openComplement.ι).app _).symm

/-- The inclusion of supports `RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F)`, through
`RΓ_Z(T, -) ≅ RΓ(T, Rz_! Rz^! -)`. -/
noncomputable def supportInclusionMap (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
    + 1} Λ))) :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) d).obj F ⟶
        (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).obj F :=
  ((rightDerivedSectionsWithSupportIso Λ d).app F).hom ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map (supportedInclusion Λ b c d hd F) ≫
      ((rightDerivedSectionsWithSupportIso Λ b).app F).inv

/-- The restriction `RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F)` to the open complement `V` of `C`,
induced by the unit `E ⟶ Rv_* Lv^* E` for `E = Rb_! Rb^! F`. -/
noncomputable def supportRestrictionMap (F : DerivedCategory (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))) :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) b).obj F ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) (pullback.snd b
          c.openComplement.ι)).obj
        ((L((c.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj F) :=
  ((rightDerivedSectionsWithSupportIso Λ b).app F).hom ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.openComplement.ι).unit.app _) ≫
    (supportRestrictionIso₃ Λ b c F).inv

/-- Blueprint `proposition-purity-vector-bundles`: Restriction triangle inside a closed
support

Let `b : B ⟶ T`, `c : C ⟶ T` be closed immersions, `v : V ⟶ T` the open complement of `C`, and
`d : D ⟶ T` a closed immersion onto `B ∩ C`; `B ∩ V` is the closed subscheme `B ×_T V` of `V`.
For every complex `F` of étale sheaves on `T` there is a distinguished triangle

`RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F) ⟶ RΓ_{B ∩ C}(T, F)[1]`

in `D(Λ)`, where `RΓ_Z` is the derived functor of the sections supported on `Z`
(`AlgebraicGeometry.Etale.rightDerivedSectionsWithSupport`). The first map is induced by the
inclusion of supports and the second by the restriction to `V`
(`AlgebraicGeometry.Etale.supportInclusionMap`, `AlgebraicGeometry.Etale.supportRestrictionMap`).
-/
theorem exists_distTriang_supportRestriction
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ δ, Triangle.mk (supportInclusionMap Λ b c d hd F) (supportRestrictionMap Λ b c F) δ ∈
      distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_supportedInclusion Λ b c d hd F
  set G := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T
  let e₁ := (rightDerivedSectionsWithSupportIso Λ d).app F
  let e₂ := (rightDerivedSectionsWithSupportIso Λ b).app F
  let e₃ := supportRestrictionIso₃ Λ b c F
  refine ⟨e₃.hom ≫ (G.mapTriangle.obj (Triangle.mk (supportedInclusion Λ b c d hd F)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.openComplement.ι).unit.app
        ((R(b)_![ModuleCat.{u + 1} Λ]).obj ((R(b)^![Λ]).obj F))) δ)).mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ (G.map_distinguished _ hδ) _
      (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)⟩
  · simp [supportInclusionMap, e₁, e₂]
    rfl
  · simp [supportRestrictionMap, e₂, e₃]
    rfl
  · simp only [Triangle.mk_mor₃, assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, comp_id]

end Triangle

end Etale

end AlgebraicGeometry
