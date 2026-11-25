/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Defs

/-!
# Generic constructibility of a direct image, on the bounded below derived categories

The property `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn` of Deligne's
generic constructibility theorem is phrased on the unbounded derived categories, for a sheaf
placed in degree `0`. Here it is extended to every bounded below complex `K` and rephrased on the
bounded below derived categories, where the base change theorems and the pasting laws for the
derived base change map are available
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus`). The two agree for a sheaf placed in
degree `0` (`AlgebraicGeometry.Etale.hasConstructibleDirectImageBaseChangeOn_iff`), by the
comparison `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_ι_obj_iff` of the two derived
base change maps.

The property of `K` is stable under isomorphisms, shifts and extensions, so it holds for every
bounded complex whose cohomology sheaves have it
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_bounded`). This is the dévissage
along the truncation triangles of the third step of the proof of
`theorem-generic-constructibility-base-change-rj`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Over a subset `U` of `S`, the derived direct image of the bounded below complex `K` along
`j : X ⟶ Y`, for `Y` over `S` via `fY`, is bounded constructible and its formation commutes with
every base change from a noetherian scheme: for every noetherian `T`, every `t : T ⟶ S` with
image in `U` and all cartesian squares

```
  X_T --g'--> X
   |          |
  j_T         j
   ↓          ↓
  Y_T --g---> Y
   |          |
  f_T         fY
   ↓          ↓
   T ---t---> S
```

the direct image `Rj_{T,*}(g'^* K)` is bounded constructible and the derived base change map
`g^* Rj_* K ⟶ Rj_{T,*} g'^* K` on the bounded below derived categories is an isomorphism. For a
sheaf placed in degree `0` this is `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn`
(`AlgebraicGeometry.Etale.hasConstructibleDirectImageBaseChangeOn_iff`). -/
def HasDirectImageBaseChangeOnPlus {S X Y : Scheme.{u}} (fY : Y ⟶ S) (j : X ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (U : Set S) : Prop :=
  ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ S), Set.range t ⊆ U →
    ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (fT : YT ⟶ T) (g' : XT ⟶ X) (jT : XT ⟶ YT),
      IsPullback g fT fY t → ∀ sq : IsPullback g' jT j g,
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          (_root_.DerivedCategory.Plus.ι.obj
            ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
            (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K))) ∧
        IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)

variable {Λ}

/-- The property is inherited by every smaller subset of the base. -/
lemma HasDirectImageBaseChangeOnPlus.mono {S X Y : Scheme.{u}} {fY : Y ⟶ S} {j : X ⟶ Y}
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U V : Set S} (h : HasDirectImageBaseChangeOnPlus Λ fY j K U) (hVU : V ⊆ U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K V :=
  fun T _ t ht ↦ h T t (ht.trans hVU)

/-- The property `AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn` of a sheaf is
the property `AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus` of the sheaf placed in
degree `0`. -/
theorem hasConstructibleDirectImageBaseChangeOn_iff {S X Y : Scheme.{u}} (fY : Y ⟶ S)
    (j : X ⟶ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Set S) :
    HasConstructibleDirectImageBaseChangeOn Λ fY j F U ↔
      HasDirectImageBaseChangeOnPlus Λ fY j
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U := by
  have key : ∀ (YT XT : Scheme.{u}) (g : YT ⟶ Y) (g' : XT ⟶ X) (jT : XT ⟶ YT)
      (sq : IsPullback g' jT j g),
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          ((R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ↔
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) YT
          (_root_.DerivedCategory.Plus.ι.obj
            ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
            (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
              ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ∧
        IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
    intro YT XT g g' jT sq
    let Z := (_root_.DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) 0).obj F
    let e : (R((jT)_*[ModuleCat.{u + 1} Λ])).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≅
        _root_.DerivedCategory.Plus.ι.obj ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
          (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Z)) :=
      (R((jT)_*[ModuleCat.{u + 1} Λ])).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ g').app
            (_root_.DerivedCategory.Plus.ι.obj Z)) ≪≫
        ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app
          (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Z)).symm
    refine and_congr ⟨fun h ↦ ObjectProperty.prop_of_iso _ e h,
      fun h ↦ ObjectProperty.prop_of_iso _ e.symm h⟩ ?_
    exact isIso_derivedBaseChangeMap_app_ι_obj_iff _ sq.toCommSq Z
  exact forall_congr' fun T ↦ forall_congr' fun _ ↦ forall_congr' fun t ↦ forall_congr' fun _ ↦
    forall_congr' fun YT ↦ forall_congr' fun XT ↦ forall_congr' fun g ↦ forall_congr' fun _ ↦
      forall_congr' fun g' ↦ forall_congr' fun jT ↦ forall_congr' fun _ ↦
        forall_congr' fun sq ↦ key YT XT g g' jT sq

section Closure

variable {S X Y : Scheme.{u}} {fY : Y ⟶ S} {j : X ⟶ Y} {U : Set S}

/-- The property is invariant under isomorphisms of complexes. -/
lemma HasDirectImageBaseChangeOnPlus.of_iso
    {K K' : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') (h : HasDirectImageBaseChangeOnPlus Λ fY j K U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K' U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨h₁, h₂⟩ := h T t ht YT XT g fT g' jT hY sq
  exact ⟨ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
      ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
        (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.mapIso e))) h₁,
    (NatTrans.isIso_app_iff_of_iso _ e).1 h₂⟩

/-- The property of a complex only depends on its isomorphism class. -/
lemma hasDirectImageBaseChangeOnPlus_iff_of_iso
    {K K' : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') :
    HasDirectImageBaseChangeOnPlus Λ fY j K U ↔ HasDirectImageBaseChangeOnPlus Λ fY j K' U :=
  ⟨.of_iso e, .of_iso e.symm⟩

/-- The property holds for a zero object. -/
lemma HasDirectImageBaseChangeOnPlus.of_isZero
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero K) : HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  let Φ := ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus
  have h₁ : IsZero (Φ.obj K) := Φ.map_isZero hK
  have h₂ : IsZero ((((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus).obj
      ((j)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K)) :=
    Functor.map_isZero _ (Functor.map_isZero _ hK)
  exact ⟨boundedConstructible_of_isZero Λ (_root_.DerivedCategory.Plus.ι.map_isZero h₁),
    ⟨⟨h₁.to_ _, h₂.eq_of_src _ _, h₁.eq_of_src _ _⟩⟩⟩

variable [Finite Λ]

/-- The property is stable under the shifts. -/
lemma HasDirectImageBaseChangeOnPlus.shift
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : HasDirectImageBaseChangeOnPlus Λ fY j K U) (n : ℤ) :
    HasDirectImageBaseChangeOnPlus Λ fY j (K⟦n⟧) U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨h₁, h₂⟩ := h T t ht YT XT g fT g' jT hY sq
  let Φ := ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι
  refine ⟨ObjectProperty.prop_of_iso _ ((Φ.commShiftIso n).app K).symm
    (ObjectProperty.le_shift _ n _ h₁), ?_⟩
  exact (_root_.DerivedCategory.Plus.isIso_app_shift_iff _ K n).2 h₂

/-- **Two out of three** for the property: if it holds for the first and the third term of a
distinguished triangle, it holds for the second. -/
lemma HasDirectImageBaseChangeOnPlus.of_distTriang₂
    {Tr : Triangle (_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))} (hTr : Tr ∈ distTriang _)
    (h₁ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₁ U)
    (h₃ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₃ U) :
    HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₂ U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨c₁, i₁⟩ := h₁ T t ht YT XT g fT g' jT hY sq
  obtain ⟨c₃, i₃⟩ := h₃ T t ht YT XT g fT g' jT hY sq
  let Φ := ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι
  exact ⟨ObjectProperty.ext_of_isTriangulatedClosed₂ _ _ (Φ.map_distinguished _ hTr) c₁ c₃,
    NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ _ hTr i₁ i₃⟩

/-- **Two out of three** for the property: if it holds for the first and the second term of a
distinguished triangle, it holds for the third. -/
lemma HasDirectImageBaseChangeOnPlus.of_distTriang₃
    {Tr : Triangle (_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))} (hTr : Tr ∈ distTriang _)
    (h₁ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₁ U)
    (h₂ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₂ U) :
    HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₃ U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨c₁, i₁⟩ := h₁ T t ht YT XT g fT g' jT hY sq
  obtain ⟨c₂, i₂⟩ := h₂ T t ht YT XT g fT g' jT hY sq
  let Φ := ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι
  exact ⟨ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ (Φ.map_distinguished _ hTr) c₁ c₂,
    NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ _ hTr i₁ i₂⟩

/-- **Two out of three** for the property: if it holds for the second and the third term of a
distinguished triangle, it holds for the first. -/
lemma HasDirectImageBaseChangeOnPlus.of_distTriang₁
    {Tr : Triangle (_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))} (hTr : Tr ∈ distTriang _)
    (h₂ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₂ U)
    (h₃ : HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₃ U) :
    HasDirectImageBaseChangeOnPlus Λ fY j Tr.obj₁ U := by
  intro T _ t ht YT XT g fT g' jT hY sq
  obtain ⟨c₂, i₂⟩ := h₂ T t ht YT XT g fT g' jT hY sq
  obtain ⟨c₃, i₃⟩ := h₃ T t ht YT XT g fT g' jT hY sq
  let Φ := ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
    (jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι
  exact ⟨ObjectProperty.ext_of_isTriangulatedClosed₁ _ _ (Φ.map_distinguished _ hTr) c₂ c₃,
    NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃ _ hTr i₂ i₃⟩

open _root_.DerivedCategory.Plus in
/-- **Dévissage for the property**: if it holds for each cohomology sheaf of a complex `K` with
cohomology in `[a, a + n - 1]`, placed in degree `0`, then it holds for `K`. The induction runs
along the truncation triangles `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶`. -/
lemma HasDirectImageBaseChangeOnPlus.of_isGE_of_isLE (n : ℕ) :
    ∀ (a : ℤ) (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → HasDirectImageBaseChangeOnPlus Λ fY j
        ((singleFunctor _ 0).obj ((homologyFunctor _ q).obj K)) U) →
      HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  induction n with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact .of_isZero (TStructure.t.isZero K (a - 1) a (by lia))
  | succ n ih =>
    intro a K _ _ hK
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b K
    have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(n + 1) - 1) _ (by lia)
    have : ((TStructure.t.triangleLTGE b).obj K).obj₃.IsLE b :=
      inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : ((TStructure.t.triangleLTGE b).obj K).obj₃.IsGE b :=
      inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj K).obj₃ b
    have := isIso_homologyFunctor_map_truncGEπ_app K b b le_rfl
    let eG : (homologyFunctor _ b).obj K ≅ G :=
      asIso ((homologyFunctor _ b).map ((TStructure.t.truncGEπ b).app K)) ≪≫
        (homologyFunctor _ b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso b).app G
    have h₀ : HasDirectImageBaseChangeOnPlus Λ fY j ((singleFunctor _ 0).obj G) U :=
      .of_iso ((singleFunctor _ 0).mapIso eG) (hK b (by lia) (by lia))
    have h₃ : HasDirectImageBaseChangeOnPlus Λ fY j ((TStructure.t.triangleLTGE b).obj K).obj₃ U :=
      .of_iso (((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G ≪≫ e.symm) (h₀.shift (-b))
    have h₁ : HasDirectImageBaseChangeOnPlus Λ fY j
        ((TStructure.t.triangleLTGE b).obj K).obj₁ U := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have := isIso_homologyFunctor_map_truncLTι_app K b q (by lia)
        exact .of_iso ((singleFunctor _ 0).mapIso
          (asIso ((homologyFunctor _ q).map ((TStructure.t.truncLTι b).app K))).symm)
          (hK q hq (by lia))
    exact .of_distTriang₂ hT h₁ h₃

open _root_.DerivedCategory.Plus in
/-- **Dévissage for the property**: if it holds for each cohomology sheaf of a bounded complex
`K`, placed in degree `0`, then it holds for `K`. -/
lemma HasDirectImageBaseChangeOnPlus.of_bounded
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ q, HasDirectImageBaseChangeOnPlus Λ fY j
      ((singleFunctor _ 0).obj ((homologyFunctor _ q).obj K)) U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U :=
  have : K.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le K b _ (by lia)
  .of_isGE_of_isLE (b - a + 1).toNat a K inferInstance this fun q _ _ ↦ hK q

end Closure

end Etale

end AlgebraicGeometry
