/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Stability of `Dctf`: closed immersions and finite open covers

This file bounds the exceptional inverse image `Ri^!` along a closed immersion through the
direct image along the open complement, and shows that membership in `D_c^[a, b]` with Tor
amplitude in `[a, b]` can be checked on a finite open cover.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Closed immersions: reduction to the open complement -/

section ClosedImmersion

open Pretriangulated

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

/-- For a closed immersion `i`, restricting an extension by zero recovers the complement:
`D(i^*) (Ri_! Q) ≅ Q`, since `Ri_! = Ri_* = D(i_*)` and `i^* i_* ≅ 𝟭`. -/
noncomputable def mapDerivedCategoryUpperStarRightDerivedLowerShriekIso {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    R(i)_![A] ⋙ D((i)^*[A]) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar A i ≪≫
    Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (FC := FC) A i) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (Etale.upperStarLowerStarAdjunction A i).counit) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [HasSmallSiteSheafify A] [PreservesFiniteLimits (CategoryTheory.forget A)] in
/-- Extension by zero along a closed immersion `i` preserves Tor amplitude: if the projection
formula holds for `i` at `P` and `P` has Tor amplitude in `[a, b]`, so does `Ri_! P`, since
`Ri_! P ⊗ᴸ G ≅ Ri_!(P ⊗ᴸ i^* G)` and `Ri_! = D(i_*)` is exact. -/
lemma torAmplitudeIn_rightDerivedLowerShriek_of_isClosedImmersion [UpperStarPreservesFlat A]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    {a b : ℤ} {P : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    (hPF : ∀ L, HasProjectionFormula A i P L) (hP : torAmplitudeIn A Z a b P) :
    torAmplitudeIn A T a b ((R(i)_![A]).obj P) := fun G ↦ by
  have : IsIso (((projectionMap A i).app P).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) :=
    hPF ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  -- `Ri_! (P ⊗ᴸ i^* G) ≅ Ri_! P ⊗ᴸ G` by the projection formula
  let e : (R(i)_![A]).obj (((-⊗ᴸ-(Z)[A]).obj P).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)^*[A].obj G))) ≅
        ((-⊗ᴸ-(T)[A]).obj ((R(i)_![A]).obj P)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G) :=
    (R(i)_![A]).mapIso (((-⊗ᴸ-(Z)[A]).obj P).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso A i).app G).symm) ≪≫
      (asIso (((projectionMap A i).app P).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))).symm
  -- `Ri_! ≅ D(i_*)` is exact
  let e' := (rightDerivedLowerShriekIsoRightDerivedLowerStar A i ≪≫
    Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (FC := FC) A i).app
      (((-⊗ᴸ-(Z)[A]).obj P).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)^*[A].obj G)))
  obtain ⟨h₁, h₂⟩ :=
    ((i)_*[A]).homologyConcentratedIn_mapDerivedCategory_obj (hP ((i)^*[A].obj G))
  have : _root_.DerivedCategory.TStructure.t.IsGE (D((i)_*[A]).obj (((-⊗ᴸ-(Z)[A]).obj P).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)^*[A].obj G)))) a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE (D((i)_*[A]).obj (((-⊗ᴸ-(Z)[A]).obj P).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)^*[A].obj G)))) b := h₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso (e'.symm ≪≫ e) a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso (e'.symm ≪≫ e) b⟩

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is invariant under isomorphism. -/
lemma homologyConcentratedIn_of_iso {X : Scheme.{u}} {a b : ℤ}
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : K ≅ K')
    (h : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a b K' := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e b⟩

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₂` concentrated in `[a, b]` and
`X₃` in `[a, e]`, `b ≤ e`, the first term is concentrated in `[a, e + 1]`. -/
lemma homologyConcentratedIn_obj₁ {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e)
    (h₂ : _root_.DerivedCategory.homologyConcentratedIn a b T.obj₂)
    (h₃ : _root_.DerivedCategory.homologyConcentratedIn a e T.obj₃) :
    _root_.DerivedCategory.homologyConcentratedIn a (e + 1) T.obj₁ := by
  have hT' := inv_rot_of_distTriang T hT
  obtain ⟨g₂, l₂⟩ := h₂
  obtain ⟨g₃, l₃⟩ := h₃
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₁ (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift T.obj₃ a (-1) (a + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₁ (e + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift T.obj₃ e (-1) (e + 1)
  have : _root_.DerivedCategory.TStructure.t.IsLE T.invRotate.obj₃ b := l₂
  have : _root_.DerivedCategory.TStructure.t.IsGE T.invRotate.obj₃ a := g₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT' a
      (_root_.DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1)) ‹_›,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT' (e + 1) ‹_›
      (_root_.DerivedCategory.TStructure.t.isLE_of_le _ b (e + 1))⟩


omit [HasSmallSiteSheafify A] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` with `X₂` of Tor amplitude in `[a, b]`
and `X₃` of Tor amplitude in `[a, e]`, `b ≤ e`, the first term has Tor amplitude in
`[a, e + 1]`. -/
lemma torAmplitudeIn_obj₁ {X : Scheme.{u}}
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) {a b e : ℤ} (hbe : b ≤ e)
    (h₂ : torAmplitudeIn A X a b T.obj₂) (h₃ : torAmplitudeIn A X a e T.obj₃) :
    torAmplitudeIn A X a (e + 1) T.obj₁ := fun F ↦ by
  let G := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  let := _root_.DerivedCategory.commShiftTensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
  have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
    (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
  exact homologyConcentratedIn_obj₁ A _ (G.map_distinguished _ hT) hbe (h₂ F) (h₃ F)
/-- **The exceptional inverse image along a closed immersion, from the open complement.**
Let `i : Z ⟶ T` be a closed immersion with open complement `j`. If `K` lies in `D_c^[a, b]` with
Tor amplitude in `[a, b]`, and `Rj_* j^* K` in `D_c^[a, e]` with Tor amplitude in `[a, e]`,
`b ≤ e`, then `Ri^! K` lies in `D_c^[a, e + 1]` with Tor amplitude in `[a, e + 1]`: the
localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` bounds `Ri_! Ri^! K`, and for the Tor
amplitude the projection formula identifies `Ri_!(Ri^! K ⊗ᴸ G)` with `Ri_! Ri^! K ⊗ᴸ i_* G`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar
    [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)] {Z T U : Scheme.{u}}
    [(Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) T).IsClosedUnderKernels]
    [(Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) T).IsClosedUnderCokernels]
    [(Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) T).IsClosedUnderExtensions]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u +
        1} Λ))]
    (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    (j : U ⟶ T) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {a b e : ℤ} (hbe : b ≤ e) {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u
        + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K)
    (hM : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a e ((R((j)_*[ModuleCat.{u + 1}
        Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (hPF : ∀ L, HasProjectionFormula (ModuleCat.{u + 1} Λ) i ((R(i)^![Λ]).obj K) L) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (e + 1) ((R(i)^![Λ]).obj K) := by
  obtain ⟨⟨hKbc, hKc⟩, hKt⟩ := hK
  obtain ⟨⟨hMbc, hMc⟩, hMt⟩ := hM
  have hT := supportedLocalizationTriangle_mem_distTriang Λ i j hij K
  set N := (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K)
  -- `N` is bounded constructible
  have hNbc : boundedConstructible (ModuleCat.{u + 1} Λ) T N :=
    (boundedConstructible (ModuleCat.{u + 1} Λ) T).ext_of_isTriangulatedClosed₂ _
        (inv_rot_of_distTriang _ hT)
      ((boundedConstructible (ModuleCat.{u + 1} Λ) T).le_shift (-1) _ hMbc) hKbc
  -- `N` lies in `[a, e + 1]` with Tor amplitude in `[a, e + 1]`
  have hNc := homologyConcentratedIn_obj₁ (ModuleCat.{u + 1} Λ) _ hT hbe hKc hMc
  have hNt : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a (e + 1) N :=
    torAmplitudeIn_obj₁ (ModuleCat.{u + 1} Λ) _ hT hbe hKt hMt
  -- `Ri^! K ≅ i^* N`
  let ε := mapDerivedCategoryUpperStarRightDerivedLowerShriekIso (ModuleCat.{u + 1} Λ) i
  refine ⟨⟨(boundedConstructible (ModuleCat.{u + 1} Λ) Z).prop_of_iso (ε.app _)
      (hNbc.mapDerivedCategory_upperStar i),
    homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ) (ε.app _)
      (((i)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hNc)⟩, fun G ↦ ?_⟩
  -- `i_! (Ri^! K ⊗ᴸ G) ≅ N ⊗ᴸ i_* G` by the projection formula
  have : IsIso (((projectionMap (ModuleCat.{u + 1} Λ) i).app ((R(i)^![Λ]).obj K)).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj G))) :=
    hPF ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj G))
  let e₁ : (L((i)^*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((i)_*[ModuleCat.{u + 1} Λ].obj G)) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) i).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((asIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit).app G)
  let e₂ : (R(i)_![ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj
      K)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅
        ((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj N).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((i)_*[ModuleCat.{u + 1} Λ].obj G)) :=
    (R(i)_![ModuleCat.{u + 1} Λ]).mapIso (((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₁.symm) ≪≫
      (asIso (((projectionMap (ModuleCat.{u + 1} Λ) i).app ((R(i)^![Λ]).obj K)).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj G)))).symm
  exact homologyConcentratedIn_of_iso (ModuleCat.{u + 1} Λ) ((ε.app _).symm ≪≫ (D((i)^*[ModuleCat.{u
      + 1} Λ])).mapIso e₂).symm
    (((i)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj (hNt _))

end ClosedImmersion

/-! ### Gluing over a finite open cover -/

section Gluing

open ZeroObject

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- A homology sheaf vanishes if it vanishes after restriction to the members of an open
cover. -/
lemma isZero_homology_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ)
    (h : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (D(((U i).ι)^*[A]).obj R))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective A
    (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
    (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
    (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
      isIso_of_source_target_iso_zero _ ((h i.down).of_iso
        ((((U i.down).ι)^*[A].mapDerivedCategoryHomologyFunctorIso q).app R)).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso
    (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
/-- Concentration in `[a, b]` is local for an open cover. -/
lemma homologyConcentratedIn_of_openCover {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, _root_.DerivedCategory.homologyConcentratedIn a b (D(((U i).ι)^*[A]).obj R)) :
    _root_.DerivedCategory.homologyConcentratedIn a b R :=
  ⟨(_root_.DerivedCategory.isGE_iff R a).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isGE_iff _ a).1 (h i).1 q hq,
    (_root_.DerivedCategory.isLE_iff R b).2 fun q hq ↦ isZero_homology_of_openCover A U hU R q
      fun i ↦ (_root_.DerivedCategory.isLE_iff _ b).1 (h i).2 q hq⟩

omit [HasSmallSiteSheafify A] in
/-- Tor amplitude in `[a, b]` is local for an open cover. -/
lemma torAmplitudeIn_of_openCover [UpperStarPreservesFlat A] {X : Scheme.{u}}
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {a b : ℤ}
    (h : ∀ i, torAmplitudeIn A (U i) a b (D(((U i).ι)^*[A]).obj R)) :
    torAmplitudeIn A X a b R := fun G ↦ by
  refine homologyConcentratedIn_of_openCover A U hU _ fun i ↦ ?_
  let j := (U i).ι
  let e : D((j)^*[A]).obj (R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj G) ≅
      D((j)^*[A]).obj R ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj ((j)^*[A].obj G) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).app _).symm ≪≫
      leftDerivedUpperStarTensorIso A j _ _ ≪≫
      tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory A j).app R)
        ((singleFunctorCompLeftDerivedUpperStarIso A j).app G)
  obtain ⟨h₁, h₂⟩ := h i ((j)^*[A].obj G)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

end Gluing

end Etale

end AlgebraicGeometry
