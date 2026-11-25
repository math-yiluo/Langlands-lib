/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Stability of `Dctf`: finite coefficients and open immersions

For a finite coefficient ring `Λ`, this file shows that the derived tensor product and the
extension by zero `Rj_!` along an open immersion preserve `Dctf`, computes `Rj_!` and `Rj^!`
along an open immersion, constructs the descended functors `Lf^*` and `𝔻_X` between the
categories `Dctf`, and records how tensoring with a shifted flat object moves the intervals.

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

/-! ### The derived tensor product at a finite coefficient ring -/

section Tensor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `proposition-six-operations-dctf--14`: Tor sheaves of constructible sheaves.

For a finite ring `Λ` and constructible sheaves `F` and `G` of `Λ`-modules on `X_ét`, every
homology sheaf of `F ⊗ᴸ G` is constructible: on a common stratification both are locally
constant, and on a cover where both are constant `Hʳ(F ⊗ᴸ G)` is the constant sheaf
`Tor_{-r}(M, N)` of finite modules. -/
theorem isConstructibleSheaf_homology_tensor_singleFunctor {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] [IsConstructibleSheaf G] (r : ℤ) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) :=
  isConstructibleSheaf_torSheaf Λ F G r

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (ii), constructibility: for a finite ring `Λ`, the derived tensor product of two
bounded constructible complexes, one of them of finite Tor amplitude, is bounded constructible.
Finite Tor amplitude of one factor is needed for boundedness: over `ℤ/ℓ²` on a point,
`ℤ/ℓ ⊗ᴸ ℤ/ℓ` has a nonzero `Tor_i` for every `i ≥ 0`. The coefficients cannot be an arbitrary
coefficient category: over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has the
non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ` in degree `-1`, although `R/(x)` has Tor
amplitude in `[-1, 0]`. This is blueprint `proposition-six-operations-dctf--14` (i).
-/
theorem boundedConstructible_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : finiteTorAmplitude (ModuleCat.{u + 1} Λ) X M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) :=
  have : IsNoetherianRing Λ := inferInstance
  ⟨bounded_derivedTensor_of_finiteTorAmplitude _ X hK.1 hMt,
    constructibleHomology_derivedTensor _ (fun F G hF hG n ↦ by
      have := (Etale.constructibleSheaf_iff _ _ _).mp hF
      have := (Etale.constructibleSheaf_iff _ _ _).mp hG
      exact (Etale.constructibleSheaf_iff _ _ _).mpr
        (isConstructibleSheaf_homology_tensor_singleFunctor Λ F G n)) hK hM⟩

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (ii): `- ⊗ᴸ - : Dctf(X, Λ) × Dctf(X, Λ) ⥤ Dctf(X, Λ)` is defined, for a finite ring
`Λ`. The internal-Hom half of the clause is `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`
below. This is blueprint `proposition-six-operations-dctf--14` (ii).
-/
theorem constructibleFiniteTor_tensor (X : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) := by
  obtain ⟨hKbc, a, b, hKt⟩ := hK
  obtain ⟨hMbc, c, d, hMt⟩ := hM
  exact ⟨boundedConstructible_tensor Λ X hKbc hMbc ⟨c, d, hMt⟩,
    a + c, b + d, torAmplitudeIn_tensor _ X a b c d hKt hMt⟩

end Tensor

/-! ### Tensoring an extension by zero -/

section OpenTensor

variable [UpperStarPreservesFlat A] {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Blueprint `proposition-proper-direct-image-extension-zero--8`: Tensoring an extension by zero.

For an open immersion `j : U ⟶ Y`, the natural isomorphism
`(j_!K) ⊗ᴸ M ≅ j_!(K ⊗ᴸ Lj^*M)` of bifunctors `D(U_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`, where `j_!` is
the (exact) extension by zero applied levelwise, `⊗ᴸ` the derived tensor product and `Lj^*`
the derived pullback. It is the inverse of the projection formula
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`, which is checked to be
an isomorphism after restricting to `U` and to the closed complement of `U`. -/
noncomputable def derivedTensorOpenImmersionLowerShriekIso :
    derivedTensorWhiskeringLeftOpenImmersionLowerShriek A j ≅
      (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorWhiskeringRightLeftDerivedUpperStar A j) :=
  (derivedOpenImmersionLowerShriekProjectionIso A j).symm

end OpenTensor

/-! ### Open immersions -/

section OpenImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U Y : Scheme.{u}} (j : U ⟶ Y)
  [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j]

/-- The derived lower shriek along a quasi-compact open immersion `j` is extension by zero,
`Rj_! ≅ D(j_!)`: it is computed by the compactification `U ⟶[j] Y ⟶[𝟙] Y`, and `Rj_!` does not
depend on the compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). -/
noncomputable def rightDerivedLowerShriekIsoOfIsOpenImmersion :
    R(j)_![ModuleCat.{u + 1} Λ] ≅ D((j)_!open[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerShriekIso Λ (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft D((j)_!open[ModuleCat.{u + 1} Λ])
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _

omit [Finite Λ] [HasCompactification j] in
/-- Blueprint `proposition-proper-direct-image-extension-zero--8`: Extension by zero preserves
constructibility and Tor amplitude.

Let `j : U ⟶ Y` be a quasi-compact open immersion (for instance any open immersion of
finite-type schemes over a field) and `Λ` a ring. If `K` is a bounded constructible complex
on `U` with homology concentrated in `[a, b]` and Tor amplitude in `[c, d]`, then the extension
by zero `j_!K` is bounded constructible on `Y`, with homology concentrated in `[a, b]` and Tor
amplitude in `[c, d]`; in particular `j_!K ∈ Dctf(Y, Λ)`. Indeed `j_!` is exact, so
`Hʳ(j_!K) = j_!Hʳ(K)`, the extension by zero of a constructible sheaf is constructible, and
`j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)` (`proposition-proper-direct-image-extension-zero--8`) for a sheaf `G`
on `Y` in degree `0`. -/
theorem boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    {a b c d : ℤ} {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : boundedConstructible (ModuleCat.{u + 1} Λ) U K)
    (hab : _root_.DerivedCategory.homologyConcentratedIn a b K)
    (hcd : torAmplitudeIn (ModuleCat.{u + 1} Λ) U c d K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Y (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) ∧
      _root_.DerivedCategory.homologyConcentratedIn a b
        (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Y c d (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) := by
  let F := (j)_!open[ModuleCat.{u + 1} Λ]
  refine ⟨⟨?_, fun n ↦ ?_⟩, F.homologyConcentratedIn_mapDerivedCategory_obj hab, fun G ↦ ?_⟩
  · exact F.bounded_mapDerivedCategory_obj hbc.1
  · have := hbc.2 n
    have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n ⋙ F).obj K) :=
      IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
        j.range_closedComplement ((_root_.DerivedCategory.homologyFunctor _ n).obj K)
    exact IsConstructibleSheaf.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
  · -- `j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)`
    have e := ((derivedTensorOpenImmersionLowerShriekIso (ModuleCat.{u + 1} Λ) j).app
      K).app ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ≪≫
      F.mapDerivedCategory.mapIso (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) j).app G))
    obtain ⟨h₁, h₂⟩ := F.homologyConcentratedIn_mapDerivedCategory_obj (hcd ((j)^*[_].obj G))
    have : _root_.DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) c := h₁
    have : _root_.DerivedCategory.TStructure.t.IsLE (F.mapDerivedCategory.obj
        (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj (((j)^*[ModuleCat.{u + 1} Λ] ⋙
          _root_.DerivedCategory.singleFunctor _ 0).obj G))) d := h₂
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm c,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm d⟩

omit [Finite Λ] [HasCompactification j] in
/-- Extension by zero along a quasi-compact open immersion `j` preserves membership in
`D_c^[a, b]` with Tor amplitude in `[a, b]`; the case `[c, d] = [a, b]` of
`boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`. -/
theorem constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) :=
  have h := boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    Λ j hK.1.1 hK.1.2 hK.2
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Blueprint `proposition-proper-direct-image-extension-zero--8`: Extension by zero preserves the
finite-Tor constructible category.

For a quasi-compact open immersion `j : U ⟶ Y` admitting a compactification and a finite ring
`Λ`, extension by zero sends `Dctf(U, Λ)` into `Dctf(Y, Λ)` *without moving the interval*: if
`K` is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`, then so is `Rj_! K`. Indeed `Rj_! = j_!` is exact, the extension by zero of a
constructible sheaf is constructible, and `j_!K ⊗ᴸ F ≅ j_!(K ⊗ᴸ j^*F)` by the projection
formula. -/
theorem constructibleTorAmplitudeIn_rightDerivedLowerShriek (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj K) :=
  constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app K).symm
    (constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ j a b hK)

/-- For a quasi-compact open immersion `j`, the exceptional inverse image is the restriction,
`Rj^! ≅ D(j^*)`: both are right adjoint to `Rj_! ≅ D(j_!)`. -/
noncomputable def rightDerivedUpperShriekIsoOfIsOpenImmersion :
    R(j)^![Λ] ≅ D((j)^*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedUpperShriekAdjunction Λ j).rightAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoLeft
      (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).symm)

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (i), open-immersion case: for a quasi-compact open immersion `f` and a finite ring `Λ`,
`Rf^!` preserves the constructible interval and the Tor amplitude *unchanged*, the right adjoint
of `Rf_! ≅ f_!` being the exact functor `f^*`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U a b
      ((R(j)^![Λ]).obj K) := by
  obtain ⟨⟨hbc, hab⟩, hta⟩ := hK
  refine constructibleTorAmplitudeIn_of_iso _
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app K).symm ⟨⟨?_,
      ((j)^*[ModuleCat.{u + 1} Λ]).homologyConcentratedIn_mapDerivedCategory_obj hab⟩, ?_⟩
  · exact hbc.mapDerivedCategory_upperStar j
  · exact (torAmplitudeIn (ModuleCat.{u + 1} Λ) U a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ j a b hta)

end OpenImmersion

/-! ### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `proposition-six-operations-dctf`, clause (i): the restriction
`Lf^* : Dctf(Y, A) ⥤ Dctf(X, A)` of the derived pullback to the small categories. -/
noncomputable def DerivedCategoryFiniteTor.leftDerivedUpperStar [UpperStarPreservesFlat A]
    (f : X ⟶ Y) :
    DerivedCategoryFiniteTor A Y ⥤ DerivedCategoryFiniteTor A X :=
  ObjectProperty.lift _ (DerivedCategoryFiniteTor.ι A Y ⋙ L((f)^*[A]))
    fun K ↦ constructibleFiniteTor_leftDerivedUpperStar A f K.property

/-- Blueprint `proposition-six-operations-dctf`, clause (vi): the restriction
`𝔻_X : Dctf(X, A)ᵒᵖ ⥤ Dctf(X, A)` of the Verdier dual to the small categories, given that `𝔻_X`
preserves `Dctf(X, A)`. For a finite `Λ` whose exponent is invertible on `k` and `X` separated of
finite type over `k`, this is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`; that
the restriction is an anti-equivalence is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`. -/
noncomputable def DerivedCategoryFiniteTor.verdierDual {S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a]
    (h : ∀ ⦃K⦄, constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((Etale.verdierDual Λ a).obj (op K))) :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ⥤ DerivedCategoryFiniteTor (ModuleCat.{u +
        1} Λ) X :=
  ObjectProperty.lift _ ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X).op ⋙ Etale.verdierDual
      Λ a)
    fun K ↦ h K.unop.property

end Functors

/-! ### Tensoring with a shifted flat object -/

omit [HasSmallSiteSheafify A] in
/-- Shifting moves the Tor amplitude: if `K` has Tor amplitude in `[a, b]`, then `K⟦n⟧` has
Tor amplitude in `[a - n, b - n]`. -/
lemma torAmplitudeIn_shift {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} {a b : ℤ}
    (hK : torAmplitudeIn A X a b K) (n : ℤ) : torAmplitudeIn A X (a - n) (b - n) (K⟦n⟧) := by
  intro F
  obtain ⟨h₁, h₂⟩ := hK F
  set F' := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let e : ((-⊗ᴸ-(X)[A]).obj (K⟦n⟧)).obj F' ≅ (((-⊗ᴸ-(X)[A]).obj K).obj F')⟦n⟧ :=
    (((-⊗ᴸ-(X)[A]).flip.obj F').commShiftIso n).app K
  have : _root_.DerivedCategory.TStructure.t.IsGE (((-⊗ᴸ-(X)[A]).obj K).obj F') a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE (((-⊗ᴸ-(X)[A]).obj K).obj F') b := h₂
  have := _root_.DerivedCategory.TStructure.t.isGE_shift
    (((-⊗ᴸ-(X)[A]).obj K).obj F') a n (a - n)
  have := _root_.DerivedCategory.TStructure.t.isLE_shift
    (((-⊗ᴸ-(X)[A]).obj K).obj F') b n (b - n)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm _,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm _⟩

omit [HasSmallSiteSheafify A] in
/-- A flat sheaf placed in degree `0` has Tor amplitude in `[0, 0]`: the single complex is a
bounded complex of flat objects concentrated in degree `0`. -/
lemma torAmplitudeIn_singleFunctor_zero_of_flat {X : Scheme.{u}}
    (L : Sheaf X.smallEtaleTopology A) (hL : ObjectProperty.flat L) :
    torAmplitudeIn A X 0 0 ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
  (torAmplitudeIn A X 0 0).prop_of_iso
    ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app L).symm
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ 0 0 fun q ↦ by
      by_cases hq : q = 0
      · subst hq
        exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 L).symm hL
      · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq))

omit [HasSmallSiteSheafify A] in
/-- If `N ≅ K ⊗ᴸ ω` with `ω ≅ L⟦m⟧`, where `K` has Tor amplitude in `[a, b]`, `L` has Tor
amplitude in `[0, 0]` and `(K ⊗ᴸ L)⟦m⟧` is bounded constructible, then `N` lies in
`D_c^[a - m, b - m]` with Tor amplitude in `[a - m, b - m]`. -/
lemma constructibleTorAmplitudeIn_of_iso_tensor_shift {X : Scheme.{u}}
    {N K ω L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} {a b m : ℤ}
    (e₁ : N ≅ ((-⊗ᴸ-(X)[A]).obj K).obj ω) (e₂ : ω ≅ L⟦m⟧) (hK : torAmplitudeIn A X a b K)
    (hL : torAmplitudeIn A X 0 0 L)
    (hbc : boundedConstructible A X ((((-⊗ᴸ-(X)[A]).obj K).obj L)⟦m⟧)) :
    constructibleTorAmplitudeIn A X (a - m) (b - m) N := by
  let e : N ≅ (((-⊗ᴸ-(X)[A]).obj K).obj L)⟦m⟧ :=
    e₁ ≪≫ ((-⊗ᴸ-(X)[A]).obj K).mapIso e₂ ≪≫ ((((-⊗ᴸ-(X)[A]).obj K).commShiftIso m).app L)
  have ht : torAmplitudeIn A X a b (((-⊗ᴸ-(X)[A]).obj K).obj L) := by
    simpa using torAmplitudeIn_tensor A X a b 0 0 hK hL
  have ht' := torAmplitudeIn_shift A ht m
  exact constructibleTorAmplitudeIn_of_iso A e.symm
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht'⟩, ht'⟩

end Etale

end AlgebraicGeometry
