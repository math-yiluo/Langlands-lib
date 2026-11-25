/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The projection formula and finite reduction of the coefficients

Let `Λ` be a coefficient ring and `J` an ideal of `Λ`. In this repository the reduction of
coefficients `K ↦ K_m` along `Λ ⟶ Λ/J` is the endofunctor
`ρ = AlgebraicGeometry.Etale.reductionModIdeal`, `K ↦ K ⊗ᴸ (Λ/J)_X`, of `D(X_ét, Λ)`: the
reduction `K_m` is kept as a complex of `Λ`-modules. Read in `D(Λ)`, a tensor product over
`Λ/J` of two reduced complexes is `K_m ⊗ᴸ_{Λ/J} L_m = K ⊗ᴸ_Λ L_m`, and `Rf_!` commutes with
reduction, so the projection map `PF_{f, K_m, L_m}` of the blueprint becomes the projection map
`PF_{f, K, ρL}` over `Λ`.

The three compatibilities of `ρ` used in blueprint `sk-prop-sf-pf-reduction` are:

* with `⊗ᴸ`: the associator `ρ(M ⊗ᴸ L) = (M ⊗ᴸ L) ⊗ᴸ (Λ/J)_Y ≅ M ⊗ᴸ ρL`;
* with `Lf^*`: `Lf^*(ρL) ≅ ρ(Lf^*L)`, the tensor comparison of `Lf^*` followed by
  `Lf^*(Λ/J)_Y ≅ (Λ/J)_X` (`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`);
* with `Rf_!`: `ρ(Rf_!K) ⟶ Rf_!(ρK)`, the projection map at `(K, (Λ/J)_Y)` followed by
  `Lf^*(Λ/J)_Y ≅ (Λ/J)_X` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekReductionModIdealMap`).
  It is an isomorphism for `Λ` finite, by the finite projection formula.

Everything except the identification of the constant complexes is formal, and is done for an
arbitrary coefficient category `A` and an arbitrary object `N` in place of `(Λ/J)_Y`. The square
is stated for a general coefficient category: at `A = ModuleCat Λ`, writing the monoidal
structure of `D(X_ét, Λ)` through instance search produces a term the kernel cannot compare
with the one inside `AlgebraicGeometry.Etale.derivedTensor` in reasonable time (see the
implementation notes of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).

When `Λ/ϖⁿ` is perfect, that is for `J = (ϖⁿ)` with `ϖ` a nonzerodivisor (for `Λ = 𝒪_E`, the
reduction `𝒪_E ⟶ A_{E,n}`), the constant complex `(Λ/ϖⁿ)_X` is dualizable, and the comparisons
of `ρ` with `Rf_!` and `Rf_*` are isomorphisms for every `Λ` (blueprint
`proposition-six-operations-change-coefficients`).

## Main statements

- `AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle`
  (`sk-prop-sf-pf-reduction`, `prop-sf-pf-reduction`): the square comparing `ρ(PF_{f, K, L})`
  and `PF_{f, K, ρL}` through the three compatibilities commutes.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMapOfCompactification_iff`,
  `AlgebraicGeometry.Etale.hasProjectionFormula_iff_reductionModIdeal`: hence, for `Λ` finite,
  `ρ(PF_{f, K, L})` is an isomorphism if and only if `PF_{f, K, ρL}` is, and the projection
  formula holds at `(K, L)` if and only if it holds at `(K, ρL)`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow`,
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_span_pow`
  (`proposition-six-operations-change-coefficients`): reduction modulo `ϖⁿ` commutes with `Rf_!` and
  `Rf_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X Y : Scheme.{u}}

/-- The compatibility of `- ⊗ᴸ N` with the derived tensor product: the associator
`(M ⊗ᴸ L) ⊗ᴸ N ≅ M ⊗ᴸ (L ⊗ᴸ N)`. -/
noncomputable def derivedTensorRightTensorIso
    (N M L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorRight A X N).obj (((-⊗ᴸ-(X)[A]).obj M).obj L) ≅
      ((-⊗ᴸ-(X)[A]).obj M).obj ((derivedTensorRight A X N).obj L) :=
  α_ M L N

/-- For `a : Lf^*N_Y ≅ N_X`, the isomorphism `Lf^*(L ⊗ᴸ N_Y) ≅ Lf^*L ⊗ᴸ N_X`, natural in `L`:
the tensor comparison of `Lf^*` followed by `a`. -/
noncomputable def leftDerivedUpperStarDerivedTensorRightIso (f : X ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX) :
    derivedTensorRight A Y NY ⋙ L((f)^*[A]) ≅ L((f)^*[A]) ⋙ derivedTensorRight A X NX :=
  derivedTensorRightCompLeftDerivedUpperStarIso A f NY ≪≫
    Functor.isoWhiskerLeft L((f)^*[A]) ((derivedTensorRightFunctor A X).mapIso a)

lemma leftDerivedUpperStarDerivedTensorRightIso_hom_app (f : X ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarDerivedTensorRightIso A f a).hom.app L =
      ((leftDerivedUpperStarTensorComparison A f).app L).app NY ≫
        L((f)^*[A]).obj L ◁ a.hom :=
  rfl

/-- For `a : Lg^*N_Y ⟶ N_Z`, the comparison `Rg_*M ⊗ᴸ N_Y ⟶ Rg_*(M ⊗ᴸ N_Z)`, natural in `M`: the
projection map of `Rg_*` at `(M, N_Y)` followed by `Rg_*(M ◁ a)`. -/
noncomputable def rightDerivedLowerStarDerivedTensorRightMap {Z : Scheme.{u}} (g : Z ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NZ : DerivedCategory (Sheaf Z.smallEtaleTopology A)} (a : L((g)^*[A]).obj NY ⟶ NZ) :
    R((g)_*[A]) ⋙ derivedTensorRight A Y NY ⟶ derivedTensorRight A Z NZ ⋙ R((g)_*[A]) where
  app M := ((rightDerivedLowerStarProjectionMap A g).app M).app NY ≫ R((g)_*[A]).map (M ◁ a)
  naturality _ _ φ := Adjunction.projectionMap_comp_map_whiskerLeft_naturality
    (fun M L ↦ ((rightDerivedLowerStarProjectionMap A g).app M).app L) a
    (fun φ L ↦ NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A g).naturality φ) L) φ

/-- **`Rg_*` commutes with tensoring by a dualizable object.** For `a : Lg^*N_Y ≅ N_Z` with `N_Y`
dualizable, the comparison `Rg_*M ⊗ᴸ N_Y ⟶ Rg_*(M ⊗ᴸ N_Z)` is an isomorphism, by the projection
formula for `Rg_*` at a dualizable object
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable`). -/
theorem isIso_rightDerivedLowerStarDerivedTensorRightMap_of_isDualizable {Z : Scheme.{u}}
    (g : Z ⟶ Y) {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NZ : DerivedCategory (Sheaf Z.smallEtaleTopology A)} (a : L((g)^*[A]).obj NY ≅ NZ)
    (hN : IsDualizable NY) :
    IsIso (rightDerivedLowerStarDerivedTensorRightMap A g a.hom) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable A g M hN
  exact inferInstanceAs (IsIso (_ ≫ _))

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {f : X ⟶ Y} (c : Compactification f)

/-- For `a : Lf^*N_Y ⟶ N_X`, the comparison `Rf_!K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)`, natural in `K`: the
projection map `PF_{K, N_Y}` followed by `Rf_!(K ◁ a)`. -/
noncomputable def rightDerivedLowerShriekDerivedTensorRightMap
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ⟶ NX) :
    Rf_!(c)[A] ⋙ derivedTensorRight A Y NY ⟶ derivedTensorRight A X NX ⋙ Rf_!(c)[A] where
  app K := ((projectionMapOfCompactification A c).app K).app NY ≫
    Rf_!(c)[A].map (K ◁ a)
  naturality _ _ φ := Adjunction.projectionMap_comp_map_whiskerLeft_naturality
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L) a
    (fun φ L ↦ NatTrans.congr_app ((projectionMapOfCompactification A c).naturality φ) L) φ

lemma rightDerivedLowerShriekDerivedTensorRightMap_app
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ⟶ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekDerivedTensorRightMap A c a).app K =
      ((projectionMapOfCompactification A c).app K).app NY ≫ Rf_!(c)[A].map (K ◁ a) :=
  rfl

/-- **The reduction square of the projection map, for a general coefficient object.** For
`a : Lf^*N_Y ≅ N_X`, `K` on `X` and `L` on `Y`, the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N_Y ---PF_{K, L} ⊗ᴸ N_Y---> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N_Y
        | ≅ (associator)                               | comparison of Rf_! and - ⊗ᴸ N
        v                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N_Y)                           Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ N_X)
        | PF_{K, L ⊗ᴸ N_Y}                             ^ ≅ Rf_!(associator⁻¹)
        v                                              |
Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N_Y)) ---Rf_!(K ⊗ᴸ (δ ≫ 1 ⊗ᴸ a))--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ N_X))
```
commutes, where the comparisons are `AlgebraicGeometry.Etale.derivedTensorRightTensorIso`,
`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorRightMap` and
`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorRightIso`. It follows from the
associativity of the projection map
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`). -/
theorem projectionMapOfCompactification_derivedTensorRight
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorRight A Y NY).map (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app
          (K ⊗ L((f)^*[A]).obj L) =
      (derivedTensorRightTensorIso A NY ((Rf_!(c)[A]).obj K) L).hom ≫
        ((projectionMapOfCompactification A c).app K).app (L ⊗ NY) ≫
        Rf_!(c)[A].map (K ◁ (leftDerivedUpperStarDerivedTensorRightIso A f a).hom.app L) ≫
        Rf_!(c)[A].map (derivedTensorRightTensorIso A NX K (L((f)^*[A]).obj L)).inv :=
  Adjunction.projectionMap_whiskerRight_comp
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L)
    (projectionMapOfCompactification_assoc A c) a.hom K L

/-- **Invertibility through the reduction square, for a general coefficient object.** If the
comparison `Rf_!M ⊗ᴸ N_Y ⟶ Rf_!(M ⊗ᴸ N_X)` is an isomorphism at `M = K ⊗ᴸ Lf^*L`, then
`PF_{K, L} ⊗ᴸ N_Y` is an isomorphism if and only if `PF_{K, L ⊗ᴸ N_Y}` is. -/
theorem isIso_derivedTensorRight_map_projectionMapOfCompactification_iff
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hc : IsIso ((rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app
      (K ⊗ L((f)^*[A]).obj L))) :
    IsIso ((derivedTensorRight A Y NY).map (((projectionMapOfCompactification A c).app K).app L))
      ↔ IsIso (((projectionMapOfCompactification A c).app K).app (L ⊗ NY)) :=
  Adjunction.isIso_projectionMap_whiskerRight_iff
    (fun K L ↦ ((projectionMapOfCompactification A c).app K).app L)
    (projectionMapOfCompactification_assoc A c) a.hom K L hc

/-- If the projection formula holds at `(K, N_Y)` for every `K`, then for `a : Lf^*N_Y ≅ N_X` the
comparison `Rf_!K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)` is an isomorphism. -/
theorem isIso_rightDerivedLowerShriekDerivedTensorRightMap
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (h : ∀ K, HasProjectionFormulaOfCompactification A c K NY) :
    IsIso (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ ?_
  have : IsIso (((projectionMapOfCompactification A c).app K).app NY) := h K
  exact inferInstanceAs (IsIso (_ ≫ _))

/-- **`Rf_!` commutes with tensoring by a dualizable object.** For `a : Lf^*N_Y ≅ N_X` with
`N_Y` dualizable, the comparison `Rf_!K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)` is an isomorphism, by the
projection formula at a dualizable object
(`AlgebraicGeometry.Etale.hasProjectionFormulaOfCompactification_of_isDualizable`). -/
theorem isIso_rightDerivedLowerShriekDerivedTensorRightMap_of_isDualizable
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (hN : IsDualizable NY) :
    IsIso (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom) :=
  isIso_rightDerivedLowerShriekDerivedTensorRightMap A c a fun K ↦
    hasProjectionFormulaOfCompactification_of_isDualizable A c K hN

/-- A form of
`AlgebraicGeometry.Etale.isIso_derivedTensorRight_map_projectionMapOfCompactification_iff` in
which the object `L ⊗ᴸ N_Y` at which the second projection map is taken may be given by any
equal expression `LN`; this lets the statement be specialised to the reduction functors of a
concrete coefficient ring. -/
theorem isIso_derivedTensorRight_map_projectionMapOfCompactification_iff'
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (hc : IsIso ((rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app
      (((derivedTensor A X).obj K).obj (L((f)^*[A]).obj L))))
    (LN : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (hLN : L ⊗ NY = LN) :
    IsIso ((derivedTensorRight A Y NY).map (((projectionMapOfCompactification A c).app K).app L))
      ↔ IsIso (((projectionMapOfCompactification A c).app K).app LN) := by
  subst hLN
  exact isIso_derivedTensorRight_map_projectionMapOfCompactification_iff A c a K L hc

end General

section Constant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}}

/-- The constant complex `M_X ∈ D(X_ét)` on an object `M` of the coefficient category: the
constant sheaf with value `M`, placed in degree zero. -/
noncomputable abbrev constantSingle (X : Scheme.{u}) (M : A) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology A).obj M)

/-- **The derived pullback of a constant complex is constant**: `Lf^*(M_Y) ≅ M_X`. The pullback
`f^*` is exact, so `Lf^*` is computed termwise
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`), and `f^*` carries
constant sheaves to constant sheaves (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). -/
noncomputable def leftDerivedUpperStarSingleConstantSheafIso (f : X ⟶ Y) (M : A) :
    L((f)^*[A]).obj (constantSingle A Y M) ≅ constantSingle A X M :=
  (leftDerivedUpperStarIsoMapDerivedCategory A f).app _ ≪≫
    ((f)^*[A].mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((Scheme.upperStarConstantSheafIso A f).app M)

omit [HasSmallSiteSheafify A] in
/-- A sheaf `F` which is the cokernel of a monomorphism `𝟙 ⟶ 𝟙` of unit sheaves is dualizable
in `D(X_ét)` when placed in degree zero
(`DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact`). For `A = ModuleCat Λ` and a
nonzerodivisor `ϖ` of `Λ`, this applies to the constant sheaf `(Λ/ϖⁿ)_X`, the cokernel of
`ϖⁿ : Λ_X ⟶ Λ_X`. -/
theorem isDualizable_singleFunctor_obj_of_shortExact_unit
    {S : ShortComplex (Sheaf X.smallEtaleTopology A)} (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ 𝟙_ _) (e₂ : S.X₂ ≅ 𝟙_ _) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj S.X₃) :=
  DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS
    (isDualizable_unit.of_iso e₁.symm) (isDualizable_unit.of_iso e₂.symm)

omit [HasSmallSiteSheafify A] in
/-- The constant complex `M_X` is dualizable if the constant sheaf `M_X` is the cokernel of a
monomorphism `𝟙 ⟶ 𝟙` of unit sheaves
(`AlgebraicGeometry.Etale.isDualizable_singleFunctor_obj_of_shortExact_unit`). -/
theorem isDualizable_constantSingle_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology A)} (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ 𝟙_ _) (e₂ : S.X₂ ≅ 𝟙_ _) {M : A}
    (e₃ : S.X₃ ≅ (constantSheaf X.smallEtaleTopology A).obj M) :
    IsDualizable (constantSingle A X M) :=
  (isDualizable_singleFunctor_obj_of_shortExact_unit A hS e₁ e₂).of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso e₃)

omit [HasSmallSiteSheafify A] in
/-- The constant complex `M_X` is dualizable if the constant sheaf `M_X` is isomorphic to the
unit sheaf. -/
theorem isDualizable_constantSingle_of_iso_unit {M : A}
    (e : (constantSheaf X.smallEtaleTopology A).obj M ≅ 𝟙_ _) :
    IsDualizable (constantSingle A X M) :=
  isDualizable_unit.of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso e ≪≫ singleFunctorObjUnitIso A X).symm

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {f : X ⟶ Y} (c : Compactification f)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `sk-prop-sf-pf-reduction`, with its detailed node `prop-sf-pf-reduction`:
Projection formula: compatibility with finite reduction; the square.

Let `M` be an object of the coefficient category and `ρ = - ⊗ᴸ M` the functor of tensoring with
the constant complex `M_X` on every scheme `X`. For `A = ModuleCat Λ` and `M = Λ/J` this is the
reduction of the coefficients along `Λ ⟶ Λ/J`, kept in `D(-, Λ)`
(`AlgebraicGeometry.Etale.reductionModIdeal`, see
`AlgebraicGeometry.Etale.reductionModIdeal_eq_derivedTensorRight`); for `Λ = A_{E,n}` and
`J = 𝔪_E^m` it is the finite reduction `K ↦ K_m` of the blueprint. For `K` on `X` and `L` on
`Y` the square
```
ρ(Rf_!K ⊗ᴸ L) ------------ρ(PF_{K, L})-------------> ρ(Rf_!(K ⊗ᴸ Lf^*L))
     | ≅ (associator)                                          | comparison of Rf_! and ρ
     v                                                         v
Rf_!K ⊗ᴸ ρL ---PF_{K, ρL}---> Rf_!(K ⊗ᴸ Lf^*ρL) ---≅---> Rf_!(ρ(K ⊗ᴸ Lf^*L))
```
commutes. Here the comparison of `Rf_!` with `ρ` is the projection map at `(-, M_Y)` followed by
`Lf^*M_Y ≅ M_X` (`AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`), and the
bottom right isomorphism is built from the comparison of `Lf^*` with `ρ` (the tensor comparison of
`Lf^*` followed by the same isomorphism) and the associator. Read in `D(-, Λ)`, `PF_{K, ρL}` is
the projection map `PF_{K_m, L_m}` of the reductions, since `K_m ⊗ᴸ_{Λ/J} L_m = K ⊗ᴸ_Λ L_m`.

As in the blueprint, this is an equality of the specified morphisms, proved from their
constructions and not from agreement on stalks: the projection map of `Rf_!` is associative
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`), which comes down to the
counit–tensor description of the projection map of the proper direct image and the
monoidality of the derived pullbacks. -/
theorem projectionMapOfCompactification_constantSingle (M : A)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorRight A Y (constantSingle A Y M)).map
        (((projectionMapOfCompactification A c).app K).app L) ≫
        (rightDerivedLowerShriekDerivedTensorRightMap A c
          (leftDerivedUpperStarSingleConstantSheafIso A f M).hom).app (K ⊗ L((f)^*[A]).obj L) =
      (derivedTensorRightTensorIso A (constantSingle A Y M) ((Rf_!(c)[A]).obj K) L).hom ≫
        ((projectionMapOfCompactification A c).app K).app (L ⊗ constantSingle A Y M) ≫
        Rf_!(c)[A].map (K ◁ (leftDerivedUpperStarDerivedTensorRightIso A f
          (leftDerivedUpperStarSingleConstantSheafIso A f M)).hom.app L) ≫
        Rf_!(c)[A].map
          (derivedTensorRightTensorIso A (constantSingle A X M) K (L((f)^*[A]).obj L)).inv :=
  projectionMapOfCompactification_derivedTensorRight A c _ K L

end Constant

section Module

variable (Λ : Type (u + 1)) [CommRing Λ] (J : Ideal Λ) {X Y : Scheme.{u}}

lemma reductionModIdeal_eq_derivedTensorRight (X : Scheme.{u}) :
    reductionModIdeal Λ X J = derivedTensorRight (ModuleCat.{u + 1} Λ) X
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J))) :=
  rfl

/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the pullback.

**`Lf^*` commutes with the reduction of the coefficients**: the isomorphism
`Lf^*(L ⊗ᴸ (Λ/J)_Y) ≅ Lf^*L ⊗ᴸ (Λ/J)_X`, natural in `L`, given by the tensor comparison of
`Lf^*` followed by `Lf^*(Λ/J)_Y ≅ (Λ/J)_X`. The two functors are
`reductionModIdeal Λ Y J ⋙ Lf^*` and `Lf^* ⋙ reductionModIdeal Λ X J`
(`AlgebraicGeometry.Etale.reductionModIdeal_eq_derivedTensorRight`). -/
noncomputable def leftDerivedUpperStarReductionModIdealIso (f : X ⟶ Y) :
    derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J))) ⋙
        L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight _ X (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J))) :=
  leftDerivedUpperStarDerivedTensorRightIso _ f
    (leftDerivedUpperStarSingleConstantSheafIso _ f (ModuleCat.of Λ (Λ ⧸ J)))

attribute [local instance] Scheme.Etale.essentiallySmall

/-- The comparison of `Rg_*` with the reduction of the coefficients,
`ρ(Rg_*M) = Rg_*M ⊗ᴸ (Λ/J)_Y ⟶ Rg_*(M ⊗ᴸ (Λ/J)_Z) = Rg_*(ρM)`, natural in `M`: the projection
map of `Rg_*` at `(M, (Λ/J)_Y)` followed by `Lg^*(Λ/J)_Y ≅ (Λ/J)_Z`. -/
noncomputable def rightDerivedLowerStarReductionModIdealMap {Z : Scheme.{u}} (g : Z ⟶ Y) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J))) ⟶
      derivedTensorRight _ Z (constantSingle _ Z (ModuleCat.of Λ (Λ ⧸ J))) ⋙
        R((g)_*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedLowerStarDerivedTensorRightMap _ g
    (leftDerivedUpperStarSingleConstantSheafIso _ g (ModuleCat.of Λ (Λ ⧸ J))).hom

variable {Λ} in
/-- For a nonzerodivisor `ϖ` of `Λ`, the constant complex `(Λ/ϖⁿ)_X` is dualizable: the constant
sheaf `(Λ/ϖⁿ)_X` is the cokernel of the multiplication `ϖⁿ : Λ_X ⟶ Λ_X`
(`DerivedCategory.sheafQuotPowShortComplex_shortExact`). -/
theorem isDualizable_constantSingle_quotient_span_pow {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) (X : Scheme.{u}) :
    IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X
      (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n))) :=
  isDualizable_constantSingle_of_shortExact _
    (DerivedCategory.sheafQuotPowShortComplex_shortExact X.smallEtaleTopology hϖ rfl n)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- The constant complex `(Λ/0)_X` is dualizable: it is the unit `Λ_X`. -/
theorem isDualizable_constantSingle_quotient_bot (X : Scheme.{u}) :
    IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ (⊥ : Ideal Λ)))) :=
  isDualizable_constantSingle_of_iso_unit _
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (Submodule.quotEquivOfEqBot (⊥ : Ideal Λ) rfl).toModuleIso)

variable {Λ} in
/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the ordinary direct image at the integral stage.

For a nonzerodivisor `ϖ` of `Λ` (for `Λ = 𝒪_E`, a uniformizer), the reduction modulo `ϖⁿ`
commutes with `Rg_*` for any morphism `g`: the comparison `ρ(Rg_*M) ⟶ Rg_*(ρM)` is an
isomorphism. As in the blueprint, `Λ/ϖⁿ` is perfect over `Λ`, the constant complex `(Λ/ϖⁿ)_Y` is
dualizable (`AlgebraicGeometry.Etale.isDualizable_constantSingle_quotient_span_pow`), and the
projection map of `Rg_*` is invertible at a dualizable object. -/
theorem isIso_rightDerivedLowerStarReductionModIdealMap_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) {Z : Scheme.{u}} (g : Z ⟶ Y) :
    IsIso (rightDerivedLowerStarReductionModIdealMap Λ (Ideal.span {ϖ} ^ n) g) :=
  isIso_rightDerivedLowerStarDerivedTensorRightMap_of_isDualizable _ g _
    (isDualizable_constantSingle_quotient_span_pow hϖ n Y)

/-- The comparison `ρ(Rg_*M) ⟶ Rg_*(ρM)` for the zero ideal is an isomorphism. -/
theorem isIso_rightDerivedLowerStarReductionModIdealMap_bot {Z : Scheme.{u}} (g : Z ⟶ Y) :
    IsIso (rightDerivedLowerStarReductionModIdealMap Λ ⊥ g) :=
  isIso_rightDerivedLowerStarDerivedTensorRightMap_of_isDualizable _ g _
    (isDualizable_constantSingle_quotient_bot Λ Y)

variable {f : X ⟶ Y} (c : Compactification f)

/-- **The comparison of `Rf_!` with the reduction of the coefficients**,
`ρ(Rf_!K) = Rf_!K ⊗ᴸ (Λ/J)_Y ⟶ Rf_!(K ⊗ᴸ (Λ/J)_X) = Rf_!(ρK)`, natural in `K`: the
projection map at `(K, (Λ/J)_Y)` followed by `Lf^*(Λ/J)_Y ≅ (Λ/J)_X`. The two functors are
`Rf_! ⋙ reductionModIdeal Λ Y J` and `reductionModIdeal Λ X J ⋙ Rf_!`
(`AlgebraicGeometry.Etale.reductionModIdeal_eq_derivedTensorRight`). -/
noncomputable def rightDerivedLowerShriekReductionModIdealMap :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⋙
        derivedTensorRight _ Y (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J))) ⟶
      derivedTensorRight _ X (constantSingle _ X (ModuleCat.of Λ (Λ ⧸ J))) ⋙
        Rf_!(c)[ModuleCat.{u + 1} Λ] :=
  rightDerivedLowerShriekDerivedTensorRightMap _ c
    (leftDerivedUpperStarSingleConstantSheafIso _ f (ModuleCat.of Λ (Λ ⧸ J))).hom

/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the compact-support direct image between finite levels.

For a finite coefficient ring `Λ`, the comparison `ρ(Rf_!K) ⟶ Rf_!(ρK)` of `Rf_!` with the
reduction of the coefficients is an isomorphism: it is a projection map followed by an
isomorphism, and the projection formula holds at finite coefficients
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`). -/
instance isIso_rightDerivedLowerShriekReductionModIdealMap [Finite Λ] :
    IsIso (rightDerivedLowerShriekReductionModIdealMap Λ J c) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ c.g
  refine isIso_rightDerivedLowerShriekDerivedTensorRightMap _ c _ fun K ↦ ?_
  change IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app
    (constantSingle _ Y (ModuleCat.of Λ (Λ ⧸ J))))
  rw [projectionMapOfCompactification_app_app]
  infer_instance

variable {Λ} in
/-- Blueprint `proposition-six-operations-change-coefficients`: Basic operations and coefficient
reduction; the compact-support direct image at the integral stage.

For a nonzerodivisor `ϖ` of `Λ` (for `Λ = 𝒪_E`, a uniformizer), the reduction modulo `ϖⁿ`
commutes with `Rf_!`: the comparison `ρ(Rf_!K) ⟶ Rf_!(ρK)` is an isomorphism, the constant
complex `(Λ/ϖⁿ)_Y` being dualizable
(`AlgebraicGeometry.Etale.isDualizable_constantSingle_quotient_span_pow`). -/
theorem isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    IsIso (rightDerivedLowerShriekReductionModIdealMap Λ (Ideal.span {ϖ} ^ n) c) :=
  isIso_rightDerivedLowerShriekDerivedTensorRightMap_of_isDualizable _ c _
    (isDualizable_constantSingle_quotient_span_pow hϖ n Y)

/-- Blueprint `sk-prop-sf-pf-reduction`, with its detailed node `prop-sf-pf-reduction`:
Projection formula: compatibility with finite reduction; the equivalence of invertibility.

For a finite coefficient ring `Λ` and an ideal `J`, the reduction `ρ(PF_{K, L})` of the
projection map is an isomorphism if and only if the projection map `PF_{K, ρL}` of the
reductions is: by the commutative square
`AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle` the two differ by
isomorphisms, the comparison of `Rf_!` with `ρ` being invertible at finite coefficients
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap`). -/
theorem isIso_reductionModIdeal_map_projectionMapOfCompactification_iff [Finite Λ]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((reductionModIdeal Λ Y J).map
        (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L)) ↔
      IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app
        ((reductionModIdeal Λ Y J).obj L)) :=
  isIso_derivedTensorRight_map_projectionMapOfCompactification_iff' _ c
    (leftDerivedUpperStarSingleConstantSheafIso _ f (ModuleCat.of Λ (Λ ⧸ J))) K L
    (inferInstanceAs (IsIso ((rightDerivedLowerShriekReductionModIdealMap Λ J c).app _))) _ rfl

/-- Blueprint `sk-prop-sf-pf-reduction`, with its detailed node `prop-sf-pf-reduction`:
Projection formula: compatibility with finite reduction; the conclusion.

For a finite coefficient ring `Λ` (for instance `A_{E,n}`) and an ideal `J` (for instance
`𝔪_E^m`, `m ≤ n`), the projection formula holds at `(K, L)` if and only if it holds at
`(K, ρL)`, where `ρ = - ⊗ᴸ (Λ/J)` is the reduction of the coefficients; read in `D(-, Λ)`, the
latter is the projection formula `PF_{K_m, L_m}` of the reductions. As in the blueprint, both
sides hold, by the projection formula at finite coefficients
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`, the case of `sk-thm-sf-pf-finite`);
the comparison square itself is
`AlgebraicGeometry.Etale.projectionMapOfCompactification_constantSingle`. -/
theorem hasProjectionFormula_iff_reductionModIdeal [Finite Λ] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L ↔
      HasProjectionFormula (ModuleCat.{u + 1} Λ) f K ((reductionModIdeal Λ Y J).obj L) :=
  iff_of_true (hasProjectionFormula_of_finite Λ f K L)
    (hasProjectionFormula_of_finite Λ f K _)

end Module

end Etale

end AlgebraicGeometry
