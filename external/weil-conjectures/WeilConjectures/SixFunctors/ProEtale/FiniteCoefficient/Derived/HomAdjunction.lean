/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Internal hom adjunction formulas on the pro-étale site

Let `f : Y ⟶ X` be a morphism of schemes. On the unbounded derived categories of pro-étale
sheaves, the derived pullback `Lf^*` is strong monoidal
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso`). Passing to right adjoints
along `Lf^* ⊣ Rf_*` and the tensor–hom adjunctions gives the internal-hom form of the
projection formula `RHom(B, Rf_* C) ≅ Rf_* RHom(Lf^* B, C)`. In the same way, the projection
formula for the extension by zero along an open immersion `j`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`) gives
`Rj_* RHom(K, j^* N) ≅ RHom(j_! K, N)`.

## Main statements

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomIso`:
  `RHom(B, Rf_* C) ≅ Rf_* RHom(Lf^* B, C)`, naturally in `C`.
- `AlgebraicGeometry.ProEtale.derivedHomOpenImmersionLowerShriekIso`:
  `Rj_* RHom(K, j^* N) ≅ RHom(j_! K, N)` for an open immersion `j`, naturally in `N`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomClosedImmersionIso`:
  `RHom(Ri_* K, Ri_* C) ≅ Ri_* RHom(K, C)` for a closed immersion `i`, naturally in `C`.
- `AlgebraicGeometry.ProEtale.isZero_derivedHom_rightDerivedLowerStar_of_disjoint`:
  `RHom(Ri_* K, Rj_* N) = 0` when the ranges of `i` and of the open immersion `j` are disjoint.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

/-- The **internal-hom projection formula** for a morphism `f : Y ⟶ X`:
`RHom(B, Rf_* C) ≅ Rf_* RHom(Lf^* B, C)`, naturally in `C : D(Y_proét)`. The two sides are right
adjoint to `T ↦ Lf^*(B ⊗ᴸ T)` and to `T ↦ Lf^* B ⊗ᴸ Lf^* T`, which agree since `Lf^*` is strong
monoidal (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso`). -/
noncomputable def rightDerivedLowerStarCompDerivedHomIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    R((f)_*[A]) ⋙ (RHom(X)[A]).obj (op B) ≅
      (RHom(Y)[A]).obj (op (L((f)^*[A]).obj B)) ⋙ R((f)_*[A]) :=
  ((derivedTensorHomAdjunction A B).comp
    (derivedUpperStarLowerStarAdjunction A f)).rightAdjointUniq
    (((derivedUpperStarLowerStarAdjunction A f).comp
      (derivedTensorHomAdjunction A (L((f)^*[A]).obj B))).ofNatIsoLeft
        ((leftDerivedUpperStarTensorNatIso A f).app B).symm)

/-- The **internal-hom form of the projection formula for the extension by zero** along an
open immersion `j : U ⟶ X`: `Rj_* RHom(K, j^* N) ≅ RHom(j_! K, N)`, naturally in
`N : D(X_proét)`. The two sides are right adjoint to `T ↦ j_!(K ⊗ᴸ Lj^* T)` and to
`T ↦ j_! K ⊗ᴸ T`, which agree by the projection formula
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`. -/
noncomputable def derivedHomOpenImmersionLowerShriekIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)) :
    D((j)^*[A]) ⋙ (RHom(U)[A]).obj (op K) ⋙ R((j)_*[A]) ≅
      (RHom(X)[A]).obj (op (D((j)_!open[A]).obj K)) :=
  (((derivedUpperStarLowerStarAdjunction A j).comp (derivedTensorHomAdjunction A K)).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)).rightAdjointUniq
    ((derivedTensorHomAdjunction A (D((j)_!open[A]).obj K)).ofNatIsoLeft
      ((derivedOpenImmersionLowerShriekProjectionIso A j).app K).symm)

omit [ProEtale.UpperStarPreservesFlat A] in
/-- The internal hom out of a zero object of `D(X_proét)` vanishes: maps `T ⟶ RHom(K, N)`
correspond to maps `K ⊗ᴸ T ⟶ N`, and `K ⊗ᴸ T = 0` since the derived tensor product is additive
in each variable. -/
lemma isZero_derivedHom_obj_obj_of_isZero {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : IsZero K)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    IsZero (((RHom(X)[A]).obj (op K)).obj N) := by
  rw [IsZero.iff_id_eq_zero]
  have hT : IsZero (((-⊗ᴸ-(X)[A]).obj K).obj (((RHom(X)[A]).obj (op K)).obj N)) := by
    change IsZero (K ⊗ ((RHom(X)[A]).obj (op K)).obj N)
    rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hK.eq_of_src (𝟙 K) 0,
      MonoidalPreadditive.zero_whiskerRight]
  apply ((derivedTensorHomAdjunction A K).homEquiv _ _).symm.injective
  exact hT.eq_of_src _ _

end General

section Immersion

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

/-- For a closed immersion `i : Z ⟶ X`, the counit `Li^* Ri_* K ⟶ K` is an isomorphism, since
`Ri_*` is fully faithful (`AlgebraicGeometry.ProEtale.full_rightDerivedFunctor_lowerStar`). -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit_isIso_of_R_fully_faithful

/-- For a closed immersion `i : Z ⟶ X`: `RHom(Ri_* K, Ri_* C) ≅ Ri_* RHom(K, C)`, naturally in
`C : D(Z_proét)`. It is `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomIso` for
`B = Ri_* K`, composed with the counit isomorphism `Li^* Ri_* K ≅ K`. -/
noncomputable def rightDerivedLowerStarCompDerivedHomClosedImmersionIso {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))) :
    R((i)_*[ModuleCat.{u + 1} Λ]) ⋙
        (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op (R((i)_*[ModuleCat.{u + 1} Λ]).obj K)) ≅
      (RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op K) ⋙ R((i)_*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedLowerStarCompDerivedHomIso (ModuleCat.{u + 1} Λ) i _ ≪≫
    Functor.isoWhiskerRight ((RHom(Z)[ModuleCat.{u + 1} Λ]).mapIso
      (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K)).op.symm)
      _

omit [IsNoetherianRing Λ] in
/-- If the ranges of `i : Z ⟶ X` and of the open immersion `j : U ⟶ X` are disjoint, then
`Lj^* Ri_* K = 0` for every `K : D(Z_proét)`: computing `Ri_* K` by a K-injective complex `I`,
`Lj^* Ri_* K ≅ j^* i_* I` termwise, and `j^* i_* = 0` on sheaves
(`AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint`). -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))) :
    IsZero (L((j)^*[ModuleCat.{u + 1} Λ]).obj (R((i)_*[ModuleCat.{u + 1} Λ]).obj K)) := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have hI : IsZero ((((j)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex _).obj
      ((((i)_*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex _).obj I)) := by
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} Λ) i j hij _).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hI).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _ ≪≫
      D((j)^*[ModuleCat.{u + 1} Λ]).mapIso (R((i)_*[ModuleCat.{u + 1} Λ]).mapIso e ≪≫
        ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorObjQIso I) ≪≫
      ((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app _)

/-- If the ranges of `i : Z ⟶ X` and of the open immersion `j : U ⟶ X` are disjoint (e.g.
`j` is the open complement of the closed immersion `i`), then `RHom(Ri_* K, Rj_* N) = 0` for all
`K : D(Z_proét)` and `N : D(U_proét)`: by
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompDerivedHomIso` it is
`Rj_* RHom(Lj^* Ri_* K, N)`, and `Lj^* Ri_* K = 0`. -/
lemma isZero_derivedHom_rightDerivedLowerStar_of_disjoint
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    IsZero (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
      (op (R((i)_*[ModuleCat.{u + 1} Λ]).obj K))).obj (R((j)_*[ModuleCat.{u + 1} Λ]).obj N)) :=
  have := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).isRightAdjoint
  (Functor.map_isZero R((j)_*[ModuleCat.{u + 1} Λ]) (isZero_derivedHom_obj_obj_of_isZero _
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint i j hij K) N)).of_iso
    ((rightDerivedLowerStarCompDerivedHomIso (ModuleCat.{u + 1} Λ) j _).app N)

end Immersion

end AlgebraicGeometry.ProEtale
