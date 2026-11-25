/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars

/-!

# The Künneth map of nearby cycles under a flat change of coefficients

This is the analogue of `WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChange` for a
flat coefficient change `a : Λ ⟶ Λ'` (the extensions of scalars along `a` preserve finite limits),
with the (Pull) isomorphisms `ProEtale.CondensedRing.derivedPullIso` and the (Push) comparisons
`ProEtale.CondensedRing.derivedPushHom` in place of
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso` and
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`; the proofs are the same, with the
cube law `ProEtale.CondensedRing.derivedPullIso_cube` and the monoidality
`ProEtale.CondensedRing.comparisonCompatible_derivedPullIso` of (Pull). This applies to
`𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`, for which the (Push) comparisons are invertible on bounded below objects
along quasi-compact quasi-separated morphisms.

* `NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap_of_flat`: `T Π_{A,B}` and `Π_{T A, T B}`
  are isomorphic arrows if `derivedPushHom` is invertible at `Lε_M^* A`, `Lε_N^* B` and
  `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)`;
* `NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap_of_flat`: the same after restriction
  along any `h : W ⟶ Z'`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/- The statements below elaborate many derived functors and derived tensor products of module
objects, each of which needs the instances `PreservesColimit (Discrete.functor _) (tensorLeft _)`
of the module objects. These come from their monoidal closed structure: trying first to create the
colimits, and postponing the instance problems of the implicit categories more than once, take
about a third of the elaboration time of this file without changing the elaborated terms. -/
attribute [-instance] preservesColimit_of_createsColimit_and_hasColimit
set_option maxSynthPendingDepth 1

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

-- unifying the tensor products of the monoidal structure of `Lf^*` unfolds the derived categories
/-- **Extension of scalars and the monoidal structure of the derived pullback**: with
`T = L(Ext_a)`, its tensor comparison `m` and `P : Lf^* ⋙ T ≅ T ⋙ Lf^*`, the square
```
T (Lf^* K) ⊗ T (Lf^* M) ──P ⊗ P──▶ Lf^* T K ⊗ Lf^* T M ──μ──▶ Lf^* (T K ⊗ T M)
```
starting from `m : T (Lf^* K ⊗ Lf^* M) ⟶ T Lf^* K ⊗ T Lf^* M` agrees with
`T μ ≫ P ≫ Lf^* m`. -/
lemma extendScalars_tensorHom_comp_μ_leftDerivedUpperStar_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    ((derivedExtendScalarsTensorIso a X).hom.app (L((f)^*⟦Λ⟧).obj K)).app
        (L((f)^*⟦Λ⟧).obj M) ≫
        ((derivedPullIso a f).hom.app K ⊗ₘ
          (derivedPullIso a f).hom.app M) ≫
        Functor.LaxMonoidal.μ L((f)^*⟦Λ'⟧) _ _ =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          (Functor.LaxMonoidal.μ L((f)^*⟦Λ⟧) K M) ≫
        (derivedPullIso a f).hom.app (K ⊗ M) ≫
        L((f)^*⟦Λ'⟧).map (((derivedExtendScalarsTensorIso a Y).hom.app K).app M) :=
  map_μ_comp_of_map_δ_comp (derivedPullIso a f)
    (fun K M ↦ ((derivedExtendScalarsTensorIso a X).hom.app K).app M)
    (fun K M ↦ ((derivedExtendScalarsTensorIso a Y).hom.app K).app M)
    (fun K M ↦ (comparisonCompatible_derivedPullIso a f).tensorHom K M) K M

/-- **Extension of scalars and the lax tensor map of the derived pushforward**: with
`T = L(Ext_a)`, its tensor comparison `m` and the comparison `ρ : T Rj_* ⟶ Rj_* T`
(the mate of `ProEtale.CondensedRing.derivedPullIso`), the lax tensor maps
`μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` satisfy `T μ_j ≫ ρ ≫ Rj_* m = m ≫ (ρ ⊗ ρ) ≫ μ_j`. -/
lemma extendScalars_map_lowerStarTensorMap'_of_flat {U T : Scheme.{u}} (j : U ⟶ T)
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    (Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.map
        (lowerStarTensorMap' Λ j A B) ≫
        ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ j)
      (derivedUpperStarLowerStarAdjunction Λ' j) (derivedPullIso a j).inv)).app (A ⊗ B) ≫
        R((j)_*⟦Λ'⟧).map (((derivedExtendScalarsTensorIso a U).hom.app A).app B) =
      ((derivedExtendScalarsTensorIso a T).hom.app (R((j)_*⟦Λ⟧).obj A)).app
          (R((j)_*⟦Λ⟧).obj B) ≫
        (((mateEquiv (derivedUpperStarLowerStarAdjunction Λ j)
      (derivedUpperStarLowerStarAdjunction Λ' j) (derivedPullIso a j).inv)).app A ⊗ₘ
          ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ j)
      (derivedUpperStarLowerStarAdjunction Λ' j) (derivedPullIso a j).inv)).app B) ≫
        lowerStarTensorMap' Λ' j _ _ :=
  Adjunction.map_homEquiv_comp_mateEquiv_app (derivedUpperStarLowerStarAdjunction Λ j)
    (derivedUpperStarLowerStarAdjunction Λ' j) (derivedPullIso a j).symm
    (Functor.OplaxMonoidal.δ L((j)^*⟦Λ⟧)) (Functor.OplaxMonoidal.δ L((j)^*⟦Λ'⟧))
    (fun x y ↦ (Functor.OplaxMonoidal.δ_natural _ x y).symm) _
    (fun x y ↦ derivedExtendScalarsTensorIso_natural a U x y) _
    (fun K M ↦ (comparisonCompatible_derivedPullIso a j).tensorHom K M) A B

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}}

/-- The comparison `T Ψ_M A ⟶ Ψ_M (T A)` of the nearby cycles `Ψ_M = Li^* Rj_* Lε^*` with the
derived extension of scalars `T = L(Ext_a)`: the (Pull) isomorphisms for `i` and `ε` and the
comparison `ρ : T Rj_* ⟶ Rj_* T` (the mate of `ProEtale.CondensedRing.derivedPullIso`).
It is an isomorphism when `ρ` is one at `Lε^* A`. -/
noncomputable def extendScalarsComparisonOfFlat (M : NearbyCyclesModel X X')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.obj ((M.nearbyCycles Λ).obj A) ⟶
      (M.nearbyCycles Λ').obj ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A) :=
  (derivedPullIso a M.i).hom.app _ ≫
    L((M.i)^*⟦Λ'⟧).map (((mateEquiv (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j) (derivedPullIso a M.j).inv)).app _ ≫
      R((M.j)_*⟦Λ'⟧).map ((derivedPullIso a M.ε).hom.app A))

variable {Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

-- the comparison of the pasted squares with the pullback exchanges unfolds the nearby cycles
set_option maxRecDepth 10000 in
/-- **The pullback exchange under a flat change of coefficients**: for a morphism of models
`φ : M ⟶ N` and `T = L(Ext_a)`, the square
```
T Lf'^* Ψ_N A ──T α_φ──▶ T Ψ_M Lf^* A ──Φ──▶ Ψ_M T Lf^* A ──P──▶ Ψ_M Lf^* T A
      │P                                                              ‖
Lf'^* T Ψ_N A ──Lf'^* Φ──▶ Lf'^* Ψ_N T A ─────────α_φ──────────▶ Ψ_M Lf^* T A
```
commutes, where `Φ` is `NearbyCyclesModel.extendScalarsComparisonOfFlat`. -/
theorem Hom.extendScalars_map_pullbackExchange_app_of_flat (φ : M.Hom N f f')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map
        ((φ.pullbackExchange Λ).app A) ≫ M.extendScalarsComparisonOfFlat a (L((f)^*⟦Λ⟧).obj A) ≫
        (M.nearbyCycles Λ').map ((derivedPullIso a f).hom.app A) =
      (derivedPullIso a f').hom.app _ ≫
        L((f')^*⟦Λ'⟧).map (N.extendScalarsComparisonOfFlat a A) ≫
        (φ.pullbackExchange Λ').app
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj A) := by
  have hi := derivedPullIso_cube a (derivedPullIsoCompCoherence a) φ.commSq_i
  have hj := derivedPullIso_cube a (derivedPullIsoCompCoherence a) φ.commSq_j
  have hε := derivedPullIso_cube a (derivedPullIsoCompCoherence a) φ.commSq_ε
  have hβ := mateEquiv_app_cube (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (derivedUpperStarLowerStarAdjunction Λ' N.j)
    (derivedUpperStarLowerStarAdjunction Λ' M.j) (pullbackSquareComparison Λ φ.commSq_j).hom
    (pullbackSquareComparison Λ' φ.commSq_j).hom (derivedPullIso a N.j).inv
    (derivedPullIso a M.j).inv (derivedPullIso a φ.total).inv
    (derivedPullIso a φ.generic).inv hj
  have key := map_exchange_comp_eq (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (pullbackSquareComparison Λ' φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' N.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j)
      (pullbackSquareComparison Λ' φ.commSq_j).hom)
    (pullbackSquareComparison Λ' φ.commSq_ε).hom
    (derivedPullIso a f') (derivedPullIso a N.i)
    (derivedPullIso a M.i) (derivedPullIso a φ.total)
    (derivedPullIso a φ.generic) (derivedPullIso a N.ε)
    (derivedPullIso a M.ε) (derivedPullIso a f)
    ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ' N.j) (derivedPullIso a N.j).inv))
    ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j) (derivedPullIso a M.j).inv))
    hi hβ hε (φ.pullbackExchange Λ) rfl (φ.pullbackExchange Λ') rfl A
  unfold extendScalarsComparisonOfFlat
  convert key using 2 <;> rfl

-- the comparison with the lax tensor maps of nearby cycles unfolds the derived categories
set_option maxRecDepth 10000 in
/-- **The lax tensor map of nearby cycles under a flat change of coefficients**: with
`T = L(Ext_a)`, its tensor comparison `m` and `Φ = NearbyCyclesModel.extendScalarsComparisonOfFlat`,
`T μ_Ψ ≫ Φ ≫ Ψ m = m ≫ (Φ ⊗ Φ) ≫ μ_Ψ`. -/
theorem extendScalars_map_tensorMap_of_flat (M : NearbyCyclesModel X X')
    (U V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map (M.tensorMap Λ U V) ≫
        M.extendScalarsComparisonOfFlat a (U ⊗ V) ≫
        (M.nearbyCycles Λ').map (((derivedExtendScalarsTensorIso a X).hom.app U).app V) =
      ((derivedExtendScalarsTensorIso a X').hom.app ((M.nearbyCycles Λ).obj U)).app
          ((M.nearbyCycles Λ).obj V) ≫
        (M.extendScalarsComparisonOfFlat a U ⊗ₘ M.extendScalarsComparisonOfFlat a V) ≫
        M.tensorMap Λ' _ _ := by
  have key := map_laxComp_comp_eq (derivedPullIso a M.ε)
    (derivedPullIso a M.i) ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j) (derivedPullIso a M.j).inv))
    (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ⟧)) (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ'⟧))
    (lowerStarTensorMap' Λ M.j) (lowerStarTensorMap' Λ' M.j)
    (Functor.LaxMonoidal.μ L((M.i)^*⟦Λ⟧)) (Functor.LaxMonoidal.μ L((M.i)^*⟦Λ'⟧))
    (fun x y ↦ lowerStarTensorMap'_natural Λ' M.j x y)
    (fun x y ↦ Functor.LaxMonoidal.μ_natural _ x y)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a X).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a M.generic).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a M.total).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a X').hom.app K).app L)
    (extendScalars_tensorHom_comp_μ_leftDerivedUpperStar_of_flat a M.ε)
    (fun K L ↦ (extendScalars_map_lowerStarTensorMap'_of_flat a M.j K L).symm)
    (extendScalars_tensorHom_comp_μ_leftDerivedUpperStar_of_flat a M.i) U V
  convert key using 2 <;> rfl

/-- The comparison `Φ : T Ψ_M A ⟶ Ψ_M (T A)` is an isomorphism if `ρ : T Rj_* ⟶ Rj_* T` is one
at `Lε^* A`. -/
lemma isIso_extendScalarsComparisonOfFlat (M : NearbyCyclesModel X X')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso (((mateEquiv (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j) (derivedPullIso a M.j).inv)).app
        (L((M.ε)^*⟦Λ⟧).obj A))) :
    IsIso (M.extendScalarsComparisonOfFlat a A) := by
  rw [extendScalarsComparisonOfFlat]
  infer_instance

variable {Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

-- the composite of the squares is matched against the Künneth maps
/-- **The Künneth map of nearby cycles under a flat change of coefficients**, as a commutative
square: with `T = L(Ext_a)`, its tensor comparison `m`, the (Pull) isomorphisms `P` and the
comparisons `Φ = NearbyCyclesModel.extendScalarsComparisonOfFlat`, the square
```
T (Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B) ──T Π──▶ T Ψ_P (Lf₁^* A ⊗ Lf₂^* B)
        │ m ≫ (P ≫ Lf₁'^* Φ) ⊗ (P ≫ Lf₂'^* Φ)        │ Φ ≫ Ψ_P (m ≫ P ⊗ P)
Lf₁'^* Ψ_M T A ⊗ Lf₂'^* Ψ_N T B ──Π──▶ Ψ_P (Lf₁^* T A ⊗ Lf₂^* T B)
```
commutes. -/
theorem extendScalars_map_kunnethMap_of_flat (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Mod.extendScalars (coefficientMap a Z')).leftDerivedFunctor.map
        (kunnethMap Λ φ₁ φ₂ A B) ≫
        (P.extendScalarsComparisonOfFlat a (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
          (P.nearbyCycles Λ').map (((derivedExtendScalarsTensorIso a Z).hom.app
            (L((f₁)^*⟦Λ⟧).obj A)).app (L((f₂)^*⟦Λ⟧).obj B))) ≫
          (P.nearbyCycles Λ').map ((derivedPullIso a f₁).hom.app A ⊗ₘ
            (derivedPullIso a f₂).hom.app B) =
      (((derivedExtendScalarsTensorIso a Z').hom.app _).app _ ≫
        (((derivedPullIso a f₁').hom.app _ ≫
            L((f₁')^*⟦Λ'⟧).map (M.extendScalarsComparisonOfFlat a A)) ⊗ₘ
          ((derivedPullIso a f₂').hom.app _ ≫
            L((f₂')^*⟦Λ'⟧).map (N.extendScalarsComparisonOfFlat a B)))) ≫
        kunnethMap Λ' φ₁ φ₂ ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B) :=
  (map_tensorHom_comp_comp_eq _ _ (fun x y ↦ derivedExtendScalarsTensorIso_natural a Z' x y) _ _
    _ _ _ _ _ _ _ _ _
    ((Hom.extendScalars_map_pullbackExchange_app_of_flat a φ₁ A).trans (Category.assoc _ _ _).symm)
    ((Hom.extendScalars_map_pullbackExchange_app_of_flat a φ₂ B).trans (Category.assoc _ _ _).symm)
    (comp_tensorHom_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ _ _
      (extendScalars_map_tensorMap_of_flat a P _ _) (tensorMap_natural Λ' P _ _))).trans
    (Category.assoc _ _ _).symm

-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The Künneth map of nearby cycles under a flat change of coefficients**: for `a : Λ ⟶ Λ'` with
derived extension of scalars `T = L(Ext_a)`, if the comparisons `ρ : T Rj_* ⟶ Rj_* T`
(`ProEtale.CondensedRing.derivedPushHom`) are invertible at `Lε_M^* A`,
`Lε_N^* B` and `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)`, then `T Π_{A,B}` and `Π_{T A, T B}` are isomorphic
arrows. -/
theorem nonempty_arrowIso_map_kunnethMap_of_flat (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hA : IsIso ((derivedPushHom a M.j).app (L((M.ε)^*⟦Λ⟧).obj A)))
    (hB : IsIso ((derivedPushHom a N.j).app (L((N.ε)^*⟦Λ⟧).obj B)))
    (hAB : IsIso ((derivedPushHom a P.j).app
      (L((P.ε)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z')).leftDerivedFunctor.map
        (kunnethMap Λ φ₁ φ₂ A B)) ≅
      Arrow.mk (kunnethMap Λ' φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B))) := by
  rw [derivedPushHom_eq_mateEquiv] at hA hB hAB
  have := isIso_extendScalarsComparisonOfFlat a M A hA
  have := isIso_extendScalarsComparisonOfFlat a N B hB
  have := isIso_extendScalarsComparisonOfFlat a P _ hAB
  have h := extendScalars_map_kunnethMap_of_flat a φ₁ φ₂ A B
  have k := nonempty_arrowIso_of_comp_eq h (by infer_instance) (by infer_instance)
  exact k

-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The restricted Künneth map under a flat change of coefficients**: under the hypotheses of
`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap_of_flat`, for every `h : W ⟶ Z'`,
`T Lh^* Π_{A,B}` and `Lh^* Π_{T A, T B}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_kunnethMap_of_flat (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {W : Scheme.{u}} (h : W ⟶ Z')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hA : IsIso ((derivedPushHom a M.j).app (L((M.ε)^*⟦Λ⟧).obj A)))
    (hB : IsIso ((derivedPushHom a N.j).app (L((N.ε)^*⟦Λ⟧).obj B)))
    (hAB : IsIso ((derivedPushHom a P.j).app
      (L((P.ε)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a W)).leftDerivedFunctor.map
        (L((h)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) ≅
      Arrow.mk (L((h)^*⟦Λ'⟧).map (kunnethMap Λ' φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B)))) :=
  nonempty_arrowIso_map_map_of_iso (F := L((h)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a W)))
    (F' := L(Mod.extendScalars (coefficientMap a Z'))) (G' := L((h)^*⟦Λ'⟧))
    (derivedPullIso a h) _
    (nonempty_arrowIso_map_kunnethMap_of_flat a φ₁ φ₂ A B hA hB hAB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
