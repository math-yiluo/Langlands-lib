/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeSquares
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted

/-!

# The Künneth map of nearby cycles under a change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and
`T = L(Ext_a) = Λ' ⊗ᴸ_Λ -` the derived extension of scalars, with its tensor comparison
`m : T (K ⊗ᴸ M) ≅ T K ⊗ᴸ T M` (`ProEtale.CondensedRing.derivedExtendScalarsTensorIso`), the
(Pull) isomorphisms `P_f : Lf^* ⋙ T ≅ T ⋙ Lf^*`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`) and the (Push) comparisons
`ρ_h : T Rh_* ⟶ Rh_* T`, the mates of `P_h⁻¹`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`).

For a model `M`, `Φ = P_i ≫ Li^* (ρ_j ≫ Rj_* P_ε) : T Ψ_M A ⟶ Ψ_M (T A)`
(`NearbyCyclesModel.extendScalarsComparison`) compares the nearby cycles with the change of
coefficients; it is invertible when `ρ_j` is invertible at `Lε^* A`. We show:

* the lax tensor map `μ_j` of `Rj_*` commutes with `T` through `ρ_j` and `m`
  (`ProEtale.CondensedRing.extendScalars_map_lowerStarTensorMap'`): this is the mate of the
  monoidal compatibility of `P_j`
  (`ProEtale.CondensedRing.comparisonCompatible_derivedUpperStarExtendScalarsIso`),
  by `CategoryTheory.Adjunction.map_homEquiv_comp_mateEquiv_app`;
* the pullback exchange of a morphism of models commutes with `T` through `Φ` and `P`
  (`NearbyCyclesModel.Hom.extendScalars_map_pullbackExchange_app`), by the cube laws of the
  three exchanges it is pasted from (`CategoryTheory.map_exchange_comp_eq`);
* the lax tensor map `μ_Ψ` of nearby cycles commutes with `T` through `Φ` and `m`
  (`NearbyCyclesModel.extendScalars_map_tensorMap`, `CategoryTheory.map_laxComp_comp_eq`);
* hence the **Künneth map** `Π_{A,B}` commutes with `T`
  (`NearbyCyclesModel.extendScalars_map_kunnethMap`), and `T Π_{A,B}` and `Π_{T A, T B}` are
  isomorphic arrows when `ρ_j` is invertible at `Lε_M^* A`, `Lε_N^* B` and
  `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)` (`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap`), also after
  restriction along any `h : W ⟶ Z'` (`NearbyCyclesModel.nonempty_arrowIso_map_map_kunnethMap`).

The analogue for a flat `a`, with `ProEtale.CondensedRing.derivedPullIso` and
`ProEtale.CondensedRing.derivedPushHom`, is
`WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeFlat`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

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

/-- The tensor comparison `T (K ⊗ᴸ M) ⟶ T K ⊗ᴸ T M` of the derived extension of scalars is
natural. -/
lemma derivedExtendScalarsTensorIso_natural (X : Scheme.{u})
    {K K' M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (x : K ⟶ K') (y : M ⟶ M') :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map (x ⊗ₘ y) ≫
        ((derivedExtendScalarsTensorIso a X).hom.app K').app M' =
      ((derivedExtendScalarsTensorIso a X).hom.app K).app M ≫
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map x ⊗ₘ
          (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map y) :=
  Functor.map_tensorHom_comp_app_app (derivedExtendScalarsTensorIso a X).hom x y

-- unifying the tensor products of the monoidal structure of `Lf^*` unfolds the derived categories
/-- **Extension of scalars and the monoidal structure of the derived pullback**: with
`T = L(Ext_a)`, its tensor comparison `m` and `P : Lf^* ⋙ T ≅ T ⋙ Lf^*`, the square
```
T (Lf^* K) ⊗ T (Lf^* M) ──P ⊗ P──▶ Lf^* T K ⊗ Lf^* T M ──μ──▶ Lf^* (T K ⊗ T M)
```
starting from `m : T (Lf^* K ⊗ Lf^* M) ⟶ T Lf^* K ⊗ T Lf^* M` agrees with
`T μ ≫ P ≫ Lf^* m`. -/
lemma extendScalars_tensorHom_comp_μ_leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    ((derivedExtendScalarsTensorIso a X).hom.app (L((f)^*⟦Λ⟧).obj K)).app
        (L((f)^*⟦Λ⟧).obj M) ≫
        ((derivedUpperStarExtendScalarsIso a f).hom.app K ⊗ₘ
          (derivedUpperStarExtendScalarsIso a f).hom.app M) ≫
        Functor.LaxMonoidal.μ L((f)^*⟦Λ'⟧) _ _ =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          (Functor.LaxMonoidal.μ L((f)^*⟦Λ⟧) K M) ≫
        (derivedUpperStarExtendScalarsIso a f).hom.app (K ⊗ M) ≫
        L((f)^*⟦Λ'⟧).map (((derivedExtendScalarsTensorIso a Y).hom.app K).app M) :=
  map_μ_comp_of_map_δ_comp (derivedUpperStarExtendScalarsIso a f)
    (fun K M ↦ ((derivedExtendScalarsTensorIso a X).hom.app K).app M)
    (fun K M ↦ ((derivedExtendScalarsTensorIso a Y).hom.app K).app M)
    (fun K M ↦ (comparisonCompatible_derivedUpperStarExtendScalarsIso a f).tensorHom K M) K M

/-- **Extension of scalars and the lax tensor map of the derived pushforward**: with
`T = L(Ext_a)`, its tensor comparison `m` and the comparison `ρ : T Rj_* ⟶ Rj_* T`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`), the lax tensor maps
`μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` satisfy `T μ_j ≫ ρ ≫ Rj_* m = m ≫ (ρ ⊗ ρ) ≫ μ_j`. -/
lemma extendScalars_map_lowerStarTensorMap' {U T : Scheme.{u}} (j : U ⟶ T)
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    (Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor.map
        (lowerStarTensorMap' Λ j A B) ≫
        (derivedUpperStarExtendScalarsPushHom a j).app (A ⊗ B) ≫
        R((j)_*⟦Λ'⟧).map (((derivedExtendScalarsTensorIso a U).hom.app A).app B) =
      ((derivedExtendScalarsTensorIso a T).hom.app (R((j)_*⟦Λ⟧).obj A)).app
          (R((j)_*⟦Λ⟧).obj B) ≫
        ((derivedUpperStarExtendScalarsPushHom a j).app A ⊗ₘ
          (derivedUpperStarExtendScalarsPushHom a j).app B) ≫
        lowerStarTensorMap' Λ' j _ _ :=
  Adjunction.map_homEquiv_comp_mateEquiv_app (derivedUpperStarLowerStarAdjunction Λ j)
    (derivedUpperStarLowerStarAdjunction Λ' j) (derivedUpperStarExtendScalarsIso a j).symm
    (Functor.OplaxMonoidal.δ L((j)^*⟦Λ⟧)) (Functor.OplaxMonoidal.δ L((j)^*⟦Λ'⟧))
    (fun x y ↦ (Functor.OplaxMonoidal.δ_natural _ x y).symm) _
    (fun x y ↦ derivedExtendScalarsTensorIso_natural a U x y) _
    (fun K M ↦ (comparisonCompatible_derivedUpperStarExtendScalarsIso a j).tensorHom K M) A B

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}}

/-- The comparison `T Ψ_M A ⟶ Ψ_M (T A)` of the nearby cycles `Ψ_M = Li^* Rj_* Lε^*` with the
derived extension of scalars `T = L(Ext_a)`: the (Pull) isomorphisms for `i` and `ε` and the
comparison `ρ : T Rj_* ⟶ Rj_* T` (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`).
It is an isomorphism when `ρ` is one at `Lε^* A`. -/
noncomputable def extendScalarsComparison (M : NearbyCyclesModel X X')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.obj ((M.nearbyCycles Λ).obj A) ⟶
      (M.nearbyCycles Λ').obj ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A) :=
  (derivedUpperStarExtendScalarsIso a M.i).hom.app _ ≫
    L((M.i)^*⟦Λ'⟧).map ((derivedUpperStarExtendScalarsPushHom a M.j).app _ ≫
      R((M.j)_*⟦Λ'⟧).map ((derivedUpperStarExtendScalarsIso a M.ε).hom.app A))

variable {Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

-- the comparison of the pasted squares with the pullback exchanges unfolds the nearby cycles
/-- **The pullback exchange under a change of coefficients**: for a morphism of models
`φ : M ⟶ N` and `T = L(Ext_a)`, the square
```
T Lf'^* Ψ_N A ──T α_φ──▶ T Ψ_M Lf^* A ──Φ──▶ Ψ_M T Lf^* A ──P──▶ Ψ_M Lf^* T A
      │P                                                              ‖
Lf'^* T Ψ_N A ──Lf'^* Φ──▶ Lf'^* Ψ_N T A ─────────α_φ──────────▶ Ψ_M Lf^* T A
```
commutes, where `Φ` is `NearbyCyclesModel.extendScalarsComparison`. -/
theorem Hom.extendScalars_map_pullbackExchange_app (φ : M.Hom N f f')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map
        ((φ.pullbackExchange Λ).app A) ≫ M.extendScalarsComparison a (L((f)^*⟦Λ⟧).obj A) ≫
        (M.nearbyCycles Λ').map ((derivedUpperStarExtendScalarsIso a f).hom.app A) =
      (derivedUpperStarExtendScalarsIso a f').hom.app _ ≫
        L((f')^*⟦Λ'⟧).map (N.extendScalarsComparison a A) ≫
        (φ.pullbackExchange Λ').app
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj A) := by
  have hi := derivedUpperStarExtendScalarsIso_cube a φ.commSq_i
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
  have hj := derivedUpperStarExtendScalarsIso_cube a φ.commSq_j
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
  have hε := derivedUpperStarExtendScalarsIso_cube a φ.commSq_ε
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
    (derivedUpperStarExtendScalarsIsoCompCoherence a _ _)
  have hβ := mateEquiv_app_cube (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (derivedUpperStarLowerStarAdjunction Λ' N.j)
    (derivedUpperStarLowerStarAdjunction Λ' M.j) (pullbackSquareComparison Λ φ.commSq_j).hom
    (pullbackSquareComparison Λ' φ.commSq_j).hom (derivedUpperStarExtendScalarsIso a N.j).inv
    (derivedUpperStarExtendScalarsIso a M.j).inv (derivedUpperStarExtendScalarsIso a φ.total).inv
    (derivedUpperStarExtendScalarsIso a φ.generic).inv hj
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
    (derivedUpperStarExtendScalarsIso a f') (derivedUpperStarExtendScalarsIso a N.i)
    (derivedUpperStarExtendScalarsIso a M.i) (derivedUpperStarExtendScalarsIso a φ.total)
    (derivedUpperStarExtendScalarsIso a φ.generic) (derivedUpperStarExtendScalarsIso a N.ε)
    (derivedUpperStarExtendScalarsIso a M.ε) (derivedUpperStarExtendScalarsIso a f)
    (derivedUpperStarExtendScalarsPushHom a N.j) (derivedUpperStarExtendScalarsPushHom a M.j)
    hi hβ hε (φ.pullbackExchange Λ) rfl (φ.pullbackExchange Λ') rfl A
  unfold extendScalarsComparison
  convert key using 2 <;> rfl

-- the comparison with the lax tensor maps of nearby cycles unfolds the derived categories
set_option maxRecDepth 10000 in
/-- **The lax tensor map of nearby cycles under a change of coefficients**: with
`T = L(Ext_a)`, its tensor comparison `m` and `Φ = NearbyCyclesModel.extendScalarsComparison`,
`T μ_Ψ ≫ Φ ≫ Ψ m = m ≫ (Φ ⊗ Φ) ≫ μ_Ψ`. -/
theorem extendScalars_map_tensorMap (M : NearbyCyclesModel X X')
    (U V : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map (M.tensorMap Λ U V) ≫
        M.extendScalarsComparison a (U ⊗ V) ≫
        (M.nearbyCycles Λ').map (((derivedExtendScalarsTensorIso a X).hom.app U).app V) =
      ((derivedExtendScalarsTensorIso a X').hom.app ((M.nearbyCycles Λ).obj U)).app
          ((M.nearbyCycles Λ).obj V) ≫
        (M.extendScalarsComparison a U ⊗ₘ M.extendScalarsComparison a V) ≫
        M.tensorMap Λ' _ _ := by
  have key := map_laxComp_comp_eq (derivedUpperStarExtendScalarsIso a M.ε)
    (derivedUpperStarExtendScalarsIso a M.i) (derivedUpperStarExtendScalarsPushHom a M.j)
    (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ⟧)) (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ'⟧))
    (lowerStarTensorMap' Λ M.j) (lowerStarTensorMap' Λ' M.j)
    (Functor.LaxMonoidal.μ L((M.i)^*⟦Λ⟧)) (Functor.LaxMonoidal.μ L((M.i)^*⟦Λ'⟧))
    (fun x y ↦ lowerStarTensorMap'_natural Λ' M.j x y)
    (fun x y ↦ Functor.LaxMonoidal.μ_natural _ x y)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a X).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a M.generic).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a M.total).hom.app K).app L)
    (fun K L ↦ ((derivedExtendScalarsTensorIso a X').hom.app K).app L)
    (extendScalars_tensorHom_comp_μ_leftDerivedUpperStar a M.ε)
    (fun K L ↦ (extendScalars_map_lowerStarTensorMap' a M.j K L).symm)
    (extendScalars_tensorHom_comp_μ_leftDerivedUpperStar a M.i) U V
  convert key using 2 <;> rfl

/-- The comparison `Φ : T Ψ_M A ⟶ Ψ_M (T A)` is an isomorphism if `ρ : T Rj_* ⟶ Rj_* T` is one
at `Lε^* A`. -/
lemma isIso_extendScalarsComparison (M : NearbyCyclesModel X X')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso ((derivedUpperStarExtendScalarsPushHom a M.j).app (L((M.ε)^*⟦Λ⟧).obj A))) :
    IsIso (M.extendScalarsComparison a A) := by
  rw [extendScalarsComparison]
  infer_instance

variable {Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

-- the composite of the squares is matched against the Künneth maps
/-- **The Künneth map of nearby cycles under a change of coefficients**, as a commutative
square: with `T = L(Ext_a)`, its tensor comparison `m`, the (Pull) isomorphisms `P` and the
comparisons `Φ = NearbyCyclesModel.extendScalarsComparison`, the square
```
T (Lf₁'^* Ψ_M A ⊗ Lf₂'^* Ψ_N B) ──T Π──▶ T Ψ_P (Lf₁^* A ⊗ Lf₂^* B)
        │ m ≫ (P ≫ Lf₁'^* Φ) ⊗ (P ≫ Lf₂'^* Φ)        │ Φ ≫ Ψ_P (m ≫ P ⊗ P)
Lf₁'^* Ψ_M T A ⊗ Lf₂'^* Ψ_N T B ──Π──▶ Ψ_P (Lf₁^* T A ⊗ Lf₂^* T B)
```
commutes. -/
theorem extendScalars_map_kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (Mod.extendScalars (coefficientMap a Z')).leftDerivedFunctor.map
        (kunnethMap Λ φ₁ φ₂ A B) ≫
        (P.extendScalarsComparison a (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫
          (P.nearbyCycles Λ').map (((derivedExtendScalarsTensorIso a Z).hom.app
            (L((f₁)^*⟦Λ⟧).obj A)).app (L((f₂)^*⟦Λ⟧).obj B))) ≫
          (P.nearbyCycles Λ').map ((derivedUpperStarExtendScalarsIso a f₁).hom.app A ⊗ₘ
            (derivedUpperStarExtendScalarsIso a f₂).hom.app B) =
      (((derivedExtendScalarsTensorIso a Z').hom.app _).app _ ≫
        (((derivedUpperStarExtendScalarsIso a f₁').hom.app _ ≫
            L((f₁')^*⟦Λ'⟧).map (M.extendScalarsComparison a A)) ⊗ₘ
          ((derivedUpperStarExtendScalarsIso a f₂').hom.app _ ≫
            L((f₂')^*⟦Λ'⟧).map (N.extendScalarsComparison a B)))) ≫
        kunnethMap Λ' φ₁ φ₂ ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B) :=
  (map_tensorHom_comp_comp_eq _ _ (fun x y ↦ derivedExtendScalarsTensorIso_natural a Z' x y) _ _
    _ _ _ _ _ _ _ _ _
    ((Hom.extendScalars_map_pullbackExchange_app a φ₁ A).trans (Category.assoc _ _ _).symm)
    ((Hom.extendScalars_map_pullbackExchange_app a φ₂ B).trans (Category.assoc _ _ _).symm)
    (comp_tensorHom_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ _ _
      (extendScalars_map_tensorMap a P _ _) (tensorMap_natural Λ' P _ _))).trans
    (Category.assoc _ _ _).symm

-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The Künneth map of nearby cycles under a change of coefficients**: for `a : Λ ⟶ Λ'` with
derived extension of scalars `T = L(Ext_a)`, if the comparisons `ρ : T Rj_* ⟶ Rj_* T`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`) are invertible at `Lε_M^* A`,
`Lε_N^* B` and `Lε_P^* (Lf₁^* A ⊗ Lf₂^* B)`, then `T Π_{A,B}` and `Π_{T A, T B}` are isomorphic
arrows. -/
theorem nonempty_arrowIso_map_kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hA : IsIso ((derivedUpperStarExtendScalarsPushHom a M.j).app (L((M.ε)^*⟦Λ⟧).obj A)))
    (hB : IsIso ((derivedUpperStarExtendScalarsPushHom a N.j).app (L((N.ε)^*⟦Λ⟧).obj B)))
    (hAB : IsIso ((derivedUpperStarExtendScalarsPushHom a P.j).app
      (L((P.ε)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z')).leftDerivedFunctor.map
        (kunnethMap Λ φ₁ φ₂ A B)) ≅
      Arrow.mk (kunnethMap Λ' φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B))) := by
  have := isIso_extendScalarsComparison a M A hA
  have := isIso_extendScalarsComparison a N B hB
  have := isIso_extendScalarsComparison a P _ hAB
  have h := extendScalars_map_kunnethMap a φ₁ φ₂ A B
  have k := nonempty_arrowIso_of_comp_eq h (by infer_instance) (by infer_instance)
  exact k

-- elaborating the Künneth maps of the derived categories of module objects is slow
/-- **The restricted Künneth map under a change of coefficients**: under the hypotheses of
`NearbyCyclesModel.nonempty_arrowIso_map_kunnethMap`, for every `h : W ⟶ Z'`, `T Lh^* Π_{A,B}`
and `Lh^* Π_{T A, T B}` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_map_kunnethMap (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {W : Scheme.{u}} (h : W ⟶ Z')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hA : IsIso ((derivedUpperStarExtendScalarsPushHom a M.j).app (L((M.ε)^*⟦Λ⟧).obj A)))
    (hB : IsIso ((derivedUpperStarExtendScalarsPushHom a N.j).app (L((N.ε)^*⟦Λ⟧).obj B)))
    (hAB : IsIso ((derivedUpperStarExtendScalarsPushHom a P.j).app
      (L((P.ε)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a W)).leftDerivedFunctor.map
        (L((h)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) ≅
      Arrow.mk (L((h)^*⟦Λ'⟧).map (kunnethMap Λ' φ₁ φ₂
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj A)
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj B)))) :=
  nonempty_arrowIso_map_map_of_iso (F := L((h)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a W)))
    (F' := L(Mod.extendScalars (coefficientMap a Z'))) (G' := L((h)^*⟦Λ'⟧))
    (derivedUpperStarExtendScalarsIso a h) _
    (nonempty_arrowIso_map_kunnethMap a φ₁ φ₂ A B hA hB hAB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
