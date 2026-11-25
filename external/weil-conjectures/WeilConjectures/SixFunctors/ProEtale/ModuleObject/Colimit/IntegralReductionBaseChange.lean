/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionProperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac

/-!
# Reduction modulo `ℓⁿ` and the base change morphism of bounded constructible complexes

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧` for the reduction modulo `ℓⁿ`
(`ProEtale.boundedConstructibleIntegersModPowReduction`). For a commutative square of separated
`k`-schemes of finite type
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
the pullback comparisons `Lh^* ⋙ red ≅ red ⋙ Lh^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso`) are compatible
with the pullback square comparisons `Lf'^* Lg^* ≅ Lg'^* Lf^*` on both sides
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso_cube`): this is
the coherence `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoCompCoherence` of the
ambient (Pull) isomorphisms, restricted to bounded constructible complexes.

The comparison `Rh_* ⋙ red ⟶ red ⋙ Rh_*` of the reduction with the pushforwards is the mate of
the pullback comparison
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`), so the cube law
of mates (`CategoryTheory.mateEquiv_app_cube`) shows that the reduction carries the base change
morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*` with `𝒪_E`-coefficients to the one with
`𝒪_E ⧸ ℓⁿ`-coefficients
(`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReduction_baseChange`; blueprint
`proposition-compatibility-purity-base-change`, direct images).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [TopologicalSpace.NoetherianSpace X.left] [TopologicalSpace.NoetherianSpace Y.left]
  [TopologicalSpace.NoetherianSpace X'.left] [TopologicalSpace.NoetherianSpace Y'.left]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The inverse of the composition isomorphism of the restricted derived pullbacks is the one of
the ambient derived pullbacks. -/
private lemma boundedConstructibleUpperStarComp_inv_app_hom_aux
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A B C : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (a : A ⟶ B) (b : B ⟶ C) (K : Dᵇc(C.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarComp Λ ℓ a b).inv.app K).hom =
      (leftDerivedUpperStarComp Λ a.left b.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- The underlying morphism of an `eqToHom` in a full subcategory. -/
private lemma fullSubcategory_eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {A₁ A₂ : P.FullSubcategory} (h : A₁ = A₂) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

/-- The restricted reduction modulo `ℓⁿ` is the derived extension of scalars on morphisms. -/
private lemma boundedConstructibleIntegersModPowReduction_map_hom (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {K L : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (φ : K ⟶ L) :
    ((boundedConstructibleIntegersModPowReduction Z ℓ E n).map φ).hom =
      (Mod.extendScalars (integersModPowReduction Z ℓ E n)).leftDerivedFunctor.map φ.hom :=
  rfl

set_option hygiene false in
/-- Proves the cube condition `boundedConstructibleUpperStarIntegersModPowReductionIso_cube` for
the square `sq` at the object `M` (in the context of this file): the restrictions to the ambient
derived categories are rewritten to the ambient (Pull) isomorphisms and pullback comparisons,
where the condition is `derivedUpperStarExtendScalarsIso_cube`. The reduction is applied to the
`eqToHom` of the pullback square comparison as an `eqToHom` (`eqToHom_map`) before restricting:
restricting it first produces a proof term which the kernel checks only very slowly. -/
local macro "integersModPowReduction_cube_tac" : tactic => `(tactic| (
  have H := derivedUpperStarExtendScalarsIso_cube
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
    (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)
    (derivedUpperStarExtendScalarsIsoCompCoherence _ _ _)
    (derivedUpperStarExtendScalarsIsoCompCoherence _ _ _) M.obj
  simp only [pullbackSquareComparison_hom_app, Functor.map_comp, eqToHom_map,
    Category.assoc] at H
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom,
    boundedConstructiblePullbackSquareComparison_hom_app,
    boundedConstructibleUpperStarComp_hom_app_hom, Functor.map_comp, eqToHom_map]
  simp only [boundedConstructibleIntegersModPowReduction_map_hom,
    boundedConstructibleUpperStarComp_inv_app_hom_aux, fullSubcategory_eqToHom_hom,
    boundedConstructibleUpperStarComp_hom_app_hom, Category.assoc]
  unfold integersModPowReductionUpperStarIso
  exact H))

/-- **The reduction modulo `ℓⁿ` is compatible with the pullback square comparisons**: for a
commutative square `g' ≫ f = f' ≫ g`, the two composites
`Lf'^* Lg^* red M ⟶ red Lg'^* Lf^* M` built from the pullback comparisons of the reduction and
the pullback square comparisons agree. This is the cube condition of
`CategoryTheory.mateEquiv_app_cube`. -/
lemma boundedConstructibleUpperStarIntegersModPowReductionIso_cube (sq : CommSq g' f' f g)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f').map
        ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g).inv.app M) ≫
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).obj M) ≫
      (boundedConstructibleIntegersModPowReduction X'.left ℓ E n).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq).hom.app M) =
    (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
        sq).hom.app ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M) ≫
      (boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ g').map
        ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv.app M) ≫
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M) := by
  integersModPowReduction_cube_tac

/-- **The reduction modulo `ℓⁿ` carries the base change morphism to the base change morphism**:
for a commutative square `g' ≫ f = f' ≫ g` and `K ∈ Dᵇc(X)⟦𝒪_E⟧`,
```
(Pull_g)⁻¹ (Rf_* K) ≫ red_{Y'} (BC^{𝒪_E}_K) ≫ γ_{f'} (Lg'^* K) =
  Lg^* (γ_f K) ≫ BC^{𝒪_E ⧸ ℓⁿ}_{red_X K} ≫ Rf'_* ((Pull_{g'})⁻¹ K)
```
as morphisms `Lg^* red_Y Rf_* K ⟶ Rf'_* red_{X'} Lg'^* K`, where `Pull_h : Lh^* ⋙ red ≅ red ⋙ Lh^*`
are the pullback comparisons (`boundedConstructibleUpperStarIntegersModPowReductionIso`),
`γ_h = mateEquiv (Lh^* ⊣ Rh_*) (Lh^* ⊣ Rh_*) Pull_h⁻¹ : Rh_* ⋙ red ⟶ red ⋙ Rh_*` (by definition
`boundedConstructibleLowerStarIntegersModPowReduction`) and
`BC = mateEquiv (Lf^* ⊣ Rf_*) (Lf'^* ⊣ Rf'_*) θ_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` are the base
change morphisms, the mates of the pullback square comparisons `θ_sq`.

This is `CategoryTheory.mateEquiv_app_cube` for the cube condition
`boundedConstructibleUpperStarIntegersModPowReductionIso_cube`. The statement is the type of the
proof (`type_of%`), with `γ` written as a `mateEquiv`: a hand-written statement elaborates the
instance arguments of the categories to terms whose identification with those of the
instantiated `CategoryTheory.mateEquiv_app_cube` is very expensive. -/
theorem boundedConstructibleIntegersModPowReduction_baseChange (sq : CommSq g' f' f g)
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    type_of% (mateEquiv_app_cube
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
      (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
      (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
      (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ sq).hom
      (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
        sq).hom
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f').inv
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g).inv
      (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g').inv
      (fun M ↦ by integersModPowReduction_cube_tac) K) :=
  mateEquiv_app_cube
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f')
    (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ sq).hom
    (boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ sq).hom
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f').inv
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g).inv
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n g').inv
    (fun M ↦ by integersModPowReduction_cube_tac) K

end AlgebraicGeometry.ProEtale.CondensedRing
