/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Geometric stalks of proper direct images on the pro-étale site

For a proper morphism `f : X ⟶ S`, a geometric point `x̄ : Spec Ω ⟶ S` and a bounded below
classical complex `K` of pro-étale sheaves with finite coefficients, the derived geometric stalk of
`Rf_* K` at `x̄` is the pro-étale cohomology of the geometric fibre `X_x̄`.

## Implementation details

The isomorphism is the proper base change isomorphism `Lx̄^* Rf_* K ≅ Rf'_* Lx̄'^* K`
(`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`) followed by the Leray
isomorphism for the projection `f' : X_x̄ ⟶ Spec Ω`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The Leray isomorphism `RΓ(W, Rg_* K) ≅ RΓ(Z, K)` for a morphism `g : Z ⟶ W` on the
pro-étale site: the composition of right derived functors applied to `g_* ⋙ Γ_W ≅ Γ_Z`
(`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`). -/
noncomputable def rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    {Z W : Scheme.{u}} (g : Z ⟶ W) :
    R(ProEtale.lowerStar A g) ⋙ rightDerivedGlobalSections A W ≅ rightDerivedGlobalSections A Z :=
  Functor.rightDerivedFunctorCompIso' _ _ (globalSectionsLowerStarIso A g)

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Geometric stalks of proper direct images**: for a finite coefficient ring `Λ`, a proper
morphism `f : X ⟶ S`, a geometric point `x̄ : Spec Ω ⟶ S` with `Ω` separably closed and a
bounded below classical complex `K` on `X_proét` (that is, `K ≅ ν_X^* L` with
`L ∈ D⁺(X_ét, Λ)`), the derived geometric stalk of `Rf_* K` at `x̄` is the pro-étale cohomology
of the geometric fibre `X_x̄ = X ×_S Spec Ω`:
`RΓ(Spec Ω, Lx̄^* Rf_* K) ≅ RΓ(X_x̄, Lx̄'^* K)`. -/
noncomputable def derivedGeometricStalkRightDerivedLowerStarIsoOfIsProper [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ S)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) :
    (derivedGeometricStalk (ModuleCat.{u + 1} Λ) x).obj
        (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (pullback f x)).obj
        (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f x)).obj K) :=
  haveI := isIso_derivedBaseChangeMap_app_of_isProper Λ (IsPullback.of_hasPullback f x) K hK
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).mapIso
      (asIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback f x).toCommSq).app K)) ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ)
      (pullback.snd f x)).app _

end AlgebraicGeometry.ProEtale
