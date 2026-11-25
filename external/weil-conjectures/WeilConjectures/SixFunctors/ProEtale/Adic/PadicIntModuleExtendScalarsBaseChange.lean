/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRightDerivedLowerStar

/-!
# Extension of scalars `ℚ̄_ℓ ⊗_{ℤ_ℓ} -` and higher direct images

For a morphism of schemes `f : X ⟶ Y`, restriction of scalars from `ℓ`-adic sheaves to
`ℤ_ℓ`-modules commutes with the pushforwards
(`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntPushforwardIso`), and its mate is the
canonical comparison
```
ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)
```
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsPushforwardComparison`). We show that the
induced base change morphism of derived pushforwards
`ℚ̄_ℓ ⊗ Rᵠf_* M ⟶ Rᵠf_* (ℚ̄_ℓ ⊗ M)` is an isomorphism as soon as
1. extension of scalars `ℚ̄_ℓ ⊗ -` is exact on `X` and on `Y`;
2. the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism;
3. for every injective `ℤ_ℓ,X`-module `I`, the abelian sheaf underlying `ℚ̄_ℓ ⊗ I` is
   `f_*`-acyclic

(`isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison`),
which gives an isomorphism of `ℓ`-adic sheaves
`ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ≅ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsHomologyRightDerivedIso`) and hence the
lisse-ness of `Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` when `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0])` is lisse
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_baseChange`).

Mathematically, all three conditions hold for `f` quasi-compact and quasi-separated, since
`ℚ̄_ℓ,X` is a filtered colimit of free `ℤ_ℓ,X`-modules of finite rank and `Rᵠf_*` commutes with
filtered colimits
(`WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Extension of scalars from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves is right exact, being a left
adjoint. -/
instance preservesFiniteColimits_adicSheafExtendScalars (X : Scheme.{u}) :
    PreservesFiniteColimits (adicSheafExtendScalars X l) :=
  have : PreservesColimitsOfSize.{0, 0} (adicSheafExtendScalars X l) :=
    (adicSheafExtendScalarsRestrictAdjunction X l).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Extension of scalars from `ℤ_ℓ,X`-modules to `ℓ`-adic sheaves is additive. -/
instance additive_adicSheafExtendScalars (X : Scheme.{u}) :
    (adicSheafExtendScalars X l).Additive :=
  (adicSheafExtendScalarsRestrictAdjunction X l).left_adjoint_additive

/-- The canonical comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` between extension of scalars after
pushforward and pushforward after extension of scalars, for `ℤ_ℓ,X`-modules `M`: the mate of the
isomorphism `res (f_* F) ≅ f_* (res F)` expressing that restriction of scalars commutes with the
pushforwards. -/
noncomputable def adicSheafExtendScalarsPushforwardComparison :
    padicIntModPushforward l f ⋙ adicSheafExtendScalars Y l ⟶
      adicSheafExtendScalars X l ⋙ (f)_*ᵃ[l] :=
  Adjunction.pushHomOfComapIso (adicSheafExtendScalarsRestrictAdjunction X l)
    (adicSheafExtendScalarsRestrictAdjunction Y l) (adicLowerStarRestrictPadicIntPushforwardIso l f)

/-- An `ℓ`-adic sheaf whose underlying abelian sheaf is zero is zero. -/
lemma isZero_of_isZero_adicSheafToAb {Z : AdicSheaf l X}
    (h : IsZero ((AdicSheaf.toAb l X).obj Z)) : IsZero Z := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact (AdicSheaf.toAb l X).map_injective
    (by rw [CategoryTheory.Functor.map_id, Functor.map_zero, h])

/-- An `ℓ`-adic sheaf is `f_*`-acyclic as soon as its underlying abelian sheaf is. -/
lemma rightAcyclic_adicLowerStar_of_rightAcyclic_toAb {Z : AdicSheaf l X}
    (h : ((f)_*[Ab.{u + 1}]).rightAcyclic ((AdicSheaf.toAb l X).obj Z)) :
    ((f)_*ᵃ[l]).rightAcyclic Z := fun n ↦
  isZero_of_isZero_adicSheafToAb l
    ((h n).of_iso ((rightDerivedAdicLowerStarToAbIso l f (n + 1)).app Z))

section BaseChange

variable [PreservesFiniteLimits (adicSheafExtendScalars X l)]
  [PreservesFiniteLimits (adicSheafExtendScalars Y l)]

/-- **Extension of scalars commutes with the derived pushforward**: if `ℚ̄_ℓ ⊗ -` is exact on `X`
and on `Y`, the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism, and `ℚ̄_ℓ ⊗ I` has
an `f_*`-acyclic underlying abelian sheaf for every injective `ℤ_ℓ,X`-module `I`, then the base
change morphism `ℚ̄_ℓ ⊗ R⁺f_* K ⟶ R⁺f_* (ℚ̄_ℓ ⊗ K)` is an isomorphism. -/
theorem isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison
    [IsIso (adicSheafExtendScalarsPushforwardComparison l f)]
    (h : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) [Injective I],
      ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj I))) :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (adicSheafExtendScalarsPushforwardComparison l f)) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (adicSheafExtendScalarsPushforwardComparison l f))
    fun I _ ↦ rightAcyclic_adicLowerStar_of_rightAcyclic_toAb l f (h I)

/-- `ℚ̄_ℓ ⊗ Rᵠf_* M ≅ Rᵠf_* (ℚ̄_ℓ ⊗ M)` for the classical right derived functors, under the
hypotheses of
`isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison`. -/
noncomputable def adicSheafExtendScalarsRightDerivedIso
    [IsIso (adicSheafExtendScalarsPushforwardComparison l f)]
    (h : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) [Injective I],
      ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj I))) (q : ℕ) :
    (padicIntModPushforward l f).rightDerived q ⋙ adicSheafExtendScalars Y l ≅
      adicSheafExtendScalars X l ⋙ ((f)_*ᵃ[l]).rightDerived q :=
  have : IsIso (Functor.rightDerivedBaseChange
      (adicSheafExtendScalarsPushforwardComparison l f) q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have := isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison
      l f h
    infer_instance
  asIso (Functor.rightDerivedBaseChange (adicSheafExtendScalarsPushforwardComparison l f) q)

/-- `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ≅ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` as `ℓ`-adic sheaves, the left hand side
computed for `ℤ_ℓ`-modules, under the hypotheses of
`isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison`. -/
noncomputable def adicSheafExtendScalarsHomologyRightDerivedIso
    [IsIso (adicSheafExtendScalarsPushforwardComparison l f)]
    (h : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) [Injective I],
      ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj I)))
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ) :
    (adicSheafExtendScalars Y l).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      (DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M))) :=
  (adicSheafExtendScalars Y l).mapIso
      ((padicIntModPushforward l f).homologyRightDerivedFunctorObjSingleFunctorIso M q) ≪≫
    (adicSheafExtendScalarsRightDerivedIso l f h q).app M ≪≫
    (((f)_*ᵃ[l]).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

/-- **Lisse direct images from the integral ones**: under the hypotheses of
`isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison`, if
`ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0])` is lisse, the right hand side computed for `ℤ_ℓ`-modules, then so is
`Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_baseChange
    [IsIso (adicSheafExtendScalarsPushforwardComparison l f)]
    (h : ∀ (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) [Injective I],
      ((f)_*[Ab.{u + 1}]).rightAcyclic
        ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj I)))
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ)
    (hM : IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M)))) :=
  hM.of_iso (adicSheafExtendScalarsHomologyRightDerivedIso l f h M q)

end BaseChange

end AlgebraicGeometry.ProEtale
