/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantTower
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotientCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.StalkBockstein
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The reduction modulo `ϖ` of the stalks of higher direct images, over `Λ ⧸ I`

Let `g : T ⟶ Y` be a morphism of schemes, `s` a geometric point of `Y`, `Λ` a ring and `I` an
ideal of `Λ`. The stalk at `s` of `Hⁱ(Rg_* (Λ ⧸ I)_T)`, computed in `D(T_ét, Λ)`, is the stalk of
the higher direct image `Rⁱg_* (Λ ⧸ I)_T` of the constant sheaf of `Λ ⧸ I`-modules, with scalars
restricted to `Λ` (`AlgebraicGeometry.Etale.stalkHomologyRightDerivedLowerStarQuotIso`):
restriction of scalars commutes with constant sheaves, with `Rg_*`
(`AlgebraicGeometry.Etale.restrictScalarsRightDerivedLowerStarSingleIso`) and with the homology
sheaves.

Consequently, for `Λ` noetherian and complete for `I = (ϖ)` with `ϖ` a nonzerodivisor, the
limit `lim_n (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)_T))_s` is a finite `Λ`-module as soon as the stalk of
`Rⁱg_* (Λ ⧸ I)_T` at `s` is a finite `Λ ⧸ I`-module
(`AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar_of_finite`). In
particular this holds at every geometric point `s` of a stratum `j : S ⟶ Y` over which
`Rⁱg_* (Λ ⧸ I)_T` is finite locally constant
(`AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty`), the
situation of the uniform stratification of
`AlgebraicGeometry.Etale.flcProperty_rightDerived_lowerStar_of_tower`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

variable (Λ) in
/-- The constant étale sheaf `Λ ⧸ I` of `Λ ⧸ I`-modules on `X`. -/
noncomputable abbrev constantQuotSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))).obj
    (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))

/-- The `Λ ⧸ I`-module `Λ ⧸ I` with scalars restricted to `Λ` is the `Λ`-module `Λ ⧸ I¹`. -/
noncomputable def restrictScalarsQuotIso :
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) ≅
      ModuleCat.of Λ (Λ ⧸ I ^ 1) :=
  LinearEquiv.toModuleIso
    { toFun x := Ideal.quotEquivOfEq (pow_one I).symm x
      invFun x := Ideal.quotEquivOfEq (pow_one I) x
      map_add' x y := map_add _ x y
      map_smul' r x := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      left_inv x := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      right_inv x := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }

/-- Restriction of scalars of the constant sheaf `Λ ⧸ I` of `Λ ⧸ I`-modules is the constant
sheaf `Λ ⧸ I¹` of `Λ`-modules, the third vertex of `DerivedCategory.quotPowTriangle _ _ _ 1`. -/
noncomputable def restrictScalarsConstantQuotSheafIso (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk I)).obj
        (constantQuotSheaf Λ I X) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ I ^ 1)) :=
  haveI : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  (constantSheafCompSheafComposeIso X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I))).app _ ≪≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso (restrictScalarsQuotIso I)

variable {T Y : Scheme.{u}} (g : T ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})

/-- The stalk at `s` of `Hⁱ(Rg_* (Λ ⧸ I)_T)`, computed in `D(T_ét, Λ)`, is the stalk of the higher
direct image `Rⁱg_* (Λ ⧸ I)_T` of sheaves of `Λ ⧸ I`-modules, with scalars restricted to `Λ`. -/
noncomputable def stalkHomologyRightDerivedLowerStarQuotIso (i : ℕ) :
    (stalkHomologyRightDerivedLowerStar g s i).obj
        (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI 1).obj₃ ≅
      (pointSmallEtale s).sheafFiber.obj
        ((Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk I)).obj
          (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived i).obj (constantQuotSheaf Λ I T))) :=
  (pointSmallEtale s).sheafFiber.mapIso
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
      ((R((g)_*[ModuleCat.{u + 1} Λ])).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (restrictScalarsConstantQuotSheafIso I T).symm) ≪≫
        (restrictScalarsRightDerivedLowerStarSingleIso (Ideal.Quotient.mk I) g _).symm) ≪≫
      (((Sheaf.restrictScalars Y.smallEtaleTopology
        (Ideal.Quotient.mk I)).mapDerivedCategoryHomologyFunctorIso i).app _).symm ≪≫
      (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk I)).mapIso
        (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)]).homologyRightDerivedFunctorObjSingleFunctorIso _ i))

/-- **Finiteness of the limit of the stalks of the higher direct images of `Λ ⧸ Iⁿ⁺¹`, from the
reduction modulo `I`.** Let `Λ` be noetherian and complete for `I = (ϖ)`, `ϖ` a nonzerodivisor.
If the stalk at `s` of the higher direct image `Rⁱg_* (Λ ⧸ I)_T` of sheaves of `Λ ⧸ I`-modules is
finitely generated, then `lim_n (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)_T))_s` is a finite `Λ`-module, the limit
being along the maps induced by the quotient maps `Λ ⧸ Iⁿ⁺² ⟶ Λ ⧸ Iⁿ⁺¹`
(`DerivedCategory.quotPowTriangleMap_hom₃`). -/
theorem finite_limit_stalkHomologyRightDerivedLowerStar_of_finite [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ] (i : ℕ)
    (h : ConcreteCategory.IsFinitelyGenerated ((pointSmallEtale s).sheafFiber.obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived i).obj (constantQuotSheaf Λ I T)))) :
    Module.Finite Λ ↑(limit (Functor.ofOpSequence
      (X := fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).obj
        (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).map
        (DerivedCategory.quotPowTriangleMap T.smallEtaleTopology hϖ hI (n + 1)).hom₃)) := by
  have h' := (isFinitelyGenerated_sheafFiber_restrictScalars_iff I _ Ω s).2 h
  rw [ModuleCat.isFinitelyGenerated_iff] at h'
  have : Module.Finite Λ ((stalkHomologyRightDerivedLowerStar g s i).obj
      (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI 1).obj₃) :=
    Module.Finite.equiv (stalkHomologyRightDerivedLowerStarQuotIso I g s hϖ hI i).symm.toLinearEquiv
  exact finite_limit_stalkHomologyRightDerivedLowerStar g s hϖ hI i

/-- **Finiteness of the limit of the stalks over a stratum.** Let `Λ` be noetherian and complete
for `I = (ϖ)`, `ϖ` a nonzerodivisor, with `Λ ⧸ I` finite, and `j : S ⟶ Y` a stratum over which
the higher direct image `Rⁱg_* (Λ ⧸ I)_T` restricts to a finite locally constant sheaf. Then at
every geometric point `s` of `S`, `lim_n (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)_T))_s` is a finite `Λ`-module. -/
theorem finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ] [Finite (Λ ⧸ I)] {S : Scheme.{u}} (j : S ⟶ Y)
    (s : Spec (.of Ω) ⟶ S) (i : ℕ)
    (h : flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived i).obj (constantQuotSheaf Λ I T)))) :
    Module.Finite Λ ↑(limit (Functor.ofOpSequence
      (X := fun n ↦ (stalkHomologyRightDerivedLowerStar g (s ≫ j) i).obj
        (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      fun n ↦ (stalkHomologyRightDerivedLowerStar g (s ≫ j) i).map
        (DerivedCategory.quotPowTriangleMap T.smallEtaleTopology hϖ hI (n + 1)).hom₃)) := by
  have := h
  refine finite_limit_stalkHomologyRightDerivedLowerStar_of_finite I g (s ≫ j) hϖ hI i ?_
  exact (ConcreteCategory.isFinitelyGenerated_iff_of_iso
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} (Λ ⧸ I)) j s).app _)).1
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s)

end AlgebraicGeometry.Etale
