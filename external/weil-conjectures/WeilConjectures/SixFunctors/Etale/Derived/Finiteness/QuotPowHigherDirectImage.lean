/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstantScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.StalkBocksteinQuotient

/-!
# The tower of higher direct images of the constant sheaves `Λ ⧸ Iⁿ`

Let `g : T ⟶ Y` be a morphism of schemes, `Λ` a ring and `I` an ideal of `Λ`. The higher direct
images `Hⁱ(Rg_* (Λ ⧸ Iⁿ)_T)`, computed in `D(T_ét, Λ)`, form a tower of étale sheaves of
`Λ`-modules on `Y` (`AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`), all in the single
category of sheaves of `Λ`-modules, with transition maps induced by `Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ`. Each
level is the higher direct image of `Λ ⧸ Iⁿ` computed over the ring `Λ ⧸ Iⁿ`, with scalars
restricted to `Λ` (`AlgebraicGeometry.Etale.higherDirectImageQuotPowTowerObjIso`). Hence:

- `AlgebraicGeometry.Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj`: on a stratum
  `j : S ⟶ Y` over which the `Rⁱg_* (Λ ⧸ Iⁿ)` are finite locally constant over `Λ ⧸ Iⁿ` (as given
  by the uniform stratification
  `AlgebraicGeometry.Etale.flcProperty_rightDerived_lowerStar_of_tower`),
  the restricted tower is an `IsSetFLC` tower of sheaves of `Λ`-modules;
- `AlgebraicGeometry.Etale.smul_eq_zero_sheafFiber_higherDirectImageQuotPowTower_obj`: the stalks
  of the `n`-th level are killed by `Iⁿ`.

This is the form of the torsion tower used for the `ℓ`-adic finiteness theorem in the constant
case: its stalks form the tower of
`AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty`
(`AlgebraicGeometry.Etale.higherDirectImageQuotPowTower_obj_succ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) {T Y : Scheme.{u}} (g : T ⟶ Y)

/-- The tower `n ↦ Hⁱ(Rg_* (Λ ⧸ Iⁿ)_T)` of étale sheaves of `Λ`-modules on `Y`, the derived
direct image being computed in `D(T_ét, Λ)`. -/
noncomputable def higherDirectImageQuotPowTower (i : ℤ) :
    ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Ideal.quotPowFunctor I ⋙ constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    _root_.DerivedCategory.singleFunctor _ 0 ⋙ R((g)_*[ModuleCat.{u + 1} Λ]) ⋙
      _root_.DerivedCategory.homologyFunctor _ i

/-- The `Λ ⧸ J`-module `Λ ⧸ J` with scalars restricted to `Λ` is the `Λ`-module `Λ ⧸ J`. -/
noncomputable def restrictScalarsQuotSelfIso (J : Ideal Λ) :
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)).obj (ModuleCat.of (Λ ⧸ J) (Λ ⧸ J)) ≅
      ModuleCat.of Λ (Λ ⧸ J) :=
  LinearEquiv.toModuleIso
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' r x := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Restriction of scalars of the constant sheaf `Λ ⧸ J` of `Λ ⧸ J`-modules is the constant
sheaf `Λ ⧸ J` of `Λ`-modules. -/
noncomputable def restrictScalarsConstantQuotSheafSelfIso (J : Ideal Λ) (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj
        (constantQuotSheaf Λ J X) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Λ ⧸ J)) :=
  haveI : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  (constantSheafCompSheafComposeIso X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J))).app _ ≪≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso (restrictScalarsQuotSelfIso J)

/-- **The levels of the tower**: `Hⁱ(Rg_* (Λ ⧸ Iⁿ)_T)`, computed in `D(T_ét, Λ)`, is the higher
direct image `Rⁱg_* (Λ ⧸ Iⁿ)_T` of sheaves of `Λ ⧸ Iⁿ`-modules with scalars restricted to `Λ`. -/
noncomputable def higherDirectImageQuotPowTowerObjIso (i n : ℕ) :
    (higherDirectImageQuotPowTower I g i).obj (op n) ≅
      (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk (I ^ n))).obj
        (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].rightDerived i).obj
          (constantQuotSheaf Λ (I ^ n) T)) :=
  (_root_.DerivedCategory.homologyFunctor _ i).mapIso
      ((R((g)_*[ModuleCat.{u + 1} Λ])).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (restrictScalarsConstantQuotSheafSelfIso (I ^ n) T).symm) ≪≫
        (restrictScalarsRightDerivedLowerStarSingleIso (Ideal.Quotient.mk (I ^ n)) g _).symm) ≪≫
    (((Sheaf.restrictScalars Y.smallEtaleTopology
      (Ideal.Quotient.mk (I ^ n))).mapDerivedCategoryHomologyFunctorIso i).app _).symm ≪≫
    (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk (I ^ n))).mapIso
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).homologyRightDerivedFunctorObjSingleFunctorIso _ i)

/-- **The tower is `IsSetFLC` on a stratum**: if over `j : S ⟶ Y` the higher direct image
`Rⁱg_* (Λ ⧸ Iⁿ)_T` of sheaves of `Λ ⧸ Iⁿ`-modules restricts to a sheaf with finite locally constant
underlying sheaf of sets, so does the `n`-th level of the tower. -/
lemma isSetFLC_upperStar_higherDirectImageQuotPowTower_obj {S : Scheme.{u}} (j : S ⟶ Y)
    (i n : ℕ) (h : IsSetFLC ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].rightDerived i).obj
        (constantQuotSheaf Λ (I ^ n) T)))) :
    IsSetFLC ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g i).obj (op n))) :=
  IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mapIso
      (((upperStarRestrictScalarsIso (Ideal.Quotient.mk (I ^ n)) j).app _).symm ≪≫
        (j)^*[ModuleCat.{u + 1} Λ].mapIso (higherDirectImageQuotPowTowerObjIso I g i n).symm))
    (h.restrictScalars (Ideal.Quotient.mk (I ^ n)))

/-- The `IsSetFLC` hypothesis of
`AlgebraicGeometry.Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj` from finite local
constancy over the finite ring `Λ ⧸ Iⁿ`. -/
lemma isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty {S : Scheme.{u}}
    (j : S ⟶ Y) (i n : ℕ) [Finite (Λ ⧸ I ^ n)]
    (h : flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].rightDerived i).obj
        (constantQuotSheaf Λ (I ^ n) T)))) :
    IsSetFLC ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g i).obj (op n))) :=
  have := h
  isSetFLC_upperStar_higherDirectImageQuotPowTower_obj I g j i n
    (IsFiniteLocallyConstantSheaf.isSetFLC inferInstance)

/-- An element of a module isomorphic to a module killed by `x` is killed by `x`. -/
lemma _root_.ModuleCat.smul_eq_zero_of_iso {M N : ModuleCat.{u + 1} Λ} (e : M ≅ N) {x : Λ}
    (h : ∀ y : N, x • y = 0) (m : M) : x • m = 0 := by
  have h1 := e.toLinearEquiv.symm.map_smul x (e.toLinearEquiv m)
  rw [h, map_zero, LinearEquiv.symm_apply_apply] at h1
  exact h1.symm

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The stalks of the `n`-th level are killed by `Iⁿ`**, being restrictions of scalars of
`Λ ⧸ Iⁿ`-modules. -/
lemma smul_eq_zero_sheafFiber_higherDirectImageQuotPowTower_obj (s : Spec (.of Ω) ⟶ Y)
    (i n : ℕ) {x : Λ} (hx : x ∈ I ^ n)
    (m : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((higherDirectImageQuotPowTower I g i).obj (op n))) :
    x • m = 0 :=
  ModuleCat.smul_eq_zero_of_iso
    ((pointSmallEtale s).sheafFiber.mapIso (higherDirectImageQuotPowTowerObjIso I g i n) ≪≫
      ((pointSmallEtale s).sheafFiberCompIso
        (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (I ^ n)))).app _)
    (fun y ↦ by
      rw [ModuleCat.restrictScalars.smul_def, Ideal.Quotient.eq_zero_iff_mem.2 hx, zero_smul]) m

/-- The stalks at the geometric points of a stratum `j : S ⟶ Y` of the restricted `n`-th level
are killed by `Iⁿ`. -/
lemma smul_eq_zero_sheafFiber_upperStar_higherDirectImageQuotPowTower_obj {S : Scheme.{u}}
    (j : S ⟶ Y) (s : Spec (.of Ω) ⟶ S) (i n : ℕ) {x : Λ} (hx : x ∈ I ^ n)
    (m : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g i).obj (op n)))) :
    x • m = 0 :=
  ModuleCat.smul_eq_zero_of_iso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) j s).app _)
    (smul_eq_zero_sheafFiber_higherDirectImageQuotPowTower_obj I g (s ≫ j) i n hx) m

end AlgebraicGeometry.Etale
