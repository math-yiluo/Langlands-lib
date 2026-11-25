/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowHigherDirectImage

/-!
# Finiteness of the limit of the stalks of the tower `Hⁱ(Rg_* (Λ ⧸ Iⁿ))`

The stalks of the tower `AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`, shifted by one,
form the Bockstein tower `n ↦ (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)))_s` of
`AlgebraicGeometry.Etale.finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty`
(`AlgebraicGeometry.Etale.bocksteinStalkTowerIso`). Hence, on a stratum `j : S ⟶ Y` over which
`Rⁱg_* (Λ ⧸ I)` is finite locally constant, the limit of the stalks of the restricted tower is a
finite `Λ`-module
(`AlgebraicGeometry.Etale.finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower`).
This is the finiteness hypothesis of `ModuleCat.towerLimit_isModuleTopology` for the integral
identification on universal covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- The shift `n ↦ n + 1` of `ℕ`, a final functor. -/
abbrev natAddOneFunctor : ℕ ⥤ ℕ :=
  (show Monotone fun n : ℕ ↦ n + 1 from fun _ _ h ↦ Nat.add_le_add_right h 1).functor

instance : natAddOneFunctor.Final :=
  (Monotone.final_functor_iff _).2 fun n ↦ ⟨n, n.le_succ⟩

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) {T Y : Scheme.{u}} (g : T ⟶ Y)
  {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The Bockstein tower `n ↦ (Hⁱ(Rg_* (Λ ⧸ Iⁿ⁺¹)))_s` is the shifted stalk tower of
`AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`. -/
noncomputable def bocksteinStalkTowerIso (s : Spec (.of Ω) ⟶ Y) (i : ℕ) :
    Functor.ofOpSequence
        (X := fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).obj
          (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI (n + 1)).obj₃)
        (fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).map
          (DerivedCategory.quotPowTriangleMap T.smallEtaleTopology hϖ hI (n + 1)).hom₃) ≅
      natAddOneFunctor.op ⋙ higherDirectImageQuotPowTower I g i ⋙
        (pointSmallEtale s).sheafFiber :=
  let α := NatTrans.ofOpSequence (F := Functor.ofOpSequence
      (X := fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).obj
        (DerivedCategory.quotPowTriangle T.smallEtaleTopology hϖ hI (n + 1)).obj₃)
      (fun n ↦ (stalkHomologyRightDerivedLowerStar g s i).map
        (DerivedCategory.quotPowTriangleMap T.smallEtaleTopology hϖ hI (n + 1)).hom₃))
      (G := natAddOneFunctor.op ⋙ higherDirectImageQuotPowTower I g i ⋙
        (pointSmallEtale s).sheafFiber) (fun n ↦ 𝟙 _) fun n ↦ by
        rw [Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
        rfl
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    rw [NatTrans.ofOpSequence_app]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  asIso α

include hϖ hI in
/-- **Finiteness of the limit of the stalks over a stratum.** Let `Λ` be noetherian and complete
for `I = (ϖ)`, `ϖ` a nonzerodivisor, with `Λ ⧸ I` finite, and `j : S ⟶ Y` a stratum over which
`Rⁱg_* (Λ ⧸ I)_T` restricts to a finite locally constant sheaf. Then at every geometric point `s`
of `S`, the limit of the stalks of the restricted tower `n ↦ j^* Hⁱ(Rg_* (Λ ⧸ Iⁿ)_T)` is a finite
`Λ`-module. -/
theorem finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ] [Finite (Λ ⧸ I)] {S : Scheme.{u}} (j : S ⟶ Y)
    (s : Spec (.of Ω) ⟶ S) (i : ℕ)
    (h : flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived i).obj (constantQuotSheaf Λ I T)))) :
    Module.Finite Λ ↑(limit (higherDirectImageQuotPowTower I g i ⋙
      (j)^*[ModuleCat.{u + 1} Λ] ⋙ (pointSmallEtale s).sheafFiber)) := by
  have := finite_limit_stalkHomologyRightDerivedLowerStar_of_flcProperty I g hϖ hI j s i h
  let e : limit (higherDirectImageQuotPowTower I g i ⋙
      (j)^*[ModuleCat.{u + 1} Λ] ⋙ (pointSmallEtale s).sheafFiber) ≅ _ :=
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft _
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) j s)) ≪≫
      (Functor.Initial.limitIso natAddOneFunctor.op _).symm ≪≫
      HasLimit.isoOfNatIso (bocksteinStalkTowerIso I g hϖ hI (s ≫ j) i).symm
  exact Module.Finite.equiv e.symm.toLinearEquiv

end AlgebraicGeometry.Etale
