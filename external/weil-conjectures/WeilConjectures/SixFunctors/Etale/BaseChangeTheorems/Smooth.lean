/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!

# The smooth base change theorem

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` **smooth**, recorded as `sq : IsPullback g' f' f g`. This file states the
general smooth base change theorem in étale cohomology: for every object `K` of the
bounded below derived category `D⁺(X_ét, Λ)` all of whose cohomology sheaves are torsion
with order invertible on `Y` , the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` is an isomorphism
if `f` is qcqs.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [QuasiCompact f] [QuasiSeparated f]

/-- **The smooth base change theorem** in étale cohomology. -/
theorem Etale.isIso_baseChange_of_smooth [Smooth g] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.orderInvertibleOnHomology f K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) := by
  have hK_expanded : ∀ (q : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K)),
      IsUnit (addOrderOf x : Γ(Y, ⊤)) := by
    intro q Ω hfield hclosed t x
    exact (hK q).isUnit_addOrderOf_sheafFiber Ω t x
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  let Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  obtain ⟨K', ⟨eK⟩⟩ := Etale.exists_forget₂_mapDerivedCategoryPlus_obj_iso K
  have hK' : Etale.DerivedCategory.Plus.torsionHomologyOfPrimes
      (ULift.{u + 1} ℤ) X Y.invertiblePrimes K' := by
    intro q
    constructor
    intro Ω _ _ s x
    let F := (DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) q).obj K'
    let eH : Φ.obj F ≅ (DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K :=
      (Φ.mapDerivedCategoryPlusHomologyFunctorIso q).app K' ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso eK
    have : PreservesFilteredColimitsOfSize.{u, u}
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have : LocallySmall.{u} X.Etale := locallySmall_self _
    let ψ : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).obj
        ((Scheme.pointSmallEtale s).sheafFiber.obj F) ≅
        ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K) :=
      (((Scheme.pointSmallEtale s).sheafFiberCompIso
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).app F).symm ≪≫
        (Scheme.pointSmallEtale s).sheafFiber.mapIso eH
    have hx : IsUnit (addOrderOf x : Γ(Y, ⊤)) := by
      have heq := addOrderOf_injective ψ.hom.hom
        (ConcreteCategory.bijective_of_isIso ψ.hom).1 x
      rw [← heq]
      exact hK_expanded q Ω s (ψ.hom.hom x)
    let ρ : Γ(Y, ⊤) ⟶ CommRingCat.of Ω :=
      (s ≫ f).appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom
    have : Nontrivial Γ(Y, ⊤) := ρ.hom.domain_nontrivial
    have hn : 0 < addOrderOf x := Nat.pos_of_ne_zero fun hn ↦ by
      apply hx.ne_zero
      simp only [hn, Nat.cast_zero]
    refine ⟨addOrderOf x, hn, ?_, addOrderOf_nsmul_eq_zero x⟩
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp,
      isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_of_mem_primeFactors hp)) hx⟩
  have hm := Etale.isIso_baseChange_app_of_smooth (ULift.{u + 1} ℤ) g sq K' hK'
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at hm
  have hab : IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      sq.toCommSq).app (Φ.mapDerivedCategoryPlus.obj K')) :=
    (Etale.isIso_derivedBaseChangeMapPlus_app_forget₂_iff sq.toCommSq K').2 hm
  exact (NatTrans.isIso_app_iff_of_iso
    (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) eK).1 hab

/-- **The smooth base change theorem as an isomorphism of functors** in étale cohomology. -/
theorem Etale.isIso_baseChange_of_smooth_of_ring_order_invertible [Smooth g]
    (sq : IsPullback g' f' f g) (htor : ∀ (a : Λ), IsUnit (addOrderOf a : Γ(Y, ⊤))) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : ∀ K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    fun K ↦ by
      let N := addOrderOf (1 : Λ)
      by_cases hN : N = 0
      · have hzero : IsUnit (0 : Γ(Y, ⊤)) := by
          simpa [N, hN] using htor (1 : Λ)
        have hsub : Subsingleton Γ(Y, ⊤) :=
          subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
        have : IsEmpty Y := Scheme.isEmpty_of_subsingleton_Γ hsub
        apply Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder
          Λ g sq K
        intro j
        refine ⟨?_⟩
        intro Ω _ _ s x
        exact isEmptyElim (f.base (s.base (IsLocalRing.closedPoint Ω)))
      · have hNΛ : (N : Λ) = 0 := by
          dsimp [N]
          simpa only [nsmul_eq_mul, mul_one] using addOrderOf_nsmul_eq_zero (1 : Λ)
        have hNY : IsUnit (N : Γ(Y, ⊤)) := by
          simpa [N] using htor (1 : Λ)
        apply Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder
          Λ g sq K
        intro j
        exact Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN hNΛ hNY _
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
