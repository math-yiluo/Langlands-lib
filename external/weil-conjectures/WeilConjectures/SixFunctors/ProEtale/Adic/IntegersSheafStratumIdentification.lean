/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratumFLC
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarSections

/-!
# The sheaf-level integral identification on the universal covers of a stratum

Let `g : T ⟶ Y` be quasi-compact and quasi-separated, `E` a finite extension of `ℚ_ℓ` and
`j = i ≫ o : S ⟶ Y` a stratum over which the torsion direct images `Rᵏg_* (Λ ⧸ ℓ)_T` are finite
locally constant (`Λ = Shrink 𝒪_E`). The derived-level integral identification
`Hᵏ(p^* j^* Rg_* 𝒪_{E,T}) ≅ C(-, lim_n Gₙ)` on a universal cover `p : Ỹ_y ⟶ S`
(`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty`) is
turned into an identification `C(-, lim_n Gₙ) ≅ (p ≫ j)^* Rᵏg_* 𝒪_{E,T}` of abelian sheaves
(`AlgebraicGeometry.ProEtale.nonempty_iso_upperStar_rightDerived_integersStratum`): the pullbacks
are exact, hence commute with `Hᵏ`, and `Hᵏ(Rg_* A) = Rᵏg_* A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  {T Y S S' : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g]

/-- `Hᵏ(p^* j^* Rg_* 𝒪_{E,T}) ≅ (p ≫ j)^* Rᵏg_* 𝒪_{E,T}`, the pullbacks being exact. -/
noncomputable def homologyUpperStarIntegersConeIso (j : S ⟶ Y) (p : S' ⟶ S) (k : ℕ) :
    (DerivedCategory.homologyFunctor _ k).obj
        ((ProEtale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.obj
          ((ProEtale.upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategory.obj
            (integersCone l E g).pt)) ≅
      (p ≫ j)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived k).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntegersSheaf T l E))) :=
  ((ProEtale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryHomologyFunctorIso k).symm.app
      _ ≪≫
    (ProEtale.upperStar AddCommGrpCat.{u + 1} p).mapIso
      (((ProEtale.upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategoryHomologyFunctorIso
        k).symm.app _ ≪≫
      (ProEtale.upperStar AddCommGrpCat.{u + 1} j).mapIso
        ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).homologyRightDerivedFunctorObjSingleFunctorIso
          _ k)) ≪≫
    (ProEtale.upperStarComp AddCommGrpCat.{u + 1} p j).symm.app _

/-- **The sheaf-level integral identification on the universal covers of a stratum**: for
`j = i ≫ o` as in
`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty` and the
projection `p : Ỹ_y ⟶ S` of a universal cover, `C(-, lim_n Gₙ) ≅ (p ≫ j)^* Rᵏg_* 𝒪_{E,T}`, `Gₙ`
the (finite) stalks of `j^* Hᵏ(Rg_* (Λ ⧸ ℓⁿ))` at the base point. -/
theorem nonempty_iso_upperStar_rightDerived_integersStratum {U : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace U] (i : S ⟶ U) [IsClosedImmersion i] (o : U ⟶ Y)
    [IsOpenImmersion o]
    (h : ∀ k : ℕ, Etale.flcProperty S (upperStarRightDerivedIntegersModL l E g (i ≫ o) k))
    {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℕ) :
    let H' := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
      Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) (i ≫ o)
    let St := (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber
      (A := ModuleCat.{u + 1} (integersShrink.{u} l E))
    have (n : ℕ) : Finite (St.obj (H'.obj (op n))) :=
      (isSetFLC_upperStar_higherDirectImageQuotPowTower_integers l E g (i ≫ o) h n
        k).finite_sheafFiber _
    Nonempty (ProEtale.continuousMapAddSheaf (Ũ.cover y)
        (ProEtale.towerLimitAddSubgroup (Qs := fun n ↦ DiscreteShrink (St.obj (H'.obj (op n))))
          (fun n ↦ DiscreteShrink.map
            (St.map (H'.map (homOfLE (n.le_add_right 1)).op)).hom.toAddMonoidHom)) ≅
      (Ũ.proj y ≫ i ≫ o)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived k).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntegersSheaf T l E)))) := by
  intro H' St _
  obtain ⟨φ⟩ := nonempty_iso_homologyUpperStar_integersStratum_of_flcProperty l E g i o h Ũ y k
  exact ⟨φ.symm ≪≫ homologyUpperStarIntegersConeIso l E g (i ≫ o) (Ũ.proj y) k⟩

end AlgebraicGeometry.ProEtale
