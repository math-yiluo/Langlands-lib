/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.RepresentableProConstant
public import WeilConjectures.CategoryTheory.DerivedCategory.ZSMul
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleRetract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullCompatible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The reduction modulo `ℓ` of a derived limit of partial right adjoints

Let `p : Z ⟶ Y` be a proper morphism of separated `k`-schemes of finite type, `E ⊆ ℚ̄_ℓ` a finite
subextension of `ℚ_ℓ`, `L ∈ Dᵇc(Y)⟦𝒪̲_E⟧`, and `Tₙ` a tower of bounded constructible
`𝒪_E`-complexes on `Z` representing `A ↦ Hom(Rp_* A, Res (L ⧸ ℓⁿ⁺¹))` on `Dᵇc(Z)⟦𝒪̲_E⟧`,
compatibly with the reduction tower of `L`. Write `Q = Res ∘ red` for the reduction modulo `ℓ`,
regarded as an endofunctor of `D(X_proét, 𝒪_E)`
(`AlgebraicGeometry.ProEtale.integersModReduction`); it is the cone of the multiplication by `ℓ`.
This file shows that the reduction modulo `ℓ` of the homotopy limit `G` of the `Tₙ` is bounded
constructible
(`ProEtale.CondensedRing.boundedConstructible_integersModReduction_homotopyLimit`),
hence so is its first derived reduction `G ⊗ᴸ 𝔽_E`
(`AlgebraicGeometry.ProEtale.boundedConstructible_derivedReduction_of_integersModReduction`).

The argument:

* `Q` commutes with countable products, being the cone of `ℓ`; hence `Q G` is the homotopy limit
  of the tower `Q Tₙ`;
* `Q` commutes with `Rp_*` compatibly with the reduction triangles
  (`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarIntegersModReductionComparison`), so that
  by the five lemma `Q Tₙ` represents `A ↦ Hom(Rp_* A, Q (L ⧸ ℓⁿ⁺¹))`;
* applying `Q` to the reduction triangles `L --ℓⁿ⁺¹--> L ⟶ L ⧸ ℓⁿ⁺¹ ⟶ L[1]`, whose first map
  becomes zero since `ℓ` kills the image of `Q`, shows that the tower `Q (L ⧸ ℓⁿ⁺¹)` is
  pro-isomorphic to the constant tower `Q L = L ⧸ ℓ`
  (`CategoryTheory.Pretriangulated.exists_proConstant_of_distTriang`);
* transporting this pro-isomorphism to the representing objects, the tower `Q Tₙ` is
  pro-isomorphic to the constant tower `T₀`, and `Q G ≅ T₀`
  (`CategoryTheory.Functor.RepresentsOn.nonempty_iso_of_isHomotopyLimit`).

Finally `G ⊗ᴸ 𝔽_E` is a retract of `(Q G) ⊗ᴸ 𝔽_E`, the multiplication by `ℓ` vanishing on
`𝔽_E`-complexes, and `Dᵇc(Z, 𝔽_E)` is stable under retracts
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_of_retract`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The **reduction modulo `ℓ`** `K ↦ Res (K ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓ)`, regarded as an endofunctor of
`D(X_proét, 𝒪_E)`: the cone of the multiplication by `ℓ`. -/
noncomputable abbrev integersModReduction (X : Scheme.{u}) :
    _root_.DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⥤
      _root_.DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :=
  (Mod.extendScalars (integersModPowReduction X ℓ E.1 1)).leftDerivedFunctor ⋙
    (Mod.comap (integersModPowReduction X ℓ E.1 1)).mapDerivedCategory


variable {ℓ E}

/-- `ℓ` acts by zero on the reduction modulo `ℓ`. -/
lemma zsmul_id_integersModReduction_obj {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) :
    (ℓ : ℤ) • 𝟙 ((integersModReduction ℓ E X).obj K) = 0 := by
  have : Epi (integersModPowReduction X ℓ E.1 1) :=
    (shortExact_integersModPowReduction X ℓ E.1 1).epi_g
  have w : ((ℓ : ℤ) • 𝟙 _) ≫ integersModPowReduction X ℓ E.1 1 = 0 := by
    simpa using zsmul_id_comp_integersModPowReduction X ℓ E.1 1
  have hM (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 1) X)) : (ℓ : ℤ) • 𝟙 M = 0 :=
    Mod.hom_ext _ _ (congrArg (fun f ↦ f.hom) (Mod.zsmul_id_comap_eq_zero _ w M))
  let N := (Mod.extendScalars (integersModPowReduction X ℓ E.1 1)).leftDerivedFunctor.obj K
  let Res := (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (integersModPowReduction X ℓ E.1 1)).mapDerivedCategory
  have : Res.Additive := inferInstance
  calc (ℓ : ℤ) • 𝟙 ((integersModReduction ℓ E X).obj K)
      = (ℓ : ℤ) • Res.map (𝟙 N) := congrArg (fun g ↦ (ℓ : ℤ) • g) (Res.map_id N).symm
    _ = Res.map ((ℓ : ℤ) • 𝟙 N) := (Functor.map_zsmul Res).symm
    _ = 0 := (congrArg Res.map (DerivedCategory.zsmul_id_eq_zero hM N)).trans (Res.map_zero _ _)

/-- The first derived reduction `K ⊗ᴸ 𝔽_E` of a complex whose reduction modulo `ℓ` is bounded
constructible lies in `Dᵇc(X, 𝔽_E)`: it is a retract of the first derived reduction of the
reduction modulo `ℓ`, since `ℓ` acts by zero on `𝔽_E`-complexes. -/
lemma boundedConstructible_derivedReduction_of_integersModReduction {X : Scheme.{u}}
    [IsNoetherian X]
    {K : _root_.DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((integersModReduction ℓ E X).obj K)) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K) := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
  let Lr := (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor
  let Mr := (residueFieldModuleSheaf X ℓ E).mapDerivedCategory
  have : Lr.Additive := inferInstance
  have : Mr.Additive := inferInstance
  have hT := Mr.map_distinguished _
    (Lr.map_distinguished _ (CondensedRing.integersModPowReduction_distinguished ℓ E.1 1 K))
  have hm (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))) :
      ((ℓ : ℤ) ^ 1) • 𝟙 M = 0 :=
    Sheaf.zsmul_id_eq_zero_of_intCast_eq_zero
      (by rw [pow_one, Int.cast_natCast, natCast_eq_zero_residueFieldCoeff]) M
  have h₀ : Mr.map (Lr.map (((ℓ : ℤ) ^ 1) • 𝟙 K)) = 0 :=
    calc Mr.map (Lr.map (((ℓ : ℤ) ^ 1) • 𝟙 K))
        = Mr.map (((ℓ : ℤ) ^ 1) • Lr.map (𝟙 K)) := congrArg Mr.map (Functor.map_zsmul Lr)
      _ = ((ℓ : ℤ) ^ 1) • Mr.map (Lr.map (𝟙 K)) := Functor.map_zsmul Mr
      _ = ((ℓ : ℤ) ^ 1) • 𝟙 (Mr.obj (Lr.obj K)) := congrArg (fun g ↦ ((ℓ : ℤ) ^ 1) • g)
          ((congrArg Mr.map (Lr.map_id K)).trans (Mr.map_id _))
      _ = 0 := DerivedCategory.zsmul_id_eq_zero hm _
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT (𝟙 _)
    ((congrArg (fun g ↦ g ≫ 𝟙 _) h₀).trans Limits.zero_comp)
  exact DerivedCategory.boundedConstructible_of_retract ⟨_, r, hr.symm⟩
    (boundedConstructible_derivedReduction_obj X ℓ E _ hK)

namespace CondensedRing

/-- **The reduction modulo `ℓ` of a derived limit of partial right adjoints is bounded
constructible**: if `G` is the homotopy limit of a tower `Tₙ` of bounded constructible
`𝒪_E`-complexes on `X` representing `A ↦ Hom(Rf_* A, Res (L ⧸ ℓⁿ⁺¹))` on `Dᵇc(X)⟦𝒪̲_E⟧`,
compatibly with the reduction tower of `L`, then `Res (G ⊗ᴸ 𝒪_E ⧸ ℓ)` is bounded constructible
(it is isomorphic to `T₀`). The reduction modulo `ℓ` commutes with `Rf_*` compatibly with the
natural reduction triangles (`CategoryTheory.unit_comp_map_reductionComparison`,
`CategoryTheory.map_reductionComparison_comp_δ`). -/
theorem boundedConstructible_integersModReduction_homotopyLimit {X Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    {T : ℕᵒᵖ ⥤ _root_.DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hT : ∀ n, boundedConstructible _ (T.obj (op n)))
    (ε : T ⋙ (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) f).rightDerivedFunctor ⟶
      ProEtale.reductionTower E L)
    (hε : ∀ n, Functor.RepresentsOn
      (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) f).rightDerivedFunctor
      (boundedConstructible _) (ε.app (op n)))
    {c : Cone T} (hc : IsHomotopyLimit c) :
    boundedConstructible _ ((integersModReduction ℓ E X).obj c.pt) :=
  prop_obj_homotopyLimit_of_reductionTriangle
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction Y ℓ E.1 1))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E.1 1))
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) f)
    (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E.1 1) f)
    (integersModPowReductionUpperStarIso ℓ E.1 1 f)
    (derivedComapLeftDerivedUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 1) f)
    (integersModPowReductionδ ℓ E.1 1 Y) (integersModPowReductionδ ℓ E.1 1 X) ((ℓ : ℤ) ^ 1)
    (integersModPowReduction_distinguished ℓ E.1 1) (integersModPowReduction_distinguished ℓ E.1 1)
    (integersModPowPullUnitCompatible ℓ E.1 1 f) (integersModPowPullδCompatible ℓ E.1 1 f)
    (ℓ : ℤ) zsmul_id_integersModReduction_obj (fun n ↦ (reductionTowerCone E L).π.app (op n))
    (fun n ↦ (integersModPowReductionδ ℓ E.1 (n + 1) Y).app L)
    (fun n ↦ integersModPowReduction_distinguished ℓ E.1 (n + 1) L)
    (fun n ↦ (reductionTowerCone E L).w (homOfLE n.le_succ).op)
    (fun n ↦ (congrArg (fun g ↦ g ≫ _) (reductionTower_map_succ L n)).trans
      (reductionTowerTransition_comp_δ L n).symm)
    hT ε hε (hT 0) (e := ε.app (op 0)) (hε 0) hc

end CondensedRing

end AlgebraicGeometry.ProEtale
