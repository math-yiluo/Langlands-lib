/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.TowerLimitFiniteOfReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ExtensionTowerLocallyConstant
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.StalkBockstein

/-!
# Finiteness of the limit of the stalks of the higher direct images of a tower of reductions

Let `Λ` be a noetherian `ϖ`-adically complete ring and `M : ℕᵒᵖ ⥤ Sh(T_ét, Λ)` a tower of étale
sheaves of `Λ`-modules with `ϖⁿ⁺¹ Mₙ = 0`, together with maps `ιₙ : Mₙ ⟶ Mₙ₊₁` such that
`ιₙ ∘ tₙ = ϖ`, `tₙ ∘ ιₙ = ϖ` (`tₙ` the transitions) and `0 ⟶ Mₙ --ιₙ--> Mₙ₊₁ ⟶ M₀ ⟶ 0` is short
exact: for instance the reductions `Mₙ = L ⧸ ϖⁿ⁺¹` of a lattice `L` in a lisse `ℓ`-adic sheaf, `ιₙ`
being induced by the multiplication by `ϖ`. For `g : T ⟶ Y`, a stratum `j : S ⟶ Y` and a geometric
point `s` of `S` at which the stalks of the `j^* Hᵏ(Rg_* Mₙ)` are finite, the limit of these
stalks is a finite `Λ`-module
(`AlgebraicGeometry.Etale.finite_limit_sheafFiber_upperStar_homology_rightDerived_of_tower`).

This generalises
`AlgebraicGeometry.Etale.finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower` from the
constant tower `Λ ⧸ ϖⁿ⁺¹` to towers of reductions of lattices, by the algebraic
`ModuleCat.finite_limit_of_exact_reduction` instead of a Bockstein argument with the integral
sheaf `Λ_T` (which has no analogue for a lattice with infinite monodromy on the étale site).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The stalks of the restrictions of the cohomology sheaves of derived direct images are
`Λ`-linear in the sheaf: `r • 𝟙` acts as `r`. -/
lemma sheafFiber_upperStarHomologyRightDerived_map_smul_apply (k : ℤ)
    {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (r : Λ)
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((upperStarHomologyRightDerived g j k).obj A)) :
    (pointSmallEtale s).sheafFiber.map ((upperStarHomologyRightDerived g j k).map (r • 𝟙 A)) x =
      r • x := by
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := (pointSmallEtale s).linear_sheafFiber (A := ModuleCat.{u + 1} Λ) (R := Λ)
  have h : (upperStarHomologyRightDerived g j k).map (r • 𝟙 A) = r • 𝟙 _ := by
    have h0 : (_root_.DerivedCategory.homologyFunctor _ k).map
        ((R((g)_*[ModuleCat.{u + 1} Λ])).map ((_root_.DerivedCategory.singleFunctor _ 0).map
          (r • 𝟙 A))) = r • 𝟙 _ := by
      simp only [Functor.map_smul, CategoryTheory.Functor.map_id]
    change (j)^*[ModuleCat.{u + 1} Λ].map _ = _
    rw [h0, Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [h, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

variable {ϖ : Λ}

/-- **Finiteness of the limit of the stalks of the higher direct images of a tower of
reductions.** Let `Λ` be noetherian and `ϖ`-adically complete, and `M` a tower of étale sheaves
of `Λ`-modules on `T` with `ϖⁿ⁺¹ Mₙ = 0` and short exact sequences
`0 ⟶ Mₙ --ιₙ--> Mₙ₊₁ ⟶ M₀ ⟶ 0` with `ιₙ ∘ tₙ = ϖ` and `tₙ ∘ ιₙ = ϖ`. If the stalks at `s` of the
`j^* Hᵏ(Rg_* Mₙ)` are finite, their limit is a finite `Λ`-module. -/
theorem finite_limit_sheafFiber_upperStar_homology_rightDerived_of_tower [IsNoetherianRing Λ]
    [IsAdicComplete (Ideal.span {ϖ}) Λ]
    (M : ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ι : ∀ n : ℕ, M.obj (op n) ⟶ M.obj (op (n + 1)))
    (hιt : ∀ n : ℕ, M.map (homOfLE (Nat.le_add_right n 1)).op ≫ ι n = ϖ • 𝟙 _)
    (htι : ∀ n : ℕ, ι n ≫ M.map (homOfLE (Nat.le_add_right n 1)).op = ϖ • 𝟙 _)
    (w : ∀ n : ℕ, ι n ≫ M.map (homOfLE (Nat.zero_le (n + 1))).op = 0)
    (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (w n)).ShortExact)
    (hkill : ∀ n : ℕ, ϖ ^ (n + 1) • 𝟙 (M.obj (op n)) = 0) (k : ℤ)
    (hfin : ∀ n : ℕ, Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((upperStarHomologyRightDerived g j k).obj (M.obj (op n))))) :
    Module.Finite Λ ↑(limit (M ⋙ upperStarHomologyRightDerived g j k ⋙
      (pointSmallEtale s).sheafFiber)) := by
  let H := upperStarHomologyRightDerived (Λ := Λ) g j k
  let St := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hsmul {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (r : Λ)
      (x : St.obj (H.obj A)) : St.map (H.map (r • 𝟙 A)) x = r • x :=
    sheafFiber_upperStarHomologyRightDerived_map_smul_apply g j s k r x
  have : ∀ n, Finite ((M ⋙ H ⋙ St).obj (op n)) := hfin
  refine ModuleCat.finite_limit_of_exact_reduction ϖ (M ⋙ H ⋙ St)
    (fun n ↦ (St.map (H.map (ι n))).hom) (fun n x ↦ ?_) (fun n x ↦ ?_) (fun n ↦ ?_)
    (fun n x ↦ ?_)
  · change (St.map (H.map (M.map _)) ≫ St.map (H.map (ι n))) x = _
    rw [← St.map_comp, ← H.map_comp, hιt, hsmul]
  · change (St.map (H.map (ι n)) ≫ St.map (H.map (M.map _))) x = _
    rw [← St.map_comp, ← H.map_comp, htι, hsmul]
  · let Tr := (R((g)_*[ModuleCat.{u + 1} Λ])).mapTriangle.obj (hS n).singleTriangle
    have hTr : Tr ∈ distTriang _ :=
      (R((g)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ (hS n).singleTriangle_distinguished
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (((_root_.DerivedCategory.HomologySequence.exact₂ Tr hTr k).map
        (j)^*[ModuleCat.{u + 1} Λ]).map St)
  · rw [← hsmul, hkill, H.map_zero, St.map_zero]
    rfl

end AlgebraicGeometry.Etale
