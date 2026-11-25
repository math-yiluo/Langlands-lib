/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowTowerLocallyConstant

/-!
# Uniform finite local constancy along a tower of extensions killed by `Iⁿ⁺¹`

Let `Λ` be a noetherian ring and `I` an ideal with all `Λ ⧸ Iⁿ` finite (the case `Λ = 𝒪_E`,
`I = (ℓ)`), `g : T ⟶ Y` a morphism of schemes and `j : S ⟶ Y` a stratum. Let `F : ℕ → Sh(T_ét, Λ)`
be sheaves of `Λ`-modules with `F n` killed by `Iⁿ⁺¹`, and short exact sequences
`0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0`: for instance the reductions `F n = L ⧸ Iⁿ⁺¹` of an `𝒪_E`-lattice
`L` in a lisse sheaf, the first map being the multiplication by `ϖⁿ⁺¹` for `I = (ϖ)`. If over `j`
all the `Hᵏ(Rg_* F 0)` restrict to finite locally constant sheaves of `Λ`-modules, then so do all
the `Hᵏ(Rg_* F n)`
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_upperStar_homology_rightDerived_of_tower`),
and they are `IsSetFLC`
(`AlgebraicGeometry.Etale.isSetFLC_upperStar_homology_rightDerived_of_tower`).

This generalises the case of the constant tower `F n = Λ ⧸ Iⁿ⁺¹`
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_upperStar_higherDirectImageQuotPowTower`)
to the towers of reductions of lattices in lisse `ℓ`-adic sheaves, as needed for the finiteness
theorem for lisse sheaves (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`).
Unlike `AlgebraicGeometry.Etale.flcProperty_rightDerived_lowerStar_of_tower`, the ring `Λ` need
not be finite: finite local constancy is that of sheaves of `Λ`-modules, and extensions are
controlled by the annihilators `Iⁿ⁺¹`
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)

/-- The restriction to `j : S ⟶ Y` of the `k`-th cohomology sheaf of the derived direct image
along `g` of a sheaf of `Λ`-modules placed in degree `0`, as a functor. -/
noncomputable abbrev upperStarHomologyRightDerived (k : ℤ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  _root_.DerivedCategory.singleFunctor _ 0 ⋙ R((g)_*[ModuleCat.{u + 1} Λ]) ⋙
    _root_.DerivedCategory.homologyFunctor _ k ⋙ (j)^*[ModuleCat.{u + 1} Λ]

/-- If `r` kills a sheaf of `Λ`-modules on `T`, it kills the restrictions to `S` of the
cohomology sheaves of its derived direct image. -/
lemma smul_id_upperStarHomologyRightDerived_obj
    {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {r : Λ} (hr : r • 𝟙 A = 0)
    (k : ℤ) : r • 𝟙 ((upperStarHomologyRightDerived g j k).obj A) = 0 := by
  have := congrArg (fun f ↦ (_root_.DerivedCategory.homologyFunctor _ k).map
    ((R((g)_*[ModuleCat.{u + 1} Λ])).map ((_root_.DerivedCategory.singleFunctor _ 0).map f))) hr
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at this
  change r • 𝟙 ((j)^*[ModuleCat.{u + 1} Λ].obj _) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, this, Functor.map_zero]

variable {I : Ideal Λ}

/-- **Uniform finite local constancy along a tower of extensions.** Let `Λ` be noetherian with all
`Λ ⧸ Iⁿ` finite and `F : ℕ → Sh(T_ét, Λ)` with `F n` killed by `Iⁿ⁺¹` and short exact sequences
`0 ⟶ F 0 ⟶ F (n + 1) ⟶ F n ⟶ 0`. If all the `j^* Hᵏ(Rg_* F 0)`, `k : ℤ`, are finite locally
constant sheaves of `Λ`-modules, then so are all the `j^* Hᵏ(Rg_* F n)`: by the long exact
sequences of cohomology, `j^* Hᵏ(Rg_* F (n + 1))` is an extension, killed by `Iⁿ⁺²`, of a kernel
by a cokernel of morphisms of finite locally constant sheaves. -/
theorem isFiniteLocallyConstantSheaf_upperStar_homology_rightDerived_of_tower
    [IsNoetherianRing Λ] [∀ n, Finite (Λ ⧸ I ^ n)]
    (F : ℕ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ n, ∀ r ∈ I ^ (n + 1), r • 𝟙 (F n) = 0)
    (SC : ℕ → ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hSC : ∀ n, (SC n).ShortExact) (e₁ : ∀ n, (SC n).X₁ ≅ F 0)
    (e₂ : ∀ n, (SC n).X₂ ≅ F (n + 1)) (e₃ : ∀ n, (SC n).X₃ ≅ F n)
    (h₀ : ∀ k : ℤ, flcModuleProperty Λ S ((upperStarHomologyRightDerived g j k).obj (F 0)))
    (n : ℕ) (k : ℤ) :
    flcModuleProperty Λ S ((upperStarHomologyRightDerived g j k).obj (F n)) := by
  let H (k : ℤ) := upperStarHomologyRightDerived (Λ := Λ) g j k
  have hiso {A B : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : A ≅ B) (k : ℤ)
      (h : flcModuleProperty Λ S ((H k).obj B)) : flcModuleProperty Λ S ((H k).obj A) := by
    have := h
    exact IsFiniteLocallyConstantSheaf.of_iso ((H k).mapIso e).symm
  have hker {X Z : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcModuleProperty Λ S X) (hZ : flcModuleProperty Λ S Z) :
      flcModuleProperty Λ S (kernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.kernel φ
  have hcoker {X Z : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcModuleProperty Λ S X) (hZ : flcModuleProperty Λ S Z) :
      flcModuleProperty Λ S (cokernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.cokernel φ
  induction n generalizing k with
  | zero => exact h₀ k
  | succ n ih =>
    let Tr := (R((g)_*[ModuleCat.{u + 1} Λ])).mapTriangle.obj (hSC n).singleTriangle
    have hTr : Tr ∈ distTriang _ :=
      (R((g)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ (hSC n).singleTriangle_distinguished
    let G := (j)^*[ModuleCat.{u + 1} Λ]
    have hext {S' : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        (hS' : S'.ShortExact) (h₁ : flcModuleProperty Λ S S'.X₁)
        (h₃ : flcModuleProperty Λ S S'.X₃)
        (hQ : ∀ r ∈ I ^ (n + 2), r • 𝟙 S'.X₂ = 0) : flcModuleProperty Λ S S'.X₂ := by
      have := h₁; have := h₃
      exact IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero (I ^ (n + 2)) hS' hQ
    refine hiso (e₂ n).symm k ((flcModuleProperty Λ S).prop_of_exact_five_of_mid
      (fun X ↦ ∀ r ∈ I ^ (n + 2), r • 𝟙 X = 0) hker hcoker hext
      (G.map (_root_.DerivedCategory.HomologySequence.δ Tr (k - 1) k (by lia)))
      (G.map ((_root_.DerivedCategory.homologyFunctor _ k).map Tr.mor₁))
      (G.map ((_root_.DerivedCategory.homologyFunctor _ k).map Tr.mor₂))
      (G.map (_root_.DerivedCategory.HomologySequence.δ Tr k (k + 1) (by lia))) _ _ _
      ((_root_.DerivedCategory.HomologySequence.exact₁ Tr hTr (k - 1) k (by lia)).map G)
      ((_root_.DerivedCategory.HomologySequence.exact₂ Tr hTr k).map G)
      ((_root_.DerivedCategory.HomologySequence.exact₃ Tr hTr k (k + 1) (by lia)).map G)
      (hiso (e₃ n) (k - 1) (ih (k - 1))) (hiso (e₁ n) k (h₀ k)) (hiso (e₃ n) k (ih k))
      (hiso (e₁ n) (k + 1) (h₀ (k + 1))) fun r hr ↦ ?_)
    have hr' : r • 𝟙 (SC n).X₂ = 0 := by
      rw [← cancel_mono (e₂ n).hom, Linear.smul_comp, Category.id_comp, zero_comp,
        ← Category.comp_id (e₂ n).hom, ← Linear.comp_smul, hF (n + 1) r hr, comp_zero]
    exact smul_id_upperStarHomologyRightDerived_obj g j hr' k

/-- **The levels of a tower of extensions are `IsSetFLC` on the stratum**, under the hypotheses
of `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_upperStar_homology_rightDerived_of_tower`:
`j^* Hᵏ(Rg_* F n)` is killed by `Iⁿ⁺¹`, hence a finite locally constant sheaf of
`Λ ⧸ Iⁿ⁺¹`-modules, whose underlying sheaf of sets is finite locally constant. -/
theorem isSetFLC_upperStar_homology_rightDerived_of_tower
    [IsNoetherianRing Λ] [∀ n, Finite (Λ ⧸ I ^ n)]
    (F : ℕ → Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ n, ∀ r ∈ I ^ (n + 1), r • 𝟙 (F n) = 0)
    (SC : ℕ → ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hSC : ∀ n, (SC n).ShortExact) (e₁ : ∀ n, (SC n).X₁ ≅ F 0)
    (e₂ : ∀ n, (SC n).X₂ ≅ F (n + 1)) (e₃ : ∀ n, (SC n).X₃ ≅ F n)
    (h₀ : ∀ k : ℤ, flcModuleProperty Λ S ((upperStarHomologyRightDerived g j k).obj (F 0)))
    (n : ℕ) (k : ℤ) :
    IsSetFLC ((upperStarHomologyRightDerived g j k).obj (F n)) := by
  have := isFiniteLocallyConstantSheaf_upperStar_homology_rightDerived_of_tower g j F hF SC hSC
    e₁ e₂ e₃ h₀ n k
  have hkill : ∀ r ∈ I ^ (n + 1), r • 𝟙 ((upperStarHomologyRightDerived g j k).obj (F n)) = 0 :=
    fun r hr ↦ smul_id_upperStarHomologyRightDerived_obj g j (hF n r hr) k
  let e := Sheaf.restrictScalarsCoextendScalarsIso (J := I ^ (n + 1)) _ hkill
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((Sheaf.restrictScalars _
        (Ideal.Quotient.mk (I ^ (n + 1)))).obj ((Sheaf.coextendScalars _ (I ^ (n + 1))).obj
          ((upperStarHomologyRightDerived g j k).obj (F n)))) :=
    IsFiniteLocallyConstantSheaf.of_iso e.symm
  have := IsFiniteLocallyConstantSheaf.of_restrictScalars (I ^ (n + 1))
    ((Sheaf.coextendScalars _ (I ^ (n + 1))).obj
      ((upperStarHomologyRightDerived g j k).obj (F n)))
  exact IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mapIso e)
    ((IsFiniteLocallyConstantSheaf.isSetFLC this).restrictScalars
      (Ideal.Quotient.mk (I ^ (n + 1))))

end AlgebraicGeometry.Etale
