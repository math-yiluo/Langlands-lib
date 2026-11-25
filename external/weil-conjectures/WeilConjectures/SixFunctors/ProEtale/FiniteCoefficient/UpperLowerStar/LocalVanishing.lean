/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Restriction of global sections vanishing on a pro-étale neighbourhood

Let `W` be an object of the small pro-étale site of `Y`, with structure morphism `g : W ⟶ Y`.
A global section of a sheaf `M` on `Y` whose restriction to `W` vanishes has vanishing pullback
along `g` (`AlgebraicGeometry.ProEtale.globalSectionsToUpperStar_eq_zero_of_restrict_eq_zero`).
Indeed the restriction `Γ(Y, g_* g^* M) ⟶ Γ(W, g_* g^* M)`, that is
`Γ(W, g^* M) ⟶ Γ(W ×_Y W, g^* M)`, is split injective, the diagonal of `W` being a section of
the projection `W ×_Y W ⟶ W`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]

/-- For `g : Z ⟶ Y` weakly étale, the diagonal section `Y ×_Y Z ⟶ Z ×_Y Z` of the base change
along `g` of `g`, as a morphism of the small pro-étale site of `Z`. -/
noncomputable def overPullbackDiagonal :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (ProEt.mk (𝟙 Y)) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (ProEt.mk g) :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.snd _ _) (pullback.snd _ _) rfl)
    (by simp) trivial

lemma overPullbackDiagonal_comp_map :
    overPullbackDiagonal g ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
          ((ProEt.isTerminalMkId Y).from (ProEt.mk g)) = 𝟙 _ := by
  ext : 1
  apply pullback.hom_ext
  · simp only [Functor.id_obj, Functor.const_obj_obj, overPullbackDiagonal,
      MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom, Comma.comp_left,
      Over.homMk_left, MorphismProperty.Over.pullback_map_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, MorphismProperty.Comma.id_hom,
      Comma.id_left, Category.id_comp]
    exact (pullback.condition (f := (ProEt.mk (𝟙 Y)).hom) (g := g)).symm.trans
      (Category.comp_id _)
  · simp [overPullbackDiagonal]

/-- **A global section vanishing on a pro-étale neighbourhood has vanishing pullback.** Let
`g : Z ⟶ Y` be weakly étale, and let `x` be a family of global sections of `M` whose
restriction to `Z` vanishes. Then the restriction of `x` along `g`, `Γ(Y, M) ⟶ Γ(Z, g^* M)`,
vanishes. -/
lemma globalSectionsToUpperStar_eq_zero_of_restrict_eq_zero
    {M : Sheaf (ProEt.topology Y) A} {P : A} (x : P ⟶ (Sheaf.Γ _ A).obj M)
    (hx : x ≫ (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.app M ≫
      M.obj.map ((ProEt.isTerminalMkId Y).from (ProEt.mk g)).op = 0) :
    x ≫ (globalSectionsToUpperStar A g).app M = 0 := by
  set ρ := (ProEt.isTerminalMkId Y).from (ProEt.mk g)
  set N := (g)^*[A].obj M
  let u := ((upperStarLowerStarAdjunction A g).unit.app M).hom
  have hsplit : ((g)_*[A].obj N).obj.map ρ.op ≫
      N.obj.map (overPullbackDiagonal g).op = 𝟙 _ := by
    change N.obj.map _ ≫ N.obj.map _ = _
    rw [← N.obj.map_comp]
    change N.obj.map ((overPullbackDiagonal g ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map ρ).op) = _
    rw [overPullbackDiagonal_comp_map]
    exact N.obj.map_id _
  have hnat := u.naturality ρ.op
  have h₀ : x ≫ (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.app M ≫
      u.app (op (ProEt.mk (𝟙 Y))) = 0 := by
    have : Mono (((g)_*[A].obj N).obj.map ρ.op) := mono_of_mono_fac hsplit
    rw [← cancel_mono (((g)_*[A].obj N).obj.map ρ.op)]
    simp only [Category.assoc, zero_comp]
    erw [← hnat]
    rw [← Category.assoc, ← Category.assoc, Category.assoc x]
    erw [hx]
    rw [zero_comp]
  have hΓ := (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.naturality
    ((upperStarLowerStarAdjunction A g).unit.app M)
  rw [globalSectionsToUpperStar_app, globalSectionsLowerStarIso_hom_app']
  have h₁ : x ≫ (Sheaf.Γ _ A).map ((upperStarLowerStarAdjunction A g).unit.app M) ≫
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.app ((g)_*[A].obj N) = 0 := by
    erw [hΓ]
    exact h₀
  simp only [← Category.assoc] at h₁ ⊢
  rw [h₁, zero_comp, zero_comp]

/-- **A global section vanishing on a pro-étale neighbourhood has vanishing pullback**, for
sheaves of modules: the elementwise form of
`AlgebraicGeometry.ProEtale.globalSectionsToUpperStar_eq_zero_of_restrict_eq_zero`. -/
lemma globalSectionsToUpperStar_apply_eq_zero_of_restrict_eq_zero {R : Type (u + 1)} [Ring R]
    {M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)}
    (b : (Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} R)).obj M)
    (hb : M.obj.map ((ProEt.isTerminalMkId Y).from (ProEt.mk g)).op
      ((Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId Y)).hom.app M b) = 0) :
    (globalSectionsToUpperStar _ g).app M b = 0 := by
  let x : ModuleCat.of R R ⟶ (Sheaf.Γ _ _).obj M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ b)
  have h := globalSectionsToUpperStar_eq_zero_of_restrict_eq_zero _ g x (by
    ext
    simpa [x] using hb)
  simpa [x] using congrArg (fun φ ↦ φ (1 : R)) h

end AlgebraicGeometry.ProEtale
