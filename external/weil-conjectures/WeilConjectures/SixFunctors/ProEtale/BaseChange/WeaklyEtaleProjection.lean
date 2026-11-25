/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Functor.KanExtension.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived

/-!
# The projection formula for the extension by zero along a weakly étale morphism

For a weakly étale `f : V ⟶ U`, the extension by zero `f_!` of pro-étale sheaves of
`ℚ̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriek`) satisfies the projection
formula `f_!(F ⊗ f^* G) ≅ f_! F ⊗ G`
(`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriekTensorIso`): at the presheaf level both sides
are `⨁_α F(α) ⊗ G(W)` over the lifts `α` of `W` through `f`
(`AlgebraicGeometry.ProEtale.isIso_lanProjectionMap_weaklyEtale`), and sheafification is monoidal
and commutes with extension by zero
(`AlgebraicGeometry.ProEtale.presheafToSheafCompWeaklyEtaleLowerShriekIso`). This is the
pro-étale analogue of `AlgebraicGeometry.Etale.etaleLowerShriekTensorIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {V U : Scheme.{u}} (f : V ⟶ U) [WeaklyEtale f]

/-- **The presheaf-level projection formula for extension by zero along a weakly étale
morphism.** For presheaves `F` on `V_proét` and `G` on `U_proét`, the projection map
`Lan(F ⊗ f^*G) ⟶ Lan F ⊗ G` of the left Kan extension along the localization functor is an
isomorphism: at `W` both sides are `⨁_α F(α) ⊗ G(W)` over the lifts `α` of `W` through `f`. -/
theorem isIso_lanProjectionMap_weaklyEtale (F : V.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l)
    (G : U.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) :
    IsIso ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lanProjectionMap
      F G) := by
  have : HasCoproducts.{u} (WeilCoefficients.{u} l) := hasCoproducts_shrink.{u, u + 1}
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W ↦ ?_
  obtain ⟨ι, s, hs, hiso⟩ := SmallSite.exists_final_discrete_costructuredArrow_overMap
    (inferInstance : WeaklyEtale f) W.unop
  exact Functor.isIso_lanProjectionMap_app _ F G W s hiso

variable (l) in
/-- Extension by zero commutes with sheafification: `f_!(a P) ≅ a(Lan P)` for presheaves `P` on
`V_proét`, both functors being left adjoint to the restriction of presheaves. -/
noncomputable def presheafToSheafCompWeaklyEtaleLowerShriekIso :
    presheafToSheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l) ⋙
        weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lan ⋙
        presheafToSheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) (WeilCoefficients.{u} l)
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology U))).leftAdjointUniq
    ((((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lanAdjunction
      (WeilCoefficients.{u} l)).comp (sheafificationAdjunction (Scheme.ProEt.topology U)
        (WeilCoefficients.{u} l))).ofNatIsoRight (Iso.refl _))

variable (l) in
/-- **The projection formula for extension by zero along a weakly étale morphism**:
`f_!(F ⊗ f^*G) ≅ f_!F ⊗ G`. It is the sheafification of the presheaf-level projection formula
(`AlgebraicGeometry.ProEtale.isIso_lanProjectionMap_weaklyEtale`). -/
noncomputable def weaklyEtaleLowerShriekTensorIso
    (F : Sheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l))
    (G : Sheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l)) :
    (weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f).obj
        (F ⊗ ((f)^*[WeilCoefficients.{u} l]).obj G) ≅
      (weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f).obj F ⊗ G :=
  have := isIso_lanProjectionMap_weaklyEtale f F.obj G.obj
  (weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f).mapIso
      (tensorIso (asIso ((sheafificationAdjunction (Scheme.ProEt.topology V) _).counit.app F)).symm
          (asIso ((sheafificationAdjunction (Scheme.ProEt.topology V) _).counit.app
            (((f)^*[WeilCoefficients.{u} l]).obj G))).symm ≪≫
        Functor.Monoidal.μIso (presheafToSheaf (Scheme.ProEt.topology V)
          (WeilCoefficients.{u} l)) _ _ ≪≫
        (presheafToSheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)).mapIso
          (whiskerLeftIso F.obj ((sheafToPresheaf _ _).mapIso
            ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) f
              inferInstance).app G)))) ≪≫
    (presheafToSheafCompWeaklyEtaleLowerShriekIso l f).app _ ≪≫
    (presheafToSheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l)).mapIso
      (asIso ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lanProjectionMap
        F.obj G.obj)) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf (Scheme.ProEt.topology U)
      (WeilCoefficients.{u} l)) _ _).symm ≪≫
    whiskerLeftIso _ (asIso ((sheafificationAdjunction (Scheme.ProEt.topology U) _).counit.app G))

end AlgebraicGeometry.ProEtale
