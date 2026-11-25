/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleProjection

/-!
# Extension by zero of `ℓ`-adic sheaves along a weakly étale morphism

For a weakly étale `f : V ⟶ U`, the pullback `f^*` of sheaves of `ℚ̄_ℓ`-modules is a right
adjoint, with left adjoint the extension by zero `f_!`
(`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriekAdjunction`). Hence the pullback `f^*` of
sheaves of `ℚ̄_ℓ,U`-modules preserves limits, and has a left adjoint by the special adjoint functor
theorem: the extension by zero `f_!` of `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicWeaklyEtaleLowerShriek`). On free modules it is the free module
on the extension by zero (`AlgebraicGeometry.ProEtale.adicWeaklyEtaleLowerShriekFreeIso`), whose
underlying sheaf `ℚ̄_ℓ,U ⊗ f_! P` is, by the projection formula, the extension by zero of the
underlying sheaf `ℚ̄_ℓ,V ⊗ P` (`AlgebraicGeometry.ProEtale.adicWeaklyEtaleLowerShriekFreeXIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {V U : Scheme.{u}} (f : V ⟶ U) [WeaklyEtale f]

instance : PreservesLimits ((f)^*[WeilCoefficients.{u} l]) :=
  (weaklyEtaleLowerShriekAdjunction (WeilCoefficients.{u} l) f).rightAdjoint_preservesLimits

instance : PreservesLimits ((f)^*ᵃ[l]) := by
  have : PreservesLimits ((f)^*ᵃ[l] ⋙ AdicSheaf.forget V) :=
    inferInstanceAs (PreservesLimits (AdicSheaf.forget U ⋙ (f)^*[WeilCoefficients.{u} l]))
  exact preservesLimits_of_reflects_of_preserves _ (AdicSheaf.forget V)

instance : (f)^*ᵃ[l].IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (D := AdicSheaf l U)
    (isCoseparator_coseparator (AdicSheaf l U)) (f)^*ᵃ[l]

variable (l) in
/-- The extension by zero `f_!` of sheaves of modules over the constant `ℓ`-adic sheaves along a
weakly étale `f`: the left adjoint of the pullback `f^*`. -/
noncomputable def adicWeaklyEtaleLowerShriek : AdicSheaf l V ⥤ AdicSheaf l U :=
  (f)^*ᵃ[l].leftAdjoint

variable (l) in
/-- The adjunction `f_! ⊣ f^*` on `ℓ`-adic sheaves, for `f` weakly étale. -/
noncomputable def adicWeaklyEtaleLowerShriekAdjunction :
    adicWeaklyEtaleLowerShriek l f ⊣ (f)^*ᵃ[l] :=
  Adjunction.ofIsRightAdjoint _

instance : (adicWeaklyEtaleLowerShriek l f).Additive :=
  (adicWeaklyEtaleLowerShriekAdjunction l f).left_adjoint_additive

variable (l) in
/-- The extension by zero of a free module is the free module on the extension by zero: both
are left adjoint to `M ↦ f^* M.X`. -/
noncomputable def adicWeaklyEtaleLowerShriekFreeIso :
    Mod.free (adicConstantSheaf l V) ⋙ adicWeaklyEtaleLowerShriek l f ≅
      weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f ⋙ Mod.free (adicConstantSheaf l U) :=
  Adjunction.leftAdjointUniq
    ((Mod.freeForgetAdjunction (adicConstantSheaf l V)).comp
      (adicWeaklyEtaleLowerShriekAdjunction l f))
    ((weaklyEtaleLowerShriekAdjunction (WeilCoefficients.{u} l) f).comp
      (Mod.freeForgetAdjunction (adicConstantSheaf l U)))

variable (l) in
/-- **The underlying sheaf of the extension by zero of a free module**: for a sheaf `P` of
`ℚ̄_ℓ`-modules on `V`, the underlying sheaf of `f_!(ℚ̄_ℓ,V ⊗ P)` is the extension by zero of
`ℚ̄_ℓ,V ⊗ P`, by the projection formula
`f_!(ℚ̄_ℓ,V ⊗ P) ≅ f_!(f^* ℚ̄_ℓ,U ⊗ P) ≅ ℚ̄_ℓ,U ⊗ f_! P`. -/
noncomputable def adicWeaklyEtaleLowerShriekFreeXIso
    (P : Sheaf (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)) :
    ((adicWeaklyEtaleLowerShriek l f).obj ((Mod.free (adicConstantSheaf l V)).obj P)).X ≅
      (weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f).obj
        ((Mod.free (adicConstantSheaf l V)).obj P).X :=
  (Mod.forget _).mapIso ((adicWeaklyEtaleLowerShriekFreeIso l f).app P) ≪≫
    (β_ _ _) ≪≫ (weaklyEtaleLowerShriekTensorIso l f P (adicConstantSheaf l U)).symm ≪≫
    (weaklyEtaleLowerShriek (WeilCoefficients.{u} l) f).mapIso
      (β_ _ _ ≪≫ whiskerRightIso (upperStarAdicConstantSheafIsoOfWeaklyEtale l f) P)

end AlgebraicGeometry.ProEtale
