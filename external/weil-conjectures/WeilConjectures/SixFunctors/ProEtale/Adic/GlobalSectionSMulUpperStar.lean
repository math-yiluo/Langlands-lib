/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification
public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionSMul

/-!
# Pullback of the multiplication by a global section

For a morphism `q : Z ⟶ Y` and a global section `f` of `ℚ̄_ℓ,Y`, the pullback `q^*` of sheaves of
`ℚ̄_ℓ`-modules over the constant `ℓ`-adic sheaves carries the multiplication by `f` to the
multiplication by `f ∘ q`
(`AlgebraicGeometry.ProEtale.AdicSheaf.adicUpperStar_map_globalSMul_app`): the pullback is left
adjoint to the pushforward, which carries the multiplication by `f ∘ q` to the multiplication by
`f` (`AlgebraicGeometry.ProEtale.AdicSheaf.adicLowerStar_map_globalSMul_app`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Z Y : Scheme.{u}} (q : Z ⟶ Y)
  (f : (adicConstantSheaf l Y).obj.obj (Opposite.op (proEtTop Y)))

/-- **The pullback intertwines the multiplications by a global section** `f` of `ℚ̄_ℓ,Y` and by
its pullback `f ∘ q`. -/
lemma adicUpperStar_map_globalSMul_app (G : AdicSheaf l Y) :
    (q)^*ᵃ[l].map ((globalSMul f).app G) =
      (globalSMul (pullbackGlobalSection q f)).app ((q)^*ᵃ[l].obj G) :=
  (adicUpperStarLowerStarAdjunction l q).map_app_eq_of_right _ _
    (fun N ↦ adicLowerStar_map_globalSMul_app q (sectionSheafHom_pullbackGlobalSection q f) N) G

end AlgebraicGeometry.ProEtale.AdicSheaf
