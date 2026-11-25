/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction

/-!

# The transition maps `(𝒪_E ⧸ ℓⁿ⁺¹)_X ⟶ (𝒪_E ⧸ ℓⁿ)_X`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a subfield with ring of integers `𝒪_E` and `X` a scheme. The
condensed rings `(𝒪_E ⧸ ℓⁿ)̲ = Profinite.integersModPowRingObj ℓ E n`, the reductions
`𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` (`Profinite.padicIntegersRingObjToIntegersModPow`), their pullbacks
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` (`ProEtale.integersModPowReduction`) and the short exact sequences
`0 ⟶ 𝒪_{E,X} --ℓⁿ--> 𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X ⟶ 0` (`ProEtale.shortExact_integersModPowReduction`)
are set up in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction`.
This file adds the transition maps of the tower `n ↦ (𝒪_E ⧸ ℓⁿ)_X`:

* `Profinite.modPowRingObjTransition`: the morphism of condensed rings
  `(𝒪_E ⧸ ℓⁿ⁺¹)̲ ⟶ (𝒪_E ⧸ ℓⁿ)̲` induced by the transition map `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`,
  compatible with the reductions
  (`Profinite.padicIntegersRingObjToIntegersModPow_comp_modPowRingObjTransition`);
* `ProEtale.modPowTransition`: its pullback `(𝒪_E ⧸ ℓⁿ⁺¹)_X ⟶ (𝒪_E ⧸ ℓⁿ)_X` to `X_proét`,
  compatible with the reductions (`ProEtale.integersModPowReduction_comp_modPowTransition`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- The transition map `(𝒪_E ⧸ ℓⁿ⁺¹)̲ ⟶ (𝒪_E ⧸ ℓⁿ)̲` of ring objects of condensed abelian groups:
postcomposition with the transition map `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ` of discrete rings. -/
noncomputable def modPowRingObjTransition :
    integersModPowRingObj.{u} ℓ E (n + 1) ⟶ integersModPowRingObj ℓ E n :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap (PadicAlgCl.integersModPowTransition ℓ E n)
      continuous_of_discreteTopology)

instance : IsMonHom (modPowRingObjTransition.{u} ℓ E n) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap (PadicAlgCl.integersModPowTransition ℓ E n)
        continuous_of_discreteTopology)))

/-- The reductions `𝒪̲_E ⟶ (𝒪_E ⧸ ℓⁿ)̲` are compatible with the transition maps. -/
lemma padicIntegersRingObjToIntegersModPow_comp_modPowRingObjTransition :
    padicIntegersRingObjToIntegersModPow.{u} ℓ E (n + 1) ≫ modPowRingObjTransition ℓ E n =
      padicIntegersRingObjToIntegersModPow ℓ E n :=
  rfl

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  (n : ℕ)

/-- The transition map `(𝒪_E ⧸ ℓⁿ⁺¹)_X ⟶ (𝒪_E ⧸ ℓⁿ)_X` of coefficient ring objects on `X_proét`:
the pullback along `p_X` of the transition map `(𝒪_E ⧸ ℓⁿ⁺¹)̲ ⟶ (𝒪_E ⧸ ℓⁿ)̲` of condensed
rings. -/
noncomputable abbrev modPowTransition :
    condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) X ⟶
      condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X :=
  coefficientMap (Profinite.modPowRingObjTransition ℓ E n) X

example : IsMonHom (modPowTransition X ℓ E n) := inferInstance

example : IsMonHom (integersModPowReduction X ℓ E n) := inferInstance

/-- The reductions `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` are compatible with the transition maps. -/
@[reassoc]
lemma integersModPowReduction_comp_modPowTransition :
    integersModPowReduction X ℓ E (n + 1) ≫ modPowTransition X ℓ E n =
      integersModPowReduction X ℓ E n := by
  rw [← coefficientMap_comp,
    Profinite.padicIntegersRingObjToIntegersModPow_comp_modPowRingObjTransition]

end AlgebraicGeometry.ProEtale
