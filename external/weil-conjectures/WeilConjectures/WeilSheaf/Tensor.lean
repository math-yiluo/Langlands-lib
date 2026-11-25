/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# Tensor products and constant twists of Weil sheaves

The tensor product `F ⊗ G` of a lisse Weil sheaf `F` with a Weil sheaf `G` is their tensor
product over the sheaf of rings `ℚ̄_ℓ,X̄` of continuous `ℓ`-adic functions. Since `F` is locally
free of finite rank over `ℚ̄_ℓ,X̄`, it is the internal hom `[F^∨, G]` out of the dual
`F^∨ = [F, ℚ̄_ℓ]`, with the Weil structure of internal homs
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`). The tensor product of the underlying sheaves of
`ℚ̄_ℓ`-modules, over the *discrete* ring `ℚ̄_ℓ`, would be the wrong object: already
`ℚ̄_ℓ,X̄ ⊗_{ℚ̄_ℓ} ℚ̄_ℓ,X̄` is much larger than `ℚ̄_ℓ,X̄`.

For a unit `b ∈ ℚ̄_ℓˣ` the *constant Weil twist* `F ⊗ 𝓑_b` of `F` is the tensor product of `F`
with the geometrically constant Weil line `𝓑_b` on which the geometric Frobenius acts by `b`.
Since `𝓑_b` is the unit sheaf with its Weil structure multiplied by `b`, the twist is the same
underlying sheaf as `F`, with its Weil structure `φ` replaced by `b • φ`; this is how it is defined
here. At a point with values in `𝔽_{qᵐ}` the local Frobenius of the twist is `bᵐ` times the
local Frobenius of `F`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.tensorObj`: the tensor product `F ⊗ G` of a lisse Weil sheaf
  `F` and a Weil sheaf `G`.
- `AlgebraicGeometry.WeilSheaf.constantTwist`: the constant Weil twist `F ⊗ 𝓑_b`.
- `AlgebraicGeometry.WeilSheaf.constantTwistInvIso`: twisting by `b` and then by `b⁻¹` gives
  back `F`.

The stalks and the cohomology of constant twists are computed in
`WeilConjectures.WeilSheaf.StalkConstantTwist` and
`WeilConjectures.WeilSheaf.ConstantTwistCohomology`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilCoefficients

/-- Multiplication by a unit `b` of `ℚ̄_ℓ`, as an automorphism of a sheaf of
`ℚ̄_ℓ,X`-modules. -/
noncomputable def smulIso {Z : Scheme.{u}} (b : (PadicAlgCl l)ˣ) (M : ProEtale.AdicSheaf l Z) :
    M ≅ M where
  hom := ProEtale.AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) M
  inv := ProEtale.AdicSheaf.smul (ULift.up ((b⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) M
  hom_inv_id := by
    rw [ProEtale.AdicSheaf.smul_smul, ← ProEtale.AdicSheaf.smul_one]
    exact congrArg (ProEtale.AdicSheaf.smul · M) (congrArg ULift.up (Units.inv_mul b))
  inv_hom_id := by
    rw [ProEtale.AdicSheaf.smul_smul, ← ProEtale.AdicSheaf.smul_one]
    exact congrArg (ProEtale.AdicSheaf.smul · M) (congrArg ULift.up (Units.mul_inv b))

end WeilCoefficients

namespace WeilSheaf

/-- The tensor product `F ⊗ G` of a lisse Weil sheaf `F` and a Weil sheaf `G`: their tensor
product over `ℚ̄_ℓ,X̄`, realized as the internal hom `[F^∨, G]` out of the dual of `F`, with the
Weil structure of internal homs. -/
noncomputable def tensorObj (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) : WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.ihom k₀ l X (F.dual hF).obj G.obj
  property := ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf hF.dual G.property

/-- The constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf by a unit `b ∈ ℚ̄_ℓˣ`: the tensor product
of `F` with the geometrically constant Weil line `𝓑_b` on which the geometric Frobenius acts
by `b`. It is the underlying sheaf of `F` with the Weil structure `b • φ`, so that at a point with
values in `𝔽_{qᵐ}` its local Frobenius is `bᵐ` times that of `F`, and every eigenvalue `α` of
the local Frobenius of `F` at a closed point of degree `m` becomes `bᵐ α`.
(blueprint: `proposition-twisting-weight-zero-adding-dual--2`) -/
noncomputable def constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l X where
  obj := .mk F.obj.carrier (F.obj.str ≪≫ WeilCoefficients.smulIso b F.obj.carrier)
  property := F.property

/-- A constant Weil twist of `F` is lisse exactly when `F` is: it has the same underlying étale
sheaf. -/
@[simp]
theorem isLisse_constantTwist {F : WeilSheaf k₀ l X} {b : (PadicAlgCl l)ˣ} :
    (F.constantTwist b).IsLisse ↔ F.IsLisse :=
  Iff.rfl

/-- A constant twist of a lisse Weil sheaf is lisse, the underlying sheaf being the same. -/
alias ⟨_, IsLisse.constantTwist⟩ := isLisse_constantTwist

/-- Twisting by `b` and then by `b⁻¹` gives back the Weil sheaf: both twists keep the
underlying sheaf, and the Weil structure `b⁻¹ • b • φ` is `φ`. -/
noncomputable def constantTwistInvIso (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (F.constantTwist b).constantTwist b⁻¹ ≅ F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change _ ≫ F.obj.str.hom = ((F.obj.str ≪≫ WeilCoefficients.smulIso b F.obj.carrier) ≪≫
      WeilCoefficients.smulIso b⁻¹ F.obj.carrier).hom ≫ 𝟙 _
    have : (WeilCoefficients.smulIso b⁻¹ F.obj.carrier).hom =
        (WeilCoefficients.smulIso b F.obj.carrier).inv := rfl
    simp only [this, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (congrArg (· ≫ _) ((frobeniusPullback k₀ l X).map_id _)).trans
      (Category.id_comp _))))


end WeilSheaf

end AlgebraicGeometry
