/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdierTheorem

/-!
# The exceptional Künneth map is an isomorphism

For separated `k`-schemes of finite type `X`, `Y` and bounded constructible `M` on `X`, the
exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M`
(`ProEtale.CondensedRing.exceptionalKunnethMap`) is an isomorphism
(`ProEtale.CondensedRing.isIso_exceptionalKunnethMap`, blueprint
`proposition-exceptional-external-kunneth` for `f₁ = 𝟙_X`, `f₂ = a_Y`, `L₁ = M`, `L₂ = ℚ̄_ℓ`).
It is the Künneth–Verdier map `κ_{M,ℚ̄_ℓ}` up to isomorphisms
(`ProEtale.CondensedRing.isIso_kunnethVerdierMap_unit_iff`), which is invertible by the
Künneth–Verdier theorem (`ProEtale.CondensedRing.isIso_kunnethVerdierMap`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The exceptional Künneth map is an isomorphism** (blueprint
`proposition-exceptional-external-kunneth`, for `f₁ = 𝟙_X`, `f₂ = a_Y : Y ⟶ s`, `L₁ = M` and
`L₂ = ℚ̄_ℓ`): for bounded constructible `M` on `X`, the morphism `α : M ⊠ ω_Y ⟶ Rp_X^! M` adjoint
to the composite of the Künneth formula for `Rp_X!` and the counit of `Ra_{Y!} ⊣ Ra_Y^!` is
invertible. -/
instance isIso_exceptionalKunnethMap (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (exceptionalKunnethMap ℓ (Y := Y) M) :=
  (isIso_kunnethVerdierMap_unit_iff ℓ M).1 inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
