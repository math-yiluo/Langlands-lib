/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralDerivedLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RationalProperLowerStarAdjoint

/-!
# The proper direct image on `Dᵇc` is a left adjoint, over any field

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. For a proper morphism
`g : Z ⟶ Y` of separated `k`-schemes of finite type, the derived pushforward
`Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint, for each of the `ℓ`-adic coefficient rings
`Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (blueprints `theorem-exceptional-inverse-image--15`,
`theorem-exceptional-inverse-image--16`, `theorem-exceptional-inverse-image--17`):

* `isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`,
* `isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`, from the case
  of `𝒪̲_E` by inverting `ℓ`
  (`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_padicIntegersRingObj`),
* `isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`, from the case of
  the `E̲` by the 2-colimit argument
  (`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall`).

No assumption on `k` is made: these do not use Brown representability on the localizing closures,
which needs `cd_ℓ(k) < ∞`.

These instances are the input of the exceptional inverse image `Rg^!` on `Dᵇc` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- Blueprint `theorem-exceptional-inverse-image--15`: for a proper morphism
`g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint (SGA 4 XVIII, 3.1.4; SGA 4½,
[Th. finitude]; Bhatt–Scholze, Section 6.8). -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finiteIntermediateField ℓ g
    (fun E' ↦
      isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_isProper' ℓ E' g) E

/-- Blueprint `theorem-exceptional-inverse-image--16`: for a proper morphism
`g : Z ⟶ Y` and a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` is a left adjoint: invert `ℓ` in the case of `𝒪̲_E`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_padicIntegersRingObj ℓ g E

/-- Blueprint `theorem-exceptional-inverse-image--17`: for a proper morphism
`g : Z ⟶ Y`, the derived pushforward `Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` is a left adjoint: the
2-colimit of the cases of the finite subextensions `E ⊆ ℚ̄_ℓ`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar ℓ g).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall ℓ g

/-! ### The proper-only functor

The same statements for the proper-only functor `boundedConstructibleLowerStarOfIsProper`, which
is the general one restricted to proper morphisms (`boundedConstructibleLowerStarOfIsProper_eq`).
-/

/-- `Rg_*` is a left adjoint, for the proper-only functor
`Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧`. -/
instance isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (PadicIntegersRingObj.boundedConstructibleLowerStarOfIsProper ℓ E g).IsLeftAdjoint := by
  rw [PadicIntegersRingObj.boundedConstructibleLowerStarOfIsProper_eq]
  infer_instance

/-- `Rg_*` is a left adjoint, for the proper-only functor
`Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧`. -/
instance isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (ContinuousMapRingObj.boundedConstructibleLowerStarOfIsProper ℓ E g).IsLeftAdjoint := by
  rw [ContinuousMapRingObj.boundedConstructibleLowerStarOfIsProper_eq]
  infer_instance

/-- `Rg_*` is a left adjoint, for the proper-only functor
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`. -/
instance isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_padicAlgClRingObj :
    (boundedConstructibleLowerStarOfIsProper ℓ g).IsLeftAdjoint := by
  rw [boundedConstructibleLowerStarOfIsProper_eq]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
