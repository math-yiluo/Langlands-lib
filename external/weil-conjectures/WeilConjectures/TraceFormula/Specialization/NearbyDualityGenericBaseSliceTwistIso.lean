/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesZeroTwist
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityTwist
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingAutInvariant

/-!

# The twist of the nearby cycles of a generic slice

Let `M''` be the generic slice of a trait model over a generic base along a coordinate, over the
trait `Spec K⟦t⟧`, `K = k'(x)^alg`. The pullbacks of the dualizing complexes to the slice are those
of the slice twisted by `ℚ̄_ℓ(1)[2]`; over the separably closed field `K` the Tate twist
`ℚ̄_ℓ(1)` is trivial, so the twist used is `T = ℚ̄_ℓ(0)[2]`. This file defines the isomorphism
`κ : Ψ_{M''}(A ⊗ T) ≅ Ψ_{M''} A ⊗ T`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceTwistIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- The twist of the nearby cycles of the generic slice model by `T = ℚ̄_ℓ(0)[2]`:
`κ : Ψ_{M''}(A ⊗ T) ≅ Ψ_{M''} A ⊗ T` (`NearbyCyclesModel.zeroTwistIso` for the slice model). -/
noncomputable def genericSliceTwistIso
    (A : Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
        (A ⊗ boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2) ≅
      (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj A ⊗
        boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
          0 2 :=
  (genericSliceModel (traitSliceCoord k') hb).zeroTwistIso
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (pullback.snd b (traitSlice (traitSliceCoord k'))) 2 A

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
