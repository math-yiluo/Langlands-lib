/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Nearby cycles on bounded constructible complexes

For a model `M` of `X` with special fibre `X'` whose nearby cycles `Ψ = i^* Rj_* ε^*` preserve
bounded constructible complexes
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.PreservesBoundedConstructible`;
for models of finite type over a strictly henselian trait this is Deligne's finiteness
theorem, SGA 4½, [Th. finitude], Thm. 3.2), the restriction of `Ψ` to the bounded
constructible derived categories
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructibleNearbyCycles`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The nearby cycles of the model `M` preserve bounded constructible complexes. -/
def PreservesBoundedConstructible : Prop :=
  ∀ K, boundedConstructible (condensedRingObj Λ X) K →
    boundedConstructible (condensedRingObj Λ X') ((M.nearbyCycles Λ).obj K)

variable {Λ M}

/-- The nearby cycles `Ψ : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X')⟦Λ⟧` of a model whose nearby cycles preserve bounded
constructible complexes: the restriction of `nearbyCycles`. -/
noncomputable def boundedConstructibleNearbyCycles (hM : M.PreservesBoundedConstructible Λ) :
    Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X')⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ M.nearbyCycles Λ)
    fun K ↦ hM K.obj K.property

/-- The restricted nearby cycles are compatible with the inclusions. -/
noncomputable def boundedConstructibleNearbyCyclesCompatibility
    (hM : M.PreservesBoundedConstructible Λ) :
    boundedConstructibleNearbyCycles hM ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ M.nearbyCycles Λ :=
  ObjectProperty.liftCompιIso _ _ _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
