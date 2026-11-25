/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap

/-!

# Nearby cycles commute with Verdier duality

Let `M` be a trait model over the base (`NearbyCyclesModel.IsTraitModelOfBase`) of a separated
`k`-scheme `X` of finite type, over the strictly henselian trait `S = Spec k'⟦t⟧`, with special
fibre the `k'`-scheme `X'`. Its nearby cycles `Ψ = Li^* Rj_* Lε^*` carry the lax tensor map
`μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` (`NearbyCyclesModel.tensorMap`), which restricts to bounded
constructible complexes (`NearbyCyclesModel.boundedConstructibleTensorMap`), and the dualizing map
`θ_M = β_a(ℚ̄_ℓ) : Ψ ω_X ⟶ ω_{X'}` of a family `D` of dualizing maps
(`NearbyCyclesModel.NearbyDualizingData`, blueprint `prose-E-15`). The **duality
map** (`NearbyCyclesModel.nearbyDualityMap`)
```
δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K
```
is the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ` (`CategoryTheory.Verdier.nearbyDualityMap`).

**Gabber's theorem** (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.2; blueprint
`proposition-nearby-cycles-commute-verdier-duality`) says that `δ_{M,K}` is an isomorphism for every
bounded constructible `K` (`NearbyCyclesModel.isIso_nearbyDualityMap`, reduced by open locality to
affine total spaces, `NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`, and by compactification
to proper ones, `NearbyCyclesModel.isIso_nearbyDualityMap_of_isProper`). Here `D_X` is relative
to `k`; it is identified with the duality relative to `Ω` on the geometric generic fibre since `ε`
is an open immersion into a base change of fields, and this identification is part of `θ_M`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

/-- The lax tensor map `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of nearby cycles
(`NearbyCyclesModel.tensorMap`) on bounded constructible complexes. -/
noncomputable def boundedConstructibleTensorMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles hP).obj A ⊗ (boundedConstructibleNearbyCycles hP).obj B ⟶
      (boundedConstructibleNearbyCycles hP).obj (A ⊗ B) :=
  ObjectProperty.homMk (M.tensorMap (Profinite.padicAlgClRingObj ℓ) A.obj B.obj)

variable (ℓ) [IsSepClosed k'] [Algebra k k'] {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The **duality map** `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K` of a trait model `M` over the base
(blueprint `proposition-nearby-cycles-commute-verdier-duality`): the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ`,
with `θ_M` the dualizing map `β_a(ℚ̄_ℓ)` of the family `D`
(`NearbyCyclesModel.NearbyDualizingData`). -/
noncomputable def nearbyDualityMap (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (verdierDual ℓ K) ⟶
      verdierDual ℓ ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible ℓ)).obj K) :=
  Verdier.nearbyDualityMap (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ))
    (D.θ h) K

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
