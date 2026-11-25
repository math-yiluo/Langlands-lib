/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.SixFunctors.NearbyCycles.PushforwardExchangeSquare

/-!

# The proper exchange of a proper trait model over the base

Let `M` be a trait model of a `k`-scheme `X` over the base (`NearbyCyclesModel.IsTraitModelOfBase`)
with proper total space, whose geometric generic fibre is all of `X ×_k Spec Ω`. The proper
exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism `a : X ⟶ Spec k`
(`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`) is an isomorphism on bounded
constructible complexes (`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app`).
The proof works on the ambient derived categories
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`) and then restricts
to `Dᵇc` through `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_hom`.

The proof compares `χ_a` with the proper exchange of the model `M` of its geometric generic fibre
over the trait as a model of `Spec Ω` (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`,
invertible by blueprint `prose-E-03` (2),
`NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`): by the square
law of the pullback exchanges, the two differ by `Ψ_S` of the base change morphism
`Lε^* Ra_* ⟶ Rg_* Lε^*` of the cartesian square of generic fibres, which is invertible by proper
base change (blueprint `proposition-proper-direct-image-constructible-complexes`,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`), and
by pullback exchanges along identities (`NearbyCyclesModel.pushforwardExchange_square_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Restriction to bounded constructible complexes -/

namespace NearbyCyclesModel

section Restricted

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- A component of the restricted pushforward exchange is invertible if the corresponding
component of the ambient pushforward exchange is. -/
lemma Hom.isIso_boundedConstructiblePushforwardExchange_app (φ : M.Hom N f.left f'.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj)) :
    IsIso ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K) := by
  rw [← ObjectProperty.isIso_hom_iff, Hom.boundedConstructiblePushforwardExchange_app_hom]
  exact hK

end Restricted

end NearbyCyclesModel

/-! ### The proper exchange of a proper trait model -/

namespace NearbyCyclesModel

/-- The model `M` of the geometric generic fibre (`NearbyCyclesModel.toGeneric`, with `ε = 𝟙`)
maps to `M` over `ε`, by the identities of the total space and of the geometric generic fibre. -/
@[simps]
def toGenericSelfHom {X X' : Scheme.{u}} (M : NearbyCyclesModel X X') :
    M.toGeneric.Hom M M.ε (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The trait as a model of its geometric generic point maps to the trait as a model of the base
point `Spec k`, over `Spec Ω ⟶ Spec k`, by identities. -/
@[simps]
noncomputable def traitGenericModelHom :
    (traitGenericModel k').Hom (traitModel k k') (traitModel k k').ε (𝟙 (point k').left) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [traitModel, traitGenericModel]
  comm_i := by simp [traitModel, traitGenericModel]
  comm_ε := by simp [traitModel, traitGenericModel]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback exchange of `NearbyCyclesModel.toGenericSelfHom` is invertible: all its
squares are identities. -/
instance isIso_pullbackExchange_toGenericSelfHom {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') : IsIso ((toGenericSelfHom M).pullbackExchange Λ) := by
  have : L(((toGenericSelfHom M).total)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have : L(((toGenericSelfHom M).generic)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have := isIso_mateEquiv_of_isEquivalence (derivedUpperStarLowerStarAdjunction Λ M.j)
    (derivedUpperStarLowerStarAdjunction Λ M.toGeneric.j)
    (pullbackSquareComparison Λ (toGenericSelfHom M).commSq_j).hom
  unfold Hom.pullbackExchange
  infer_instance

/-- The pullback exchange of `NearbyCyclesModel.traitGenericModelHom` is invertible: all its
squares are identities. -/
instance isIso_pullbackExchange_traitGenericModelHom :
    IsIso ((traitGenericModelHom k k').pullbackExchange Λ) := by
  have : L(((traitGenericModelHom k k').total)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have : L(((traitGenericModelHom k k').generic)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have := isIso_mateEquiv_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ (traitModel k k').j)
    (derivedUpperStarLowerStarAdjunction Λ (traitGenericModel k').j)
    (pullbackSquareComparison Λ (traitGenericModelHom k k').commSq_j).hom
  unfold Hom.pullbackExchange
  infer_instance

variable {k k'} (ℓ : ℕ) [Fact ℓ.Prime]
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

/-- **Proper exchange for a proper trait model over the base**, on the ambient derived
categories: if the total space of the trait model `M` over the base is proper over the trait and
its geometric generic fibre is all of `X ×_k Spec Ω`, the proper exchange
`χ_a : Ψ_S Ra_* K ⟶ Ra'_* Ψ_M K` of the structure morphism `a : X ⟶ Spec k` is invertible at
every bounded constructible `K` (for proper `X`). By the square law
`NearbyCyclesModel.pushforwardExchange_square_aux`, it agrees, up to invertible pullback
exchanges along identities and base change along identities, with the proper exchange of the
model of the geometric generic fibre (blueprint `prose-E-03` (2)) composed
with `Ψ_S` of the proper base change morphism of the square of generic fibres. -/
theorem IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient
    [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (h : M.IsTraitModelOfBase k q g) [IsProper q] [IsProper (toPoint X).left]
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hA : boundedConstructible _ A) :
    IsIso ((h.toTrait.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app A) := by
  have : IsNoetherian (point k).left := inferInstanceAs (IsNoetherian (Spec (.of k)))
  have : IsProper h.toTrait.total := ‹IsProper q›
  have hgen' : IsPullback M.ε g (toPoint X).left (traitModel k k').ε := by
    have e₀ : (traitModel k k').ε = traitGenericPoint k' ≫ traitToBase k k' :=
      (traitModel_j_traitToBase k k').symm
    rw [e₀, toPoint_left]
    exact hgen
  exact h.toTrait.isIso_pushforwardExchange_app_of_isProper (ℓ := ℓ)
    (𝟙 (point k).left) h.isTraitModelOver.isTraitModel.exists_over
    (isTraitModel_traitModel k k').exists_over
    (by
      change IsPullback M.i (toPoint X').left q (traitClosedPoint k')
      rw [toPoint_left]
      exact h.isTraitModelOver.isPullback_i)
    hgen' hA

/-- **Proper exchange for a proper trait model over the base**: if `X` is proper over `k`, the
total space of the trait model `M` over the base is proper over the trait and its geometric
generic fibre is all of `X ×_k Spec Ω`, the proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the
structure morphism is an isomorphism on bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`, restricted by
`NearbyCyclesModel.Hom.isIso_boundedConstructiblePushforwardExchange_app`). -/
theorem IsTraitModelOfBase.isIso_pushforwardExchange_app [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    (h : M.IsTraitModelOfBase k q g) [IsProper q] [IsProper (toPoint X).left]
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦𝐐⟧) : IsIso ((h.pushforwardExchange ℓ).app K) := by
  -- rewriting first makes the instances of the goal those of the restriction lemma
  have e1 : h.pushforwardExchange ℓ = Hom.boundedConstructiblePushforwardExchange
      (f := toPoint X) (f' := toPoint X') ℓ h.toTrait (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [e1]
  exact Hom.isIso_boundedConstructiblePushforwardExchange_app (f := toPoint X)
    (f' := toPoint X') ℓ h.toTrait _ _ K
    (h.isIso_pushforwardExchange_app_ambient ℓ hgen K.obj K.property)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
