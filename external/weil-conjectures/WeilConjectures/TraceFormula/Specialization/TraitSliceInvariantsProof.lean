/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariants
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGenericSliceTraitInvariance

/-!

# The generic-slicing identification of nearby cycles with invariants

Let `M''` be the geometric slice of a model `M` over `S = Spec k'⟦t⟧` along the generic slice
`Spec K⟦t⟧ ⟶ 𝔸¹_S`, and `θ : M'' ⟶ M_T` its map to the change of trait
(`NearbyCyclesModel.geometricSliceTraitChangeHom`). This file proves that the pullback exchange of
`θ` is the inclusion of the invariants of the pro-`p` kernel `P'`
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_isIso_cartesian`),
given the invertibility of the pullback exchange of the cartesian part of the slice ("M1 at `T`").
It follows from the same statement for the slicing exchange
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian`), since the
exchange of the change of trait `M_T ⟶ M` is invertible
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`).

The consequences for the generic slice,
`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom` and
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`, are stated here
with the extra hypothesis that `Lε^* C` extends to a bounded constructible complex on the total
space; the invertibility of the cartesian step is
`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGaloisModelHom`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (x : K) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

variable [IsSepClosed k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

-- the averages over `P' ⧸ V` on the concrete slice are large terms
/-- **The exchange of the slice of the change of trait is the inclusion of the invariants, given
the cartesian step**: the analogue of
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian` for the
exchange `α_θ`, deduced from it through the invertible exchange of the change of trait.

The average is transported along that exchange
(`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_of_isIso`, then
`NearbyCyclesModel.exists_retraction_pullbackExchange_app_of_isIso`), combined in
`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_of_isIso_id`. -/
theorem exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_isIso_cartesian [IsAlgClosed K]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)
    (hM1 : IsIso (((((baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).traitChangeModelHom
        (traitGenericField K) (baseChangeTotalStructure hM b hb (traitSlice x) (traitSlice_over x))
        q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb (traitSlice x) (traitSlice_over x))).comp
          (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).fromCartesian).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app C)) :
    ∃ (V : Subgroup (GenericAut k' K)) (_ : Fintype (GenericAut k' K ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).autAction
          (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) =
            𝟙 _) ∧
      ∃ r, ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ r = 𝟙 _ ∧
        Fintype.card (GenericAut k' K ⧸ V) •
          (r ≫ ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C) =
        ∑ σ : GenericAut k' K ⧸ V,
          (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ.out).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have key := exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian
    hM b hb (traitSlice x) (traitSlice_over x) hC hB eB hM1
  have hψ := isIso_pullbackExchange_baseChangeHom_traitMap_of_generic (ℓ := ℓ) (K := K) hM
    (A := C) hC
  have t := exists_subgroup_pullbackExchange_of_comp_of_isIso_id (Profinite.padicAlgClRingObj ℓ)
    (X := X) (M₀ := baseChange hM b hb (traitSlice x) (traitSlice_over x))
    (M₁ := baseChange hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)) (M₂ := M)
    (geometricSliceTraitChangeHom hM x hb)
    (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _))
    (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x))
    (geometricSliceTraitChangeHom_special_comp hM x hb)
    (geometricSliceTraitChangeHom_total_comp hM x hb)
    (geometricSliceTraitChangeHom_generic_comp hM x hb) C (by exact_mod_proofs hψ)
    (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x)) (by exact_mod_proofs key)
  exact_mod_proofs t

variable [Fact (ringChar k').Prime]

-- the statement involves the actions of `P' ⧸ V` on the concrete slice trait
/-- **Nearby cycles of the slice of the change of trait are the `P'`-invariants** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Facts about traits", identification (2); SGA
4½, [Th. finitude], §3.7; SGA 7, Exp. XIII, §1.3). The geometric slice `M''` of `M` is the slice of
the change of trait `M_T = M ×_S Spec K⟦t⟧` along the section `x` of `𝔸¹_{K⟦t⟧}`
(`NearbyCyclesModel.geometricSliceTraitChangeHom`). The pro-`p` kernel
`P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` of the map of inertia groups (`NearbyCyclesModel.GenericAut`)
acts on the nearby cycles of both (`NearbyCyclesModel.baseChangeAut`), trivially on those of
`M_T` by the invariance under change of trait. For bounded constructible `C`:
* the action of `P'` on `Ψ_{M''} C` factors through a finite quotient: a subgroup `V` of finite
  index acts trivially (continuity of the action, from the finiteness of `Ψ_{M''} C`);
* the pullback exchange `α_θ : Ψ_{M_T} C ⟶ Ψ_{M''} C` is the inclusion of the invariants: it is a
  split monomorphism whose idempotent is `1 / [P' : V]` times the sum of the actions of
  representatives of `P' ⧸ V` (Hochschild–Serre for the pro-`p` cover
  `Spec Ω_K ⟶ (Spec K⟦t⟧ ×_S Spec Ω)_red`; `[P' : V]` is a power of `p`, invertible in `ℚ̄_ℓ`).

The restriction `Lε^* C` is assumed to extend to a bounded constructible complex `B` on the total
space (`eB`), for the finiteness of the torsion nearby cycles. The proof is
`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_isIso_cartesian`, given
the invertibility of the pullback exchange of the cartesian part `N'' ⟶ M` of the slice (the
slice is the invariant part of its Galois layer, "M1 at `T`"). -/
theorem exists_subgroup_pullbackExchange_sliceTraitChangeHom
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) :
    ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ r, ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ r = 𝟙 _ ∧
        Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) •
          (r ≫ ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C) =
        ∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have key := exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_isIso_cartesian hM
    (traitSliceCoord k') hb hC hB eB
    (by transport_exact isIso_pullbackExchange_traitSliceGaloisModelHom hM b hb (ℓ := ℓ) hC)
  exact_mod_proofs key

-- the statement and the averages involve the nearby cycles of the slice
/-- **The generic-slicing identification of nearby cycles with invariants** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Facts about traits", identification (2)): for
a model `M` over `S = Spec k'⟦t⟧` with a coordinate `b`, a subgroup `V` of finite index of the
pro-`p` kernel `P'` acts trivially on the nearby cycles `Ψ_{M''} A` of the geometric slice, and the
slicing exchange `α : Lσ^* Ψ_M A ⟶ Ψ_{M''} A` is a split monomorphism whose idempotent is
`1 / [P' : V]` times the sum of the actions of representatives of `P' ⧸ V`. It is the composite of
the exchange of the change of trait, invertible by
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`, and of the
inclusion of the `P'`-invariants
`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp`). -/
theorem exists_subgroup_pullbackExchange_baseChangeHom_traitSlice
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) :
    ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _) ∧
      ∃ r, ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A ≫ r =
            𝟙 _ ∧
        Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) •
          (r ≫ ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A) =
        ∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  have key := exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian hM b hb
    (traitSlice (traitSliceCoord k')) (traitSlice_over _) hA hB eB
    (by transport_exact isIso_pullbackExchange_traitSliceGaloisModelHom hM b hb (ℓ := ℓ) hA)
  exact_mod_proofs key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
