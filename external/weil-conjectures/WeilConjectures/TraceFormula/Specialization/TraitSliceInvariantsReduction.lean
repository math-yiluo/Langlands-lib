/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariants
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.InvariantRetraction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PadicAlgClNsmulCancel
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The formal part of the identification of the slice nearby cycles with the invariants

`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom` (SGA 4½, [Th. finitude],
§3.7; blueprint `proposition-external-kunneth-formula-nearby-cycles`, identification (2)) asks, for
the pullback exchange `α_θ` of the morphism of models `θ : M'' ⟶ M_T` from the geometric slice to
the change of trait, for a subgroup `V` of finite index of the pro-`p` kernel `P'` acting trivially
on `Ψ_{M''} C`, and for a retraction of `α_θ` whose idempotent is the average over `P' ⧸ V`.

This file proves its formal part, for a general strictly henselian slice `Spec K⟦t⟧`:
* the exchange `α_θ` lands in the `P'`-invariants
  (`NearbyCyclesModel.pullbackExchange_geometricSliceTraitChangeHom_comp_autAction`): `θ` is
  equivariant for the actions of `P'` on `M''` and on `M_T`
  (`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`), and `P'` acts trivially on
  `Ψ_{M_T}` by the invariance of nearby cycles under change of trait
  (`NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`);
* granted the finiteness of the action and that the average lands in the image of `α_θ`, the
  averaging gives the retraction
  (`NearbyCyclesModel.exists_retraction_pullbackExchange_geometricSliceTraitChangeHom_of_image`,
  from `CategoryTheory.exists_retraction_card_smul_eq_sum`);
* hence the conclusion of `NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom`
  follows from the finiteness of the action of `P'` on `Ψ_{M''} C` and a retraction `s` of
  `α_θ` with `s ≫ α_θ` fixing the average
  (`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_image`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (x : K) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

variable [IsSepClosed k'] [IsSepClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The exchange of the slice of the change of trait lands in the invariants**: for `σ` in the
kernel `P'` of the map of inertia groups, `α_θ(C) ≫ σ = α_θ(C)`. -/
theorem pullbackExchange_geometricSliceTraitChangeHom_comp_autAction
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (σ : GenericAut k' K) :
    ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C ≫
      (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).autAction
        (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) =
      ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C := by
  have hψ := isIso_pullbackExchange_baseChangeHom_traitMap_of_generic (ℓ := ℓ)
    (K := K) hM (A := C) hC
  have hτ : (baseChangeAut hM q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
      (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _ := by
    exact @Hom.autAction_eq_id_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)
      (baseChangeAut_generic_comp hM _ _ _ _ _) C (by exact_mod_proofs hψ)
  have hτ' : (baseChangeAut hM q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _) σ).autAction (Profinite.padicAlgClRingObj ℓ) C = 𝟙 _ :=
    eq_id_of_naturality_of_iso _ (fun g ↦ Hom.autAction_naturality _ _ g)
      ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X).app C).symm hτ
  have key := Hom.pullbackExchange_app_comp_autAction_of_comm (Profinite.padicAlgClRingObj ℓ)
    (geometricSliceTraitChangeHom hM x hb)
    (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ)
    (baseChangeAut hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _) σ)
    (by simp)
    (baseChangeAut_generic_comp_baseChange hM hM _ _ _ _ (Hom.id M) _ _ _ _ σ) C
  rw [hτ'] at key
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at key
  exact_mod_proofs key

/-- **Averaging over the finite quotient gives the retraction onto the invariants**: if `s` is a
retraction of the exchange `α_θ` such that `s ≫ α_θ` fixes the sum of the actions of
representatives of `P' ⧸ V`, there is a retraction `r` of `α_θ` with `[P' : V] • (r ≫ α_θ)` the
sum of the actions. -/
theorem exists_retraction_pullbackExchange_geometricSliceTraitChangeHom_of_image
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (V : Subgroup (GenericAut k' K)) [Fintype (GenericAut k' K ⧸ V)]
    (s : _ ⟶ _)
    (hs : ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)).app C ≫ s = 𝟙 _)
    (himg : (∑ σ : GenericAut k' K ⧸ V,
          (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ.out).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) ≫
        s ≫ ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C =
      ∑ σ : GenericAut k' K ⧸ V,
          (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ.out).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    ∃ r, ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ r = 𝟙 _ ∧
        Fintype.card (GenericAut k' K ⧸ V) •
          (r ≫ ((geometricSliceTraitChangeHom hM x hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C) =
        ∑ σ : GenericAut k' K ⧸ V,
          (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ.out).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  let _ := modLinear _ (Profinite.PadicAlgCl.constRingHom.{u} ℓ)
    (baseChangeSpecial b (traitSlice x)).left
  exact exists_retraction_card_smul_eq_sum (PadicAlgCl ℓ) _ s hs Finset.univ Finset.univ_nonempty
    _ (fun σ _ ↦ pullbackExchange_geometricSliceTraitChangeHom_comp_autAction hM x hb hC σ.out)
    himg

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

variable [IsSepClosed k'] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

-- elaborating the actions of `P' ⧸ V` on the concrete slice trait `Spec k'⟦u⟧⟦t⟧` is slow
/-- **The invariants from the finiteness of the action and the image of the average**: the
conclusion of `NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom` follows
from a subgroup `V` of finite index of `P'` acting trivially on `Ψ_{M''} C` together with a
retraction `s` of `α_θ` such that `s ≫ α_θ` fixes the sum of the actions of representatives of
`P' ⧸ V`. -/
theorem exists_subgroup_pullbackExchange_sliceTraitChangeHom_of_image
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))
    (h : ∃ (V : Subgroup (GenericAut k' (traitSliceField k')))
      (_ : Fintype (GenericAut k' (traitSliceField k') ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) = 𝟙 _) ∧
      ∃ s, ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
          (Profinite.padicAlgClRingObj ℓ)).app C ≫ s = 𝟙 _ ∧
        (∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) ≫
          s ≫ ((geometricSliceTraitChangeHom hM (traitSliceCoord k') hb).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app C =
        ∑ σ : GenericAut k' (traitSliceField k') ⧸ V,
          (baseChangeAut hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)
            σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
              (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
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
  obtain ⟨V, hV₀, hV, s, hs, himg⟩ := h
  exact ⟨V, hV₀, hV,
    exists_retraction_pullbackExchange_geometricSliceTraitChangeHom_of_image hM _ hb hC V s hs himg⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
