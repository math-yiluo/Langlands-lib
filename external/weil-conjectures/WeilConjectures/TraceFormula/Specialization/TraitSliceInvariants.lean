/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCompRetraction
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The slice of the change of trait

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and let
`M''` be its geometric slice over the trait `T = Spec K⟦t⟧` along the generic slice
`σ : T ⟶ 𝔸¹_S` (`NearbyCyclesModel.baseChange`), with total space `𝒳'' = 𝒳 ×_{𝔸¹_S} T`. The
projection `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`) factors through the change of trait
`M_T = M ×_S T` of `M`, with total space `𝒳 ×_S T`:
```
M'' --θ--> M_T --ψ--> M
```
where `θ` (`NearbyCyclesModel.geometricSliceTraitChangeHom`) is the base change of the identity of
`M` along `𝔸¹_S ⟶ S`: the slice of `M_T` along the section `T ⟶ 𝔸¹_T` given by the
coordinate `x ∈ K`. This file defines `θ`. It splits the generic-slicing identification (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Facts about traits", identification (2); SGA
4½, [Th. finitude], §§3.4, 3.7) into the two facts about traits used in the blueprint:

* the pullback exchange of `ψ` is invertible: nearby cycles do not change under the change of
  trait `T ⟶ S` (`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`);
* the pullback exchange of `θ` is the inclusion of the invariants of the pro-`p` kernel
  `P' = Gal(Ω_K / Frac K⟦t⟧ · Ω)` of the map of inertia groups, which acts on the nearby cycles of
  `M''` through a finite quotient
  (`NearbyCyclesModel.exists_subgroup_pullbackExchange_sliceTraitChangeHom`, in
  `TraceFormula.Specialization.TraitSliceInvariantsProof`).

Together they give the identification of the slicing exchange of `M` with the inclusion of the
`P'`-invariants (`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`).

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

variable (x : K) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

include hb in
lemma comp_structureMorphism_eq_id_total_comp :
    b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = (Hom.id M).total ≫ q := by
  rw [Hom.id_total, Category.id_comp, hb]

/-- The morphism of models `θ : M'' ⟶ M_T` from the geometric slice `M''` of `M` along the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` to the change of trait `M_T = M ×_S Spec K⟦t⟧`: the base change
of the identity of `M` along `𝔸¹_S ⟶ S`. On total spaces it is the slice
`𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳 ×_S Spec K⟦t⟧` along the section of `𝔸¹_{K⟦t⟧}` given by `x`. -/
noncomputable abbrev geometricSliceTraitChangeHom :=
  (Hom.id M).baseChange hM hM (Category.comp_id q) (Category.comp_id (traitMap k' K)) hb
    (traitSlice_over x) (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
    (comp_structureMorphism_eq_id_total_comp hb) (traitSlice_over x)
    (by rw [Hom.id_generic, Category.id_comp])

lemma geometricSliceTraitChangeHom_total_comp :
    (geometricSliceTraitChangeHom hM x hb).total ≫
        (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)).total =
      (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).total :=
  (Hom.baseChange_total_comp hM hM _ _ _ _ (Hom.id M) _ _ _ _).trans (Category.comp_id _)

lemma geometricSliceTraitChangeHom_generic_comp :
    (geometricSliceTraitChangeHom hM x hb).generic ≫
        (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)).generic =
      (baseChangeHom hM b hb (traitSlice x) (traitSlice_over x)).generic :=
  (Hom.baseChange_generic_comp hM hM _ _ _ _ (Hom.id M) _ _ _ _).trans (Category.comp_id _)

lemma geometricSliceTraitChangeHom_special_comp :
    (Hom.id M).baseChangeSpecial (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
        (comp_structureMorphism_eq_id_total_comp hb) (traitSlice_over x) ≫
        baseChangeSpecialMap hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _) =
      baseChangeSpecialMap hM b hb (traitSlice x) (traitSlice_over x) :=
  (Hom.baseChangeSpecial_comp hM hM _ _ _ _ (Hom.id M) _ _ _).trans (Category.comp_id _)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
