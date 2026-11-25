/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDuality
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseFiniteSupport
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseProper
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceImmersion
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseExistence
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseDenseCompactification

/-!

# Nearby duality over a generic base: the induction

This file proves Gabber's theorem for trait models over a generic base
(`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_measure`) by induction on an abstract
measure `μ` of the base `X₁`, which does not increase under dense open immersions (`hμc`) and
drops under generic slicing unless the slice is empty (`hμs`); the dimension is such a measure.

The induction step (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.2; blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"): a trait model `M` of
`X₁` over the generic base is an open sub-model of a proper one `M̄` over a dense compactification
`X̄₁` of `X₁`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel_denseRange`), so that
`μ X̄₁ ≤ μ X₁`. The cone of the duality map of `M̄` has finite support
(`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase`), since by the
slice compatibility (`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`) it
suffices that nearby duality holds for the generic slices of the restrictions of `M̄`, which holds
by induction (the slices have smaller measure) or trivially (empty slices,
`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_isEmpty`). Global sections then give
nearby duality for `M̄`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_nearbyDualityMap_of_isProper_of_finset`), and
passing to the open sub-model gives it for `M`
(`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_openSubmodel`).

For trait models over a base field, the duality map is that of the underlying trait model over
the generic base (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_θ`), which gives
`NearbyCyclesModel.isIso_nearbyDualityMap_of_measure` and the finite-support statement
`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper_of_measure`.

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

section Empty

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The nearby cycles of a model of an empty scheme vanish: its geometric generic fibre is
empty. -/
lemma isZero_boundedConstructibleNearbyCycles_obj_of_isEmpty [IsEmpty X₁.left]
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleNearbyCycles hM).obj A) := by
  have : IsEmpty M.generic := Function.isEmpty M.ε
  refine IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _ ?_
  exact L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
    (R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero (isZero_derivedCategory_of_isEmpty' _ _))

variable [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **Nearby duality over an empty base**: if `X₁` is empty, the duality map `δ_{M,K}` is an
isomorphism, both sides being zero. -/
theorem isIso_nearbyDualityMapOfGenericBase_of_isEmpty [IsEmpty X₁.left]
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (nearbyDualityMapOfGenericBase ℓ D h K) := by
  have hs := isZero_boundedConstructibleNearbyCycles_obj_of_isEmpty ℓ
    (h.preservesBoundedConstructible (ℓ := ℓ)) (verdierDual ℓ K)
  have ht : IsZero (verdierDual ℓ ((boundedConstructibleNearbyCycles
      (h.preservesBoundedConstructible (ℓ := ℓ))).obj K)) :=
    letI := boundedConstructibleBraiding (X := X') (ℓ := ℓ)
    isZero_ihom_obj_of_isZero (isZero_boundedConstructibleNearbyCycles_obj_of_isEmpty ℓ _ K) _
  exact ⟨ht.to_ _, hs.eq_of_src _ _, ht.eq_of_src _ _⟩

end Empty

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Gabber's theorem for trait models over a generic base, by induction on a measure**
(Illusie, *Autour du théorème de monodromie locale*, Thm. 4.2; blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction"). Let `μ` be a measure of
schemes over fields which does not increase along dense open immersions (`hμc`), and which drops by
at least one along generic slices of trait models over the generic base, unless the slice is empty
(`hμs`). Then for every trait model `M` of `X₁` over the generic base and every family `D` of
dualizing maps over generic bases, the duality map `δ_{M,K}` is an isomorphism for every bounded
constructible `K`.

By strong induction on `μ X₁`: compactify `M` densely
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel_denseRange`), prove the
proper case from finite support (generic slices of restrictions of the compactification, by the
slice compatibility `NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`
and the induction hypothesis) and global sections, and restrict back to `M`. -/
theorem isIso_nearbyDualityMapOfGenericBase_of_measure
    (μ : ∀ {F : Type u} [Field F], Over (Spec (.of F)) → ℕ)
    (hμc : ∀ {F : Type u} [Field F] {X₁ Xc : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
      [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType Xc.hom]
      [QuasiCompact Xc.hom] [IsSeparated Xc.hom] (j : X₁ ⟶ Xc), IsOpenImmersion j.left →
      DenseRange j.left → μ Xc ≤ μ X₁)
    (hμs : ∀ {k' : Type u} [Field k'] {F : Type u} [Field F] {X₁ : Over (Spec (.of F))}
      [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
      {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
      {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
      {g : M.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOfGenericBase X₁ ι q g →
      ∀ {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
        (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q),
        μ (genericSliceBase (traitSliceCoord k') hb) + 1 ≤ μ X₁ ∨
          IsEmpty (genericSliceBase (traitSliceCoord k') hb).left)
    {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (D : NearbyDualizingDataOfGenericBase k' ℓ) {F : Type u} [Field F] [Fact (ringChar F).Prime]
    [Fact (ringChar F ≠ ℓ)] {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
    [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (nearbyDualityMapOfGenericBase ℓ D h K) := by
  suffices H : ∀ n : ℕ, ∀ {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
      [Fact (ringChar k' ≠ ℓ)] (D : NearbyDualizingDataOfGenericBase k' ℓ) {F : Type u} [Field F]
      [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] {X₁ : Over (Spec (.of F))}
      [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
      {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
      {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
      {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
      (h : M.IsTraitModelOfGenericBase X₁ ι q g), μ X₁ = n →
        ∀ K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
          IsIso (nearbyDualityMapOfGenericBase ℓ D h K) from
    H _ D h rfl K
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro k' _ _ _ _ D F _ _ _ X₁ _ _ _ ι X' _ _ _ M q g h hn K
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, Mc, qc, gc, hMc, hgen, -, _, j, _, hj, j', _, φ, _, hφ,
    hq, hg⟩ := h.exists_isProper_openSubmodel_denseRange
  have hμ : μ Xc ≤ n := hn ▸ hμc j inferInstance hj
  refine isIso_nearbyDualityMapOfGenericBase_of_openSubmodel ℓ D h hMc j j' φ hφ hq hg K ?_
  refine hMc.isIso_nearbyDualityMap_of_isProper_of_finset ℓ D hgen _ ?_
  refine exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase ℓ D hMc
    (fun V _ ιV _ cV _ hcV b hb L ↦ ?_) _
  have hR := hMc.restrictOpen V
  have hRM := hR.isTraitModelOver
  have := hRM.locallyOfFiniteType_genericSliceBase (traitSliceCoord k') hb
  have := hRM.quasiCompact_genericSliceBase (traitSliceCoord k') hb
  have := hRM.isSeparated_genericSliceBase (traitSliceCoord k') hb
  have := hRM.locallyOfFiniteType_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hRM.quasiCompact_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hRM.isSeparated_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  refine isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase ℓ D
    (Classical.choice (nonempty_nearbyDualizingDataOfGenericBase _ ℓ)) hR hb
    (hMc.exists_iso_map_θ_eq_twist_restrictOpen_of_immersion ℓ V hb D
      (Classical.choice (nonempty_nearbyDualizingDataOfGenericBase _ ℓ)) hgen cV hcV)
    (fun L' ↦ ?_) L
  rcases hμs hR hb with hlt | hempty
  · exact IH _ (by omega) _ _ rfl L'
  · exact isIso_nearbyDualityMapOfGenericBase_of_isEmpty ℓ _ _ L'

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {k' : Type u}
  [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The duality map of a trait model over the base is the duality map of the underlying trait
model over the generic base (`NearbyCyclesModel.IsTraitModelOfBase.isTraitModelOfGenericBase`),
for any family of dualizing maps over generic bases: the dualizing maps agree
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_θ`). -/
lemma nearbyDualityMap_eq_nearbyDualityMapOfGenericBase (D : NearbyDualizingData k k' ℓ)
    (DG : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    nearbyDualityMap ℓ D h K =
      nearbyDualityMapOfGenericBase ℓ DG h.isTraitModelOfGenericBase K := by
  rw [nearbyDualityMap, nearbyDualityMapOfGenericBase, DG.θ_eq_θ k D h]

/-- **Gabber's theorem for trait models over the base, from a measure** (Illusie, *Autour du
théorème de monodromie locale*, Thm. 4.2): for a measure `μ` as in
`NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_measure`, the duality map `δ_{M,K}` of
every trait model over the base is an isomorphism. It is the duality map of the underlying trait
model over the generic base
(`NearbyCyclesModel.nearbyDualityMap_eq_nearbyDualityMapOfGenericBase`), for the family of
dualizing maps of `NearbyCyclesModel.nonempty_nearbyDualizingDataOfGenericBase`. -/
theorem isIso_nearbyDualityMap_of_measure
    (μ : ∀ {F : Type u} [Field F], Over (Spec (.of F)) → ℕ)
    (hμc : ∀ {F : Type u} [Field F] {X₁ Xc : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
      [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType Xc.hom]
      [QuasiCompact Xc.hom] [IsSeparated Xc.hom] (j : X₁ ⟶ Xc), IsOpenImmersion j.left →
      DenseRange j.left → μ Xc ≤ μ X₁)
    (hμs : ∀ {k' : Type u} [Field k'] {F : Type u} [Field F] {X₁ : Over (Spec (.of F))}
      [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
      {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
      {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
      {g : M.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOfGenericBase X₁ ι q g →
      ∀ {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
        (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q),
        μ (genericSliceBase (traitSliceCoord k') hb) + 1 ≤ μ X₁ ∨
          IsEmpty (genericSliceBase (traitSliceCoord k') hb).left)
    (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (nearbyDualityMap ℓ D h K) := by
  let DG := Classical.choice (nonempty_nearbyDualizingDataOfGenericBase k' ℓ)
  rw [nearbyDualityMap_eq_nearbyDualityMapOfGenericBase ℓ D DG h K]
  exact isIso_nearbyDualityMapOfGenericBase_of_measure ℓ μ hμc hμs DG
    h.isTraitModelOfGenericBase K

/-- **Finite support of the cone of the duality map of a proper model, from a measure**: the
statement of `NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper`, for
a measure `μ` as in `NearbyCyclesModel.isIso_nearbyDualityMapOfGenericBase_of_measure`. The duality
map is an isomorphism (`NearbyCyclesModel.isIso_nearbyDualityMap_of_measure`), so `S = ∅`
works. -/
theorem exists_finset_isIso_upperStar_nearbyDualityMap_of_isProper_of_measure
    (μ : ∀ {F : Type u} [Field F], Over (Spec (.of F)) → ℕ)
    (hμc : ∀ {F : Type u} [Field F] {X₁ Xc : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
      [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType Xc.hom]
      [QuasiCompact Xc.hom] [IsSeparated Xc.hom] (j : X₁ ⟶ Xc), IsOpenImmersion j.left →
      DenseRange j.left → μ Xc ≤ μ X₁)
    (hμs : ∀ {k' : Type u} [Field k'] {F : Type u} [Field F] {X₁ : Over (Spec (.of F))}
      [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
      {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
      {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
      {g : M.generic ⟶ Spec (.of (traitGenericField k'))},
      M.IsTraitModelOfGenericBase X₁ ι q g →
      ∀ {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
        (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q),
        μ (genericSliceBase (traitSliceCoord k') hb) + 1 ≤ μ X₁ ∨
          IsEmpty (genericSliceBase (traitSliceCoord k') hb).left)
    (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g)
    [IsProper (toPoint X).left] [IsProper (toPoint X').left] [IsProper q]
    (_hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (opensOverι (finsetComplOpens S hS))).map (nearbyDualityMap ℓ D h K)) := by
  have := isIso_nearbyDualityMap_of_measure ℓ μ hμc hμs D h K
  exact ⟨∅, fun x hx ↦ absurd hx (Finset.notMem_empty x), inferInstance⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
