/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityAveraging
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceAveraging
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceClosedHom
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceDualizing

/-!

# Nearby duality over a generic base: the generic slices

Let `M` be a trait model of `X₁` over the generic base
(`NearbyCyclesModel.IsTraitModelOfGenericBase`)
over `S = Spec k'⟦t⟧`, and `b : 𝒳 ⟶ 𝔸¹_S` a coordinate of its total space. The generic slice of
`b` (`NearbyCyclesModel.genericSliceModel`, along `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` with
`K = k'(x)^alg = traitSliceField k'` and `x = traitSliceCoord k'`) is a trait model over the
generic base `(Frac K⟦t⟧, X₂)` (`NearbyCyclesModel.isTraitModelOfGenericBase_genericSliceModel`),
whose special fibre is the special fibre `𝒳''_s` of the slice (`NearbyCyclesModel.sliceSpecial`).

This file proves the **slice compatibility of nearby duality**
(`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`, blueprint
`lemma-nearby-duality-slice--1` (2) with `lemma-duality-invariants-pro-p--1`): if nearby duality
holds for the generic slice model and the twist equation holds, then the pullback of `δ_{M,L}` to
`𝒳''_s` is an isomorphism. This is the
`hslice` hypothesis of the finite-support step
`NearbyCyclesModel.exists_finset_isIso_upperStar_nearbyDualityMapOfGenericBase`.

It also records the instances and finiteness properties needed to state the duality map of the
generic slice model: the characteristic of `K` and `Frac K⟦t⟧` is that of `k'`, and the base `X₂`
and the special fibre `𝒳''_s` are separated, quasi-compact and locally of finite type.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The field of fractions of `K⟦t⟧` has the characteristic of `K`. -/
lemma ringChar_fractionRing_powerSeries (K : Type u) [Field K] :
    ringChar (FractionRing (PowerSeries K)) = ringChar K :=
  (Algebra.ringChar_eq K (FractionRing (PowerSeries K))).symm

instance (K : Type u) [Field K] [Fact (ringChar K).Prime] :
    Fact (ringChar (FractionRing (PowerSeries K))).Prime :=
  ⟨by rw [ringChar_fractionRing_powerSeries]; exact Fact.out⟩

instance (K : Type u) [Field K] (ℓ : ℕ) [Fact (ringChar K ≠ ℓ)] :
    Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ) :=
  ⟨by rw [ringChar_fractionRing_powerSeries]; exact Fact.out⟩

/-- The field `K = k'(x)^alg` of the generic slices has the characteristic of `k'`. -/
lemma ringChar_traitSliceField_eq (k' : Type u) [Field k'] :
    ringChar (traitSliceField k') = ringChar k' :=
  (Algebra.ringChar_eq k' (traitSliceField k')).symm

instance (k' : Type u) [Field k'] [Fact (ringChar k').Prime] :
    Fact (ringChar (traitSliceField k')).Prime :=
  ⟨by rw [ringChar_traitSliceField_eq]; exact Fact.out⟩

instance (k' : Type u) [Field k'] (ℓ : ℕ) [Fact (ringChar k' ≠ ℓ)] :
    Fact (ringChar (traitSliceField k') ≠ ℓ) :=
  ⟨by rw [ringChar_traitSliceField_eq]; exact Fact.out⟩

namespace ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

section Finiteness

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}

/-- The special fibre of the generic slice of a model of finite type over the trait is locally of
finite type over `K`. -/
lemma IsTraitModelOver.locallyOfFiniteType_baseChangeSpecial_traitSlice
    (hM : M.IsTraitModelOver q g) (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom := by
  have :=
    (IsTraitModelOver.baseChange hM b hb (traitSlice x) (traitSlice_over x)).locallyOfFiniteType
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

/-- The special fibre of the generic slice of a model of finite type over the trait is
quasi-compact over `K`. -/
lemma IsTraitModelOver.quasiCompact_baseChangeSpecial_traitSlice
    (hM : M.IsTraitModelOver q g) (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    QuasiCompact (baseChangeSpecial b (traitSlice x)).hom := by
  have := (IsTraitModelOver.baseChange hM b hb (traitSlice x) (traitSlice_over x)).quasiCompact
  exact inferInstanceAs (QuasiCompact (pullback.snd _ _))

/-- The special fibre of the generic slice of a model of finite type over the trait is separated
over `K`. -/
lemma IsTraitModelOver.isSeparated_baseChangeSpecial_traitSlice
    (hM : M.IsTraitModelOver q g) (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    IsSeparated (baseChangeSpecial b (traitSlice x)).hom := by
  have := (IsTraitModelOver.baseChange hM b hb (traitSlice x) (traitSlice_over x)).isSeparated
  exact inferInstanceAs (IsSeparated (pullback.snd _ _))

end Finiteness

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **Nearby duality and generic slices** (blueprint `lemma-nearby-duality-slice--1` (2), with
`lemma-duality-invariants-pro-p--1`): let `M` be a trait model over the generic base, `b : 𝒳 ⟶ 𝔸¹_S`
a coordinate of its total space, and `M''` the generic slice model of `b`
(`NearbyCyclesModel.genericSliceModel`, along `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`, `K = k'(x)^alg`), a trait
model over the generic base `(Frac K⟦t⟧, X₂)`. If the duality maps `δ_{M'',L'}` of the slice
model (with the dualizing maps of a family `D_K` over the trait `Spec K⟦t⟧`) are isomorphisms for
every `L'`, and the dualizing maps satisfy the twist equation
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`), then the pullback of `δ_{M,L}` to
the special fibre `𝒳''_s` of the slice along `𝒳''_s ⟶ X'` is an isomorphism for every `L`.

Proof. By the invariance of nearby cycles under change of trait and the
inertia action on nearby cycles (SGA 4½, [Th. finitude], §3), the pullback of `Ψ_M` to `𝒳''_s` is
the `P`-invariants of `Ψ_{M''}` of the pullback of the coefficients, `P` the pro-`p` kernel of the
map of inertia groups of the strict localisation of `𝔸¹_S` at the generic point of its special
fibre. The pullback of the dualizing complex of `X'` to `𝒳''_s` is the dualizing complex twisted
by `ℚ̄_ℓ(1)[2]` (blueprint `lemma-double-dual-geometric-generic-fibre`), and the dualizing maps `θ`
are compatible with slicing (blueprint `lemma-nearby-duality-slice--1`; this is the hypothesis `H`),
so that the pullback of `δ_{M,L}` is identified with the `P`-invariants of `δ_{M'',L'}(1)[2]`. The
`P`-invariants are a direct summand cut out by an averaging idempotent (`P` is pro-`p` and
`p ≠ ℓ`), and the restriction of an isomorphism to the two averaging summands is an isomorphism
(`CategoryTheory.isIso_comp_comp_map_op_of_averaging`). The formal part is
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_averaging_of_eq`; the geometric inputs are
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_sliceSpecialUpperStar`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_genericSliceUpperStar` and
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`.

The statement does not depend on the choice of `D_K`, the dualizing maps of trait models over
generic bases being determined by their trace and open restriction properties. If the base `X₂`
of the slice is empty, the hypothesis holds trivially, and so does the conclusion: the Milnor
fibres of `𝒳` at the points of `𝒳''_s` lie over the generic point of `𝔸¹_S`, hence in the slice,
so both sides of the pullback of `δ_{M,L}` vanish. -/
theorem isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
    [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
    [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
    [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
    [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
    [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
    (H : h.TwistEquation ℓ hb D DK)
    (hslice : ∀ L' : Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧,
      IsIso (nearbyDualityMapOfGenericBase ℓ DK
        (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb h.isTraitModelOver)
        L'))
    (L : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (L((sliceSpecialMap (traitSliceCoord k') h.isTraitModelOver hb)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧).map (nearbyDualityMapOfGenericBase ℓ D h L).hom) := by
  obtain ⟨θ, hθ, htw, hfix⟩ := h.exists_genericSliceDualizingMap ℓ hb D DK H
  obtain ⟨Γ, _, _, ψ, hψ, hn, hr⟩ :=
    h.exists_averaging_genericSliceExchange ℓ hb ((ihom L).obj (dualizingComplex ℓ X₁)) L
  obtain ⟨r₁, h₁, hρ₁, -⟩ := hr _ (Or.inl rfl)
  obtain ⟨r₂, h₂, hρ₂, hinv₂⟩ := hr _ (Or.inr rfl)
  -- the abstract lemma is instantiated once, with all functors and objects given explicitly
  have key : IsIso ((IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ h
      hb).map (nearbyDualityMapOfGenericBase ℓ D h L)) :=
    Verdier.isIso_map_nearbyDualityMap_of_averaging_of_eq
      (ΨX := boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)))
      (ΨU := IsTraitModelOfGenericBase.genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb)
      (F := IsTraitModelOfGenericBase.genericSliceUpperStar (traitSliceCoord k') ℓ h hb)
      (F' := IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb)
      (ωX := dualizingComplex ℓ X₁) (ωX' := dualizingComplex ℓ X')
      (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ)))
      (boundedConstructibleTensorMap ((isTraitModelOfGenericBase_genericSliceModel
        (traitSliceCoord k') hb h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ)))
      (D.θ h) θ (IsTraitModelOfGenericBase.genericSliceExchange (traitSliceCoord k') ℓ h hb)
      (fun x y ↦ boundedConstructibleTensorMap_natural _ x y)
      (IsTraitModelOfGenericBase.genericSliceExchange_tensor (traitSliceCoord k') ℓ h hb) hθ L
      (fun a ↦ IsTraitModelOfGenericBase.genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a))
      (fun a ↦ IsTraitModelOfGenericBase.genericSliceSelfAction_tensor (traitSliceCoord k') ℓ h hb
        (ψ a))
      (fun a ↦ hfix _ (hψ a).1 (hψ a).2.2) hinv₂ (hn _) r₁ (by exact_mod_proofs h₁)
      (by exact_mod_proofs hρ₁) r₂ h₂ hρ₂
      (h.isIso_closedHomComparison_sliceSpecialUpperStar ℓ hb _)
      (h.isIso_closedHomComparison_genericSliceUpperStar ℓ hb L) (htw _ (hslice _))
  exact (inferInstance : IsIso ((ObjectProperty.ι _).map
    ((IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map
      (nearbyDualityMapOfGenericBase ℓ D h L))))

end NearbyCyclesModel

end ProEtale.CondensedRing

end AlgebraicGeometry
