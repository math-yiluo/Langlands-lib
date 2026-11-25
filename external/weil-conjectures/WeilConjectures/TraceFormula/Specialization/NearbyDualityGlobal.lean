/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange

/-!

# Nearby duality and global sections: the concrete inputs

For a trait model `M` over the base with proper `X`, `X'` and proper total space, the global
sections `RΓ(X', δ_{M,K})` of the duality map are compared with the duality map of the trait by
the abstract identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` (blueprint
`lemma-nearby-duality-proper-direct-image` (1), (3)), applied to `G = Ra_*`, `G' = Ra'_*` and the
proper exchange `χ_a`. Its concrete inputs, proved in
`TraceFormula.Specialization.NearbyDualityLaxMonoidal` and
`TraceFormula.Specialization.NearbyDualityExchange`, are:

* the lax monoidal structure of `Rf_*` on bounded constructible complexes, the right adjoint of
  the monoidal functor `Lf^*` (`ProEtale.CondensedRing.boundedConstructibleLowerStarLaxMonoidal`);
* the compatibility of the pushforward exchange `χ_f` with the lax tensor maps
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`), from the monoidality
  of the pullback exchange through the abstract computation
  `ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux` of the Künneth map, specialised
  to the diagonal;
* **global Verdier duality**: for a proper `k`-scheme `Z`, the duality map of `(Ra_*, μ, tr_Z)`
  is the Verdier exchange morphism `Ra_* RHom(K, ω_Z) ≅ RHom(Ra_! K, ℚ̄_ℓ)` read through
  `Ra_! ≅ Ra_*` (`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), hence is an
  isomorphism (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`). The
  identification uses that the exceptional projection morphism of a proper morphism is the
  projection morphism of `Lf^* ⊣ Rf_!`
  (`ProEtale.CondensedRing.upperStar_map_exceptionalProjection_comp_counit`, blueprint
  `prop-sf-pf-coherence`).

With these, `RΓ(X', δ_{M,K})` is an isomorphism as soon as the proper exchange `χ_a` is invertible
and the duality map of the trait is invertible at `Ra_* K`
(`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### The lax monoidal structure of nearby cycles -/

namespace NearbyCyclesModel

section LaxMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- The lax monoidal structure of the nearby cycles `Ψ = Li^* ∘ Rj_* ∘ Lε^*`: the composite of the
monoidal functors `Lε^*`, `Li^*` and of the lax monoidal right adjoint `Rj_*`
(`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`). Its tensor maps are the lax tensor maps
`NearbyCyclesModel.tensorMap` (`NearbyCyclesModel.nearbyCyclesLaxMonoidal_μ`). It is not an
instance. -/
@[instance_reducible]
noncomputable def nearbyCyclesLaxMonoidal : (M.nearbyCycles Λ).LaxMonoidal :=
  @Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _ L((M.ε)^*⟦Λ⟧) (R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)) _
    (@Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _ R((M.j)_*⟦Λ⟧) L((M.i)^*⟦Λ⟧)
      (derivedUpperStarLowerStarAdjunction Λ M.j).rightAdjointLaxMonoidal _)

/-- The tensor maps of `NearbyCyclesModel.nearbyCyclesLaxMonoidal` are the lax tensor maps of
nearby cycles. -/
lemma nearbyCyclesLaxMonoidal_μ
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (M.nearbyCycles Λ) (M.nearbyCyclesLaxMonoidal Λ) A B =
      M.tensorMap Λ A B := by
  change (Functor.LaxMonoidal.μ L((M.i)^*⟦Λ⟧) _ _ ≫
    L((M.i)^*⟦Λ⟧).map (lowerStarTensorMap' Λ M.j _ _)) ≫
      L((M.i)^*⟦Λ⟧).map (R((M.j)_*⟦Λ⟧).map (Functor.LaxMonoidal.μ L((M.ε)^*⟦Λ⟧) A B)) = _
  rw [Category.assoc, ← Functor.map_comp]
  rfl

end LaxMonoidal

section Trait

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k : Type u) [Field k] (k' : Type u) [Field k'] [IsSepClosed k'] [Algebra k k']

/-- The unit map of the lax monoidal structure of the nearby cycles of the trait is invertible:
after restriction to the closed point, the unit `Λ_S ⟶ Rη̄_* Lη̄^* Λ_S` is invertible
(`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit`). -/
lemma isIso_nearbyCyclesLaxMonoidal_ε_traitModel :
    IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _ ((traitModel k k').nearbyCycles Λ)
      ((traitModel k k').nearbyCyclesLaxMonoidal Λ)) := by
  have h : IsIso (L(((traitModel k k').i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (traitModel k k').j).unit.app (𝟙_ _))) :=
    isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit Λ k'
  exact Adjunction.isIso_ε_comp_rightAdjointLaxMonoidal L(((traitModel k k').ε)^*⟦Λ⟧)
    L(((traitModel k k').i)^*⟦Λ⟧) (derivedUpperStarLowerStarAdjunction Λ (traitModel k k').j)

/-- The tensor maps of the nearby cycles of the trait are invertible at `(A, B)` if `Lε^* A` is a
finite direct sum of shifts of the unit
(`ProEtale.CondensedRing.isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition`). -/
lemma isIso_tensorMap_traitModel
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
      (condensedRingObj Λ (point k).left)))
    (hA : Nonempty (ShiftDecomposition (𝟙_ _) (L(((traitModel k k').ε)^*⟦Λ⟧).obj A))) :
    IsIso ((traitModel k k').tensorMap Λ A B) := by
  have h := isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition Λ k'
    (V := L(((traitModel k k').ε)^*⟦Λ⟧).obj B) hA.some
  unfold tensorMap
  rw [Functor.map_comp]
  change IsIso (_ ≫ L(((traitGenericModel k').i)^*⟦Λ⟧).map
    (lowerStarTensorMap' Λ (traitGenericModel k').j _ _) ≫ _)
  infer_instance

end Trait

section BoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

/-- The nearby cycles on bounded constructible complexes are strong monoidal, with tensor maps the
lax tensor maps of nearby cycles, as soon as these and the unit map of
`NearbyCyclesModel.nearbyCyclesLaxMonoidal` are invertible: the restriction
(`CategoryTheory.ObjectProperty.laxMonoidalLift`) of `NearbyCyclesModel.nearbyCyclesLaxMonoidal`.
-/
@[instance_reducible]
noncomputable def boundedConstructibleNearbyCyclesMonoidal
    (hP : M.PreservesBoundedConstructible 𝐐)
    (hμ : ∀ A B : Dᵇc(X.left)⟦𝐐⟧, IsIso (M.tensorMap 𝐐 A.obj B.obj))
    (hε : IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (M.nearbyCycles 𝐐)
      (M.nearbyCyclesLaxMonoidal 𝐐))) :
    (boundedConstructibleNearbyCycles hP).Monoidal :=
  letI : (boundedConstructibleNearbyCycles hP).LaxMonoidal :=
    @ObjectProperty.laxMonoidalLift _ _ _ _ _ _ (boundedConstructible _) _
      (boundedConstructible _) _ (M.nearbyCycles 𝐐) (M.nearbyCyclesLaxMonoidal 𝐐) _
  haveI : IsIso (Functor.LaxMonoidal.ε (boundedConstructibleNearbyCycles hP)) :=
    (ObjectProperty.isIso_hom_iff _).1 hε
  haveI (A B : Dᵇc(X.left)⟦𝐐⟧) :
      IsIso (Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hP) A B) :=
    (ObjectProperty.isIso_hom_iff _).1 (by
      change IsIso (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (M.nearbyCycles 𝐐)
        (M.nearbyCyclesLaxMonoidal 𝐐) A.obj B.obj)
      rw [nearbyCyclesLaxMonoidal_μ]
      exact hμ A B)
  (Functor.CoreMonoidal.ofLaxMonoidal _).toMonoidal

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [IsSeparated X.hom]
  [IsSeparated X'.hom] in
/-- The tensor maps of `NearbyCyclesModel.boundedConstructibleNearbyCyclesMonoidal` are the lax
tensor maps of nearby cycles. -/
lemma boundedConstructibleNearbyCyclesMonoidal_μ (hP : M.PreservesBoundedConstructible 𝐐)
    (hμ : ∀ A B : Dᵇc(X.left)⟦𝐐⟧, IsIso (M.tensorMap 𝐐 A.obj B.obj))
    (hε : IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (M.nearbyCycles 𝐐)
      (M.nearbyCyclesLaxMonoidal 𝐐))) (A B : Dᵇc(X.left)⟦𝐐⟧) :
    (letI := boundedConstructibleNearbyCyclesMonoidal hP hμ hε;
      Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hP) A B) =
      boundedConstructibleTensorMap hP A B :=
  ObjectProperty.hom_ext _ (nearbyCyclesLaxMonoidal_μ 𝐐 M A.obj B.obj)

end BoundedConstructible

end NearbyCyclesModel

/-! ### Global sections of the duality map -/

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- **The nearby cycles of the trait are monoidal on the base point**: the nearby cycles
`Ψ_S : Dᵇc(Spec k) ⥤ Dᵇc(Spec k')` of the trait `S` as a model of `Spec k` are a monoidal functor
with tensor maps the lax tensor maps of nearby cycles (`boundedConstructibleTensorMap`):
`NearbyCyclesModel.boundedConstructibleNearbyCyclesMonoidal`. The tensor maps are invertible as
`Lε^* A` is a finite direct sum of shifts of the unit on the geometric generic point `Spec Ω`
(`nonempty_shiftDecomposition_of_boundedConstructible`,
`NearbyCyclesModel.isIso_tensorMap_traitModel`), and the unit map is invertible
(`NearbyCyclesModel.isIso_nearbyCyclesLaxMonoidal_ε_traitModel`). -/
theorem exists_monoidal_traitSpecialization :
    ∃ L : (boundedConstructibleNearbyCycles
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)).Monoidal,
      ∀ A B, (letI := L; Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) A B) =
        boundedConstructibleTensorMap (preservesBoundedConstructible_traitModel ℓ) A B := by
  have hμ (A B : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      IsIso ((traitModel k k').tensorMap (Profinite.padicAlgClRingObj ℓ) A.obj B.obj) :=
    isIso_tensorMap_traitModel _ k k' A.obj B.obj
      (nonempty_shiftDecomposition_of_boundedConstructible ℓ (K := traitGenericField k') _
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ A.property))
  exact ⟨boundedConstructibleNearbyCyclesMonoidal _ hμ
      (isIso_nearbyCyclesLaxMonoidal_ε_traitModel _ k k'),
    boundedConstructibleNearbyCyclesMonoidal_μ _ hμ _⟩

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- **The duality map of the trait itself** (blueprint `lemma-nearby-duality-proper-direct-image`
(3), "with `θ_S` the identity of `A` the normalized pairing on `S` is ordinary evaluation"): for the
trait `S` as a model of the base point `Spec k`, with the lax tensor map of its nearby cycles and
the inverse of the specialization unit as dualizing map, the duality map
`δ_{S,N} : Ψ_S RHom(N, ℚ̄_ℓ) ⟶ RHom(Ψ_S N, ℚ̄_ℓ)` is an isomorphism for every bounded
constructible `N` on `Spec k`: `Ψ_S` is monoidal (`exists_monoidal_traitSpecialization`), `N` is
dualizable (`ProEtale.CondensedRing.nonempty_hasLeftDual_point`), monoidal functors commute with
duals (`CategoryTheory.Verdier.isIso_nearbyDualityMap_of_monoidal`), and the dualizing map
`σ_s⁻¹` differs from the inverse of the unit map of `Ψ_S` by an automorphism of the unit. -/
theorem isIso_nearbyDualityMap_traitModel
    (N : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
      (inv (traitSpecializationUnit k k' (ℓ := ℓ))) N) := by
  obtain ⟨L, hμ⟩ := exists_monoidal_traitSpecialization ℓ (k := k) (k' := k')
  obtain ⟨hN⟩ := nonempty_hasLeftDual_point ℓ (k := k) N
  let := L
  have h := Verdier.isIso_nearbyDualityMap_of_monoidal (boundedConstructibleNearbyCycles
    (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) (ᘁN) N
  have e₁ : (fun A B ↦ Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
      (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) A B) =
      boundedConstructibleTensorMap (preservesBoundedConstructible_traitModel ℓ) :=
    funext₂ hμ
  rw [e₁] at h
  have e₂ : inv (traitSpecializationUnit k k' (ℓ := ℓ)) =
      Functor.OplaxMonoidal.η (boundedConstructibleNearbyCycles
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) ≫
        (Functor.LaxMonoidal.ε (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ)) ≫
          inv (traitSpecializationUnit k k' (ℓ := ℓ))) := by
    rw [Functor.Monoidal.η_ε_assoc]
  rw [e₂, ← Verdier.nearbyDualityMap_comp_ihom_map]
  infer_instance

/-- **Global sections of the duality map of a proper model, reduced to the trait** (blueprint
`lemma-nearby-duality-proper-direct-image` (1) and (3)): if `X`, `X'` and the total space of the
trait model `M` over the base are proper, then `RΓ(X', δ_{M,K})` is an isomorphism as soon as the
proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism is invertible (it is used at
`K` and `D_X K`), and the duality map of the trait `S` itself (lax tensor map of its nearby cycles,
dualizing map the inverse of the specialization unit `σ_s`) is invertible at `Ra_* K`. This is
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper'`, with the compatibility of `χ_a`
with the lax tensor maps (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`),
the proper axiom of the dualizing maps
(`NearbyCyclesModel.NearbyDualizingData.pushforwardExchange_comp_map_θ_comp_trace`) and global
Verdier duality on both fibres (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`).

The invertibility of `χ_a` needs the geometric generic fibre of `M` to be all of `X ×_k Spec Ω`
(not only an open of it, as `NearbyCyclesModel.IsTraitModelOfBase` allows): for
`X = Spec k ⊔ Spec k` and the trait `S` itself as total space, mapping to the first copy, `χ_a`
kills `Ψ_S Ra_*` of the unit of the second copy.
-/
theorem isIso_lowerStar_nearbyDualityMap_of_isIso (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g) [IsProper (toPoint X).left] [IsProper (toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hχ : ∀ A, IsIso ((h.pushforwardExchange ℓ).app A))
    [IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModel (k := k) (k' := k') ℓ))
      (inv (traitSpecializationUnit k k' (ℓ := ℓ)))
      ((boundedConstructibleLowerStar ℓ (toPoint X)).obj K))] :
    IsIso ((boundedConstructibleLowerStar ℓ
      (toPoint X')).map (nearbyDualityMap ℓ D h K)) := by
  have hθ := (D.pushforwardExchange_comp_map_θ_comp_trace h hgen).symm
  have t₁ : h.pushforwardExchange ℓ = h.toTrait.boundedConstructiblePushforwardExchange ℓ
      (h.preservesBoundedConstructible ℓ) (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [t₁] at hθ hχ
  -- the categories of the abstract statement are those of the compatibility with the tensor maps
  exact Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans
    (fun A B ↦ Hom.boundedConstructiblePushforwardExchange_tensor (f := toPoint X)
      (f' := toPoint X') h.toTrait (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ) A B) hθ
    (fun A _ _ y ↦ letI := boundedConstructibleLowerStarLaxMonoidal ℓ (toPoint X')
      Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ boundedConstructibleTensorMap_natural _ x y) K (hχ K) (hχ _)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X K)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X' _) inferInstance

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
