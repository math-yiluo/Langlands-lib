/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSliceFinite
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessGlobalFinite
public import WeilConjectures.TraceFormula.Specialization.ProjectiveSpaceModel

/-!

# Deligne's finiteness theorem for nearby cycles with finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic exponent `p`, and `T` a finite
discrete ring in which `p` is invertible (its exponent is then invertible in `k'`). Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) for the affine spaces: the geometric nearby
cycles of the standard model of `𝔸ⁿ_S` carry bounded constructible complexes of `T̲`-modules to
bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`).

The proof is Deligne's induction on `n`, for all separably closed fields `k'` at once:
* for `n = 0`, `𝔸⁰_S = S` is proper over `S` and its special fibre has no non-closed point, so
  the global step (`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_finite`)
  applies with no slices;
* for `n + 1`, extend `B` by zero along the chart `𝔸ⁿ⁺¹_S ⊆ ℙⁿ⁺¹_S` to `B̃`. The pullbacks of
  `Ψ_ℙ B̃` along the charts `eₐ,ₛ` are the nearby cycles `Ψ_𝔸 (eₐ^* B̃)` (open exchange), whose
  pullbacks to the coordinate generic slices `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` are retracts of the nearby
  cycles over `Spec K⟦t⟧` of complexes on `𝔸ⁿ_{K⟦t⟧}`
  (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`), bounded
  constructible by induction. The maps `eₐ,ₛ ∘ hᵢ,ₛ` reach every non-closed point of `ℙⁿ⁺¹_{k'}`
  (`NearbyCyclesModel.exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq`), so the
  global step shows that `Ψ_ℙ B̃` is bounded constructible, and so is its restriction
  `Ψ_𝔸 B` to the chart.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The slice step with finite coefficients, as a finiteness statement**: if the nearby cycles
over `Spec K⟦t⟧` (`K = k'(x)^alg`) of `𝔸ⁿ_{K⟦t⟧}` preserve bounded constructible complexes, then the
restrictions `Lhᵢ,ₛ^* Ψ C` of the nearby cycles of bounded constructible complexes `C` on `𝔸ⁿ⁺¹_S`
to the coordinate generic slices are bounded constructible: they are retracts of the nearby cycles
of `Lhᵢ^* C`
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`). -/
theorem boundedConstructible_upperStar_nearbyCycles_affineSpaceSlice_of_finite
    {k' : Type u} [Field k'] [IsSepClosed k'] (n : ℕ) (i : Fin (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (ih : ∀ {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (affineSpaceModel (traitSliceField k') n).total) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T)
          (affineSpaceModel (traitSliceField k') n).total))},
      boundedConstructible _ C →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
          trait (traitSliceField k'))).left)
        (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C))
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' (n + 1)).total))}
    (hC : boundedConstructible _ C) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k'))).left)
      ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.continuousMapRingObj T⟧)).obj
        (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C)) := by
  have hs := isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite T n i hp hpT
    ((boundedConstructible_iff_of_finite T C).1 hC).plusEtaleOrigin
  exact boundedConstructible_of_retract_of_finite T
    ⟨_, retraction (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.continuousMapRingObj T)).app C), IsSplitMono.id _⟩
    (ih (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ C hC))

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- **Nearby cycles commute with the affine charts of `ℙⁿ_S`**: the pullback exchange
`Leₐ,ₛ^* Ψ_ℙ ⟶ Ψ_𝔸 Leₐ^*` of an affine chart is an isomorphism, the chart being an open immersion
with cartesian square of geometric generic fibres. -/
instance isIso_pullbackExchange_projectiveSpaceChartHom {k' : Type u} [Field k'] (n : ℕ)
    (a : Option (ULift.{u} (Fin n))) :
    IsIso ((projectiveSpaceChartHom k' n a).pullbackExchange
      (Profinite.continuousMapRingObj T)) :=
  have : IsOpenImmersion (projectiveSpaceChartHom k' n a).total :=
    inferInstanceAs (IsOpenImmersion (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a))
  Hom.isIso_pullbackExchange_of_isOpenImmersion _ _
    (isPullback_traitStdHom_generic (M := affineSpaceModel k' n) _
      (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')
        (traitGenericPoint k'))
      (IsPullback.of_hasPullback (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')
        (traitClosedPoint k')) _ _)

/-- **The slices of the charts of `ℙⁿ⁺¹_S`, finite coefficients**: if the nearby cycles over
`Spec K⟦t⟧` of `𝔸ⁿ_{K⟦t⟧}` preserve bounded constructible complexes, then for every bounded
constructible complex `B` on `ℙⁿ⁺¹_S`, every chart `a` and every coordinate `i`, the pullback of
`Ψ_ℙ B` along `eₐ,ₛ ∘ hᵢ,ₛ : 𝔸ⁿ_K ⟶ ℙⁿ⁺¹_{k'}` is bounded constructible. -/
theorem boundedConstructible_upperStar_nearbyCycles_projectiveSpace_of_finite
    {k' : Type u} [Field k'] [IsSepClosed k'] (n : ℕ) (a : Option (ULift.{u} (Fin (n + 1))))
    (i : Fin (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (ih : ∀ {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (affineSpaceModel (traitSliceField k') n).total) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T)
          (affineSpaceModel (traitSliceField k') n).total))},
      boundedConstructible _ C →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
          trait (traitSliceField k'))).left)
        (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C))
    {B : DerivedCategory (Mod (Sheaf
      (Scheme.ProEt.topology (projectiveSpaceModel k' (n + 1)).total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T)
        (projectiveSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k'))).left)
      ((L((affineSpaceSliceSpecialFibre k' n i ≫ projectiveSpaceChartSpecial k' (n + 1) a)^*⟦
        Profinite.continuousMapRingObj T⟧)).obj
        (((projectiveSpaceModel k' (n + 1)).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj B)) := by
  have h := boundedConstructible_upperStar_nearbyCycles_affineSpaceSlice_of_finite T n i hp hpT ih
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
      (AffineSpace.toRelativeProjectiveSpaceChart (trait k') a) B hB)
  exact (boundedConstructible _).prop_of_iso
    ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.continuousMapRingObj T⟧)).mapIso
      (asIso (((projectiveSpaceChartHom k' (n + 1) a).pullbackExchange
        (Profinite.continuousMapRingObj T)).app B)).symm ≪≫
      ((leftDerivedUpperStarComp (Profinite.continuousMapRingObj T) _ _).app _).symm) h

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- The relative projective space `ℙⁿ_S` is proper over the trait. -/
instance isProper_projectiveSpaceStructure (k' : Type u) [Field k'] (n : ℕ) :
    IsProper (projectiveSpaceStructure k' n) :=
  ProjectiveSpace.instIsProper _ _

omit [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- The total space of the standard model of `ℙⁿ_S` is Noetherian. -/
instance isNoetherian_projectiveSpaceModel_total (k' : Type u) [Field k'] (n : ℕ) :
    IsNoetherian (projectiveSpaceModel k' n).total :=
  have : IsProper (projectiveSpaceStructure k' n) := isProper_projectiveSpaceStructure k' n
  (isTraitModel_traitStdModel (projectiveSpaceStructure k' n)).isNoetherian_total

/-- **Deligne's finiteness theorem on `ℙⁿ⁺¹_S`, given the case of `𝔸ⁿ` over `Spec K⟦t⟧`**: if the
nearby cycles over `Spec K⟦t⟧` (`K = k'(x)^alg`) of `𝔸ⁿ_{K⟦t⟧}` preserve bounded constructible
complexes, then so do the nearby cycles of `ℙⁿ⁺¹_S`: the pullbacks of `Ψ_ℙ B` along the maps
`eₐ,ₛ ∘ hᵢ,ₛ`, which reach every non-closed point of the special fibre, are bounded constructible
(`NearbyCyclesModel.boundedConstructible_upperStar_nearbyCycles_projectiveSpace_of_finite`), and
the global step applies
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_finite`). -/
theorem boundedConstructible_nearbyCycles_projectiveSpace_of_finite {k' : Type u} [Field k']
    [IsSepClosed k'] [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))] (n : ℕ)
    {p : ℕ} [Fact p.Prime] (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (ih : ∀ {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (affineSpaceModel (traitSliceField k') n).total) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T)
          (affineSpaceModel (traitSliceField k') n).total))},
      boundedConstructible _ C →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
          trait (traitSliceField k'))).left)
        (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C))
    {B : DerivedCategory (Mod (Sheaf
      (Scheme.ProEt.topology (projectiveSpaceModel k' (n + 1)).total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T)
        (projectiveSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (projectiveSpaceStructure k' (n + 1))).left)
      (((projectiveSpaceModel k' (n + 1)).geometric.nearbyCycles
        (Profinite.continuousMapRingObj T)).obj B) := by
  have : IsNoetherian (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n);
      trait (traitSliceField k')) ↘ trait (traitSliceField k'))).left :=
    isNoetherian_of_isTraitModel (isTraitModel_affineSpaceModel n)
  let W : Option (ULift.{u} (Fin (n + 1))) × Fin (n + 1) → Scheme.{u} := fun _ ↦
    (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
      trait (traitSliceField k'))).left
  let h : ∀ ai, W ai ⟶ (traitStdSpecialFibre (projectiveSpaceStructure k' (n + 1))).left :=
    fun ai ↦ affineSpaceSliceSpecialFibre k' n ai.2 ≫ projectiveSpaceChartSpecial k' (n + 1) ai.1
  have : ∀ ai, IsNoetherian (W ai) := fun _ ↦ ‹_›
  refine boundedConstructible_nearbyCycles_traitStdModel_of_finite T
    (projectiveSpaceStructure k' (n + 1)) h (fun x hx ↦ ?_) hB
    (fun ai ↦ boundedConstructible_upperStar_nearbyCycles_projectiveSpace_of_finite T n ai.1 ai.2
      hp hpT ih hB)
  obtain ⟨a, i, w, hw⟩ :=
    exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq k' n x hx
  exact ⟨(a, i), w, by simp only [h, Scheme.Hom.comp_apply]; exact hw⟩

omit [DiscreteTopology T] [Finite T] in
/-- **Restriction to the affine chart**: if the nearby cycles of the extension by zero
`j_! B` of a complex `B` on `𝔸ⁿ_S` along the affine chart `j : 𝔸ⁿ_S ⟶ ℙⁿ_S` are bounded
constructible, then so are the nearby cycles of `B`: they are the pullback of `Ψ_ℙ (j_! B)` along
the chart of the special fibres (open exchange), as `Lj^* j_! B ≅ B`. -/
theorem boundedConstructible_nearbyCycles_affineSpace_of_projectiveSpace_of_finite
    {k' : Type u} [Field k'] (n : ℕ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' n).total))}
    (hB : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (projectiveSpaceStructure k' n)).left)
      (((projectiveSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj
        ((D((AffineSpace.toRelativeProjectiveSpaceChart (trait k')
          (none : Option (ULift.{u} (Fin n))))_!open⟦Profinite.continuousMapRingObj T⟧)).obj B))) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj
        B) :=
  (boundedConstructible _).prop_of_iso
    (asIso (((projectiveSpaceChartHom k' n none).pullbackExchange
      (Profinite.continuousMapRingObj T)).app _) ≪≫
      ((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).mapIso
        (asIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
          (Profinite.continuousMapRingObj T)
            (AffineSpace.toRelativeProjectiveSpaceChart (trait k')
              (none : Option (ULift.{u} (Fin n))))).unit.app B)).symm)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB)

/-- **Deligne's finiteness theorem on `𝔸⁰_S`, finite coefficients**: `𝔸⁰_S ⟶ S` is an
isomorphism, so its special fibre is a point and the global step applies with no slices. -/
theorem boundedConstructible_nearbyCycles_affineSpaceModel_zero_of_finite {k' : Type u}
    [Field k'] [IsSepClosed k'] [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' 0).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' 0).total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' 0).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj
        B) := by
  have : IsIso (traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k')).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝔸(ULift.{u} (Fin 0); trait k') ↘ trait k')
      (traitClosedPoint k')))
  have hsub : Subsingleton (traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘
      trait k')).left :=
    ⟨fun y z ↦ ((traitStdSpecialFibre (𝔸(ULift.{u} (Fin 0); trait k') ↘
      trait k')).hom.homeomorph.injective (Subsingleton.elim _ _))⟩
  refine boundedConstructible_nearbyCycles_traitStdModel_of_finite T _ (ι := PEmpty.{1})
    (W := fun _ ↦ Spec (.of k')) (fun i ↦ i.elim) (fun x hx ↦ (hx ?_).elim) hB
    (fun i ↦ i.elim)
  rw [mem_closedPoints_iff, show ({x} : Set _) = Set.univ from
    Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x]
  exact isClosed_univ

/-- **Deligne's finiteness theorem for nearby cycles on `𝔸ⁿ_S`, finite coefficients** (SGA 4½,
[Th. finitude], Thm. 3.2): over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably
closed of characteristic exponent `p`), for a finite discrete ring `T` in which `p` is invertible
and whose exponent is invertible in `k'`, the geometric nearby cycles of the standard model of
`𝔸ⁿ_S` carry bounded constructible complexes of `T̲`-modules to bounded constructible complexes.
See the module docstring for Deligne's induction. -/
theorem boundedConstructible_nearbyCycles_affineSpace_obj_of_finite (n : ℕ) :
    ∀ {k' : Type u} [Field k'] [IsSepClosed k']
      [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))] {p : ℕ} [Fact p.Prime],
      (∀ m : ℕ, (m : k') = 0 → p ∣ m) → IsUnit (p : T) →
      ∀ {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' n).total)
        Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
          (affineSpaceModel k' n).total))},
      boundedConstructible _ B →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait k') ↘ trait k')).left)
        (((affineSpaceModel k' n).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj
          B) := by
  induction n with
  | zero =>
    intro k' _ _ _ p _ _ _ B hB
    exact boundedConstructible_nearbyCycles_affineSpaceModel_zero_of_finite T hB
  | succ n ih =>
    intro k' _ _ _ p _ hp hpT B hB
    have hpK (m : ℕ) (hm : (m : traitSliceField k') = 0) : p ∣ m :=
      hp m ((algebraMap k' (traitSliceField k')).injective (by rw [map_natCast, hm, map_zero]))
    have : HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of (traitSliceField k'))) :=
      .of_hom (Spec.map (CommRingCat.ofHom (algebraMap k' (traitSliceField k'))))
    refine boundedConstructible_nearbyCycles_affineSpace_of_projectiveSpace_of_finite T (n + 1)
      (boundedConstructible_nearbyCycles_projectiveSpace_of_finite T n hp hpT
        (fun hC ↦ ih hpK hpT hC) ?_)
    exact boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace
      (Profinite.continuousMapRingObj T) _ hB

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
