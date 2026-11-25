/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsion

/-!

# Deligne's finiteness theorem for the nearby cycles of models, finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic exponent `p`, and `T` a finite
discrete ring in which `p` is invertible and whose exponent is invertible in `k'`. Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) with finite coefficients: for every model
`M` of finite type over `S`, the geometric nearby cycles carry bounded constructible complexes of
`T̲`-modules on the total space to bounded constructible complexes on the special fibre
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_finite`), hence the nearby
cycles of a model whose identification factors through the total space preserve bounded
constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel_of_finite`).

The proof follows the `ℚ̄_ℓ` case
(`WeilConjectures.TraceFormula.Specialization.NearbyFiniteness`): the theorem is local on a
finite affine open cover of the total space, an affine total space embeds into an affine space
`𝔸ⁿ_S`, and the reduction along this closed embedding
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding_of_finite`)
uses the proper exchange with finite coefficients
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`). The case
of the affine spaces is
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- The inclusion `j` of the geometric generic fibre of a model of finite type over the trait is
quasi-compact. -/
lemma IsTraitModel.quasiCompact_j {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    QuasiCompact M.j := by
  obtain ⟨q, g, _, _, _, hj, -⟩ := hM.exists_isPullback
  exact MorphismProperty.of_isPullback (P := @QuasiCompact) hj.flip inferInstance

/-- The inclusion `j` of the geometric generic fibre of a model of finite type over the trait is
quasi-separated. -/
lemma IsTraitModel.quasiSeparated_j {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    QuasiSeparated M.j := by
  obtain ⟨q, g, _, _, _, hj, -⟩ := hM.exists_isPullback
  exact MorphismProperty.of_isPullback (P := @QuasiSeparated) hj.flip inferInstance

/-- **Reduction along a closed embedding of models, finite coefficients**: let `φ : M ⟶ N` be a
morphism of models of finite type over the trait whose morphism of total spaces `t` is a closed
immersion and whose squares of geometric generic and special fibres are cartesian. If the
geometric nearby cycles of `N` preserve bounded constructible complexes of `T̲`-modules, then so
do those of `M`: `Ψ_M B ≅ Lt_s^* Rt_{s*} Ψ_M B ≅ Lt_s^* Ψ_N (Rt_* B)` by the full faithfulness of
`Rt_{s*}` and the proper exchange
(`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`). -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding_of_finite
    {Y : Scheme.{u}} {Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} (hM : M.IsTraitModel) (hN : N.IsTraitModel)
    {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left} (φ : M.geometric.Hom N.geometric t f')
    (ht : φ.total = t) [IsClosedImmersion t] (hj : IsPullback φ.generic M.j N.j t)
    (hi : IsPullback M.i f' t N.i)
    (hN' : ∀ {B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.total))},
      boundedConstructible _ B' → boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj T) Y'.left)
        ((N.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B'))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)
      ((M.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B) := by
  have := hN.isNoetherian_total
  have : IsClosedImmersion f' := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hi ‹_›
  have : IsProper t := inferInstance
  have : IsProper φ.total := by rw [ht]; infer_instance
  have : QuasiCompact M.geometric.j := hM.quasiCompact_j
  have : QuasiSeparated M.geometric.j := hM.quasiSeparated_j
  have : IsIso ((φ.pushforwardExchange (Profinite.continuousMapRingObj T)).app B) :=
    Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T φ (by rw [ht]; exact hi)
      hj.flip B (boundedConstructible_iff_of_finite T B |>.1 hB).plusEtaleOrigin
  have h₁ : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) Y'.left)
      ((N.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj
        ((R((t)_*⟦Profinite.continuousMapRingObj T⟧)).obj B)) :=
    hN' (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ t hB)
  have h₂ : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) Y'.left)
      ((R((f')_*⟦Profinite.continuousMapRingObj T⟧)).obj
        ((M.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B)) :=
    (boundedConstructible _).prop_of_iso
      (asIso ((φ.pushforwardExchange (Profinite.continuousMapRingObj T)).app B)) h₁
  exact (boundedConstructible _).prop_of_iso
    (asIso ((derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f').counit.app
      _))
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' _ h₂)

variable [IsSepClosed k'] [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))] {p : ℕ}
  [Fact p.Prime]

/-- **Reduction to affine spaces, finite coefficients**: for a model `M` of finite type over the
trait with affine total space, the geometric nearby cycles preserve bounded constructible
complexes of `T̲`-modules. Embed the total space as a closed subscheme of `𝔸ⁿ_S` and apply
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding_of_finite`
and `NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_isAffine_of_finite
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel) [IsAffine M.total]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)
      ((M.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B) := by
  obtain ⟨q, g, _, _, _, hj, hi⟩ := hM.exists_isPullback
  obtain ⟨n, c, hc, _⟩ := exists_isClosedImmersion_affineSpace_of_isAffine q
  exact boundedConstructible_geometricNearbyCycles_obj_of_closedEmbedding_of_finite T
    (N := affineSpaceModel k' n) hM (isTraitModel_affineSpaceModel n) (traitStdHom _ hj hi c hc)
    rfl (isPullback_traitStdHom_generic _ hj hi c hc) (isPullback_traitStdHom_special _ hi c hc)
    (fun hB' ↦ boundedConstructible_nearbyCycles_affineSpace_obj_of_finite T n hp hpT hB') hB

/-- **Deligne's finiteness theorem for nearby cycles, finite coefficients** (SGA 4½,
[Th. finitude], Thm. 3.2): for a model `M` of finite type over the strictly henselian trait
`Spec k'⟦t⟧`, the geometric nearby cycles `Li^* Rj_* Lj^*` carry bounded constructible complexes
of `T̲`-modules on the total space to bounded constructible complexes on the special fibre. This is
local on a finite affine open cover of the total space
(`NearbyCyclesModel.isIso_pullbackExchange_restrictHom`), and the affine case is
`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_isAffine_of_finite`. -/
theorem boundedConstructible_geometricNearbyCycles_obj_of_finite
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X'.left)
      ((M.geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B) := by
  have := hM.isNoetherian_total
  have := isNoetherian_of_isTraitModel hM
  obtain ⟨n, V, hV⟩ := hM.exists_affineOpens_cover
  refine boundedConstructible_of_openCover _ (fun a ↦ M.i ⁻¹ᵁ (V a : M.total.Opens))
    (fun x ↦ hV (M.i.base x)) _ fun a ↦ ?_
  have : TopologicalSpace.NoetherianSpace (V a : M.total.Opens) :=
    (V a : M.total.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (V a : M.total.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsAffine (M.restrict (V a : M.total.Opens)).total := (V a).2
  have := isIso_pullbackExchange_restrictHom (Profinite.continuousMapRingObj T) M (V a)
  exact (boundedConstructible _).prop_of_iso
    (asIso (((M.restrictHom (V a)).pullbackExchange (Profinite.continuousMapRingObj T)).app B)).symm
    (boundedConstructible_geometricNearbyCycles_obj_of_isAffine_of_finite T hp hpT _
      (hM.restrict _) (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hB))

/-- **Deligne's finiteness theorem for the nearby cycles of a model, finite coefficients**
(SGA 4½, [Th. finitude], Thm. 3.2): over the strictly henselian trait `Spec k'⟦t⟧`, the nearby
cycles `Ψ = Li^* Rj_* Lε^*` of a model of finite type whose identification factors as `ε = j ≫ e`
through the total space preserve bounded constructible complexes of `T̲`-modules:
`Lε^* A ≅ Lj^* Le^* A`, and `Le^* A` is bounded constructible. -/
theorem preservesBoundedConstructible_of_isTraitModel_of_finite
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    M.PreservesBoundedConstructible (Profinite.continuousMapRingObj T) := by
  obtain ⟨e, he⟩ := hε
  intro K hK
  have hB := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.continuousMapRingObj T) e K hK
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.continuousMapRingObj T)
    he.symm K).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.continuousMapRingObj T) M.j e).app K
  exact (boundedConstructible _).prop_of_iso
    ((L((M.i)^*⟦Profinite.continuousMapRingObj T⟧)).mapIso
      ((R((M.j)_*⟦Profinite.continuousMapRingObj T⟧)).mapIso (i₁ ≪≫ i₂)).symm)
    (boundedConstructible_geometricNearbyCycles_obj_of_finite T hp hpT M hM hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
