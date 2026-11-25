/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.Topology.Maps.Basic
public import WeilConjectures.Mathlib.Topology.Sober
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# A lisse Weil sheaf on a smooth curve is the middle extension of its restriction

If `F` is a lisse Weil sheaf on a smooth curve `C₀` over `k₀` and `j : U₀ ⟶ C₀` is a dense
quasi-compact open immersion, then the unit `F ⟶ j_* j^* F` of the adjunction `j^* ⊣ j_*` is an
isomorphism (blueprint: `lemma-boundary-stalk--2`). The étale finite-coefficient version is
`AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction`.

On the geometric fibres this is
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app`:
the geometric fibre `C̄` is smooth over `k̄`, hence regular, and the base change `j̄` of `j` still
has dense image (`AlgebraicGeometry.Scheme.Hom.dense_range_geometricFiberMap`). The latter holds
because the projection `C̄ ⟶ C` is flat, so it lifts generalizations and maps the generic points
of `C̄` to generic points of `C`, and the generic points of a locally Noetherian scheme lie in
every dense open subset.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.isIso_upperStarLowerStarAdjunction_unit_app` and
  `AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`: blueprint
  `lemma-boundary-stalk--2`.
-/

@[expose] public section

universe u

open CategoryTheory Topology TopologicalSpace

/-- In a Noetherian space, a dense open subset contains the generic points of all irreducible
components: the complement of the other components is a nonempty open subset of a component,
which meets the dense open. -/
theorem genericPoints_subset_of_isOpen_of_dense {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {U : Set α} (hU : IsOpen U) (hd : Dense U) : genericPoints α ⊆ U := by
  intro c hc
  obtain ⟨o, ho, hne, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨v, hvo, hvU⟩ := hd.inter_open_nonempty o ho hne
  exact (specializes_iff_mem_closure.2 (hoZ hvo)).mem_open hU hvU

namespace AlgebraicGeometry

/-- In a locally Noetherian scheme, a dense open subset contains the generic points of all
irreducible components. -/
theorem Scheme.genericPoints_subset_of_isOpen_of_dense {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : Set X} (hU : IsOpen U) (hd : Dense U) : genericPoints X ⊆ U := by
  intro c hc
  obtain ⟨_, ⟨V, hV, rfl⟩, hcV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ c) isOpen_univ
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  have : QuasiSober (V : Set X) := V.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  have hc' : (⟨c, hcV⟩ : (V : Set X)) ∈ genericPoints (V : Set X) := by
    rw [mem_genericPoints_iff_forall_specializes] at hc ⊢
    exact fun y hy ↦ Subtype.ext (hc _ (hy.map continuous_subtype_val))
  exact _root_.genericPoints_subset_of_isOpen_of_dense (α := (V : Set X))
    (hU.preimage continuous_subtype_val)
    (hd.preimage_val V.isOpen) hc'

variable {k₀ : Type u} [Field k₀]

/-- The base change `j̄ : Ū ⟶ C̄` to the algebraic closure of an open immersion `j : U ⟶ C` with
dense image into a `k₀`-scheme locally of finite type has dense image: its image is the preimage
of the image of `j` under the flat projection `C̄ ⟶ C`, which maps generic points of `C̄` to
generic points of `C`, and these lie in the dense open image of `j`. -/
theorem Scheme.Hom.dense_range_geometricFiberMap {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (hj : Dense (Set.range j.base)) :
    Dense (Set.range
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))).base) := by
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : Flat (C ↘ Spec (CommRingCat.of k₀)).geometricFiberProj :=
    MorphismProperty.pullback_fst _ _
      (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance) :
        Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))))
  have hrange : Set.range
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))).base =
      (C ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.base ⁻¹' Set.range j.base :=
    Scheme.range_snd_of_isPullback (Scheme.Hom.isPullback_geometricFiberMap j _).flip
  rw [hrange]
  refine dense_of_genericPoints_subset fun η hη ↦ ?_
  refine Scheme.genericPoints_subset_of_isOpen_of_dense j.isOpenEmbedding.isOpen_range hj ?_
  rw [mem_genericPoints_iff_forall_specializes] at hη ⊢
  intro c hc
  obtain ⟨η', hη'η, rfl⟩ :=
    Flat.generalizingMap (C ↘ Spec (CommRingCat.of k₀)).geometricFiberProj hc
  rw [hη _ hη'η]

/-- The geometric fibre of a smooth `k₀`-scheme has regular local rings. -/
theorem isRegularLocalRing_stalk_geometricFiber {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [Smooth (C ↘ Spec (CommRingCat.of k₀))]
    (c : (C ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    IsRegularLocalRing ((C ↘ Spec (CommRingCat.of k₀)).geometricFiber.presheaf.stalk c) := by
  have : Smooth (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  infer_instance

variable [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Recovery from a dense lisse open**, strong form. Let `C₀` be a smooth curve over `k₀`,
`j : U₀ ⟶ C₀` a quasi-compact open immersion with dense image and `F` a lisse Weil sheaf on
`C₀`. Then the unit `F ⟶ j_* j^* F` of the adjunction `j^* ⊣ j_*` is an isomorphism: on the
geometric fibres this is
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app`.
(blueprint: `lemma-boundary-stalk--2`) -/
theorem WeilSheaf.IsLisse.isIso_upperStarLowerStarAdjunction_unit_app {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    IsIso ((WeilSheaf.upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app F) := by
  have : Smooth (C ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsIso ((WeilSheaf.upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app
      F).hom.hom.f := by
    rw [WeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_hom_f]
    exact ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app
      isRegularLocalRing_stalk_geometricFiber _
      (Scheme.Hom.dense_range_geometricFiberMap j hj) hF
  exact WeilSheaf.isIso_of_isIso_hom_hom_f _

/-- **Recovery from a dense lisse open.** Let `C₀` be a smooth curve over `k₀`, `j : U₀ ⟶ C₀` a
quasi-compact open immersion with dense image and `F` a lisse Weil sheaf on `C₀`. Then
`F ≅ j_* j^* F`: on `U₀` this is clear, and at a removed point `x` the stalk of `j_* j^* F` is
the inertia invariants `(F_η̄)^{I_x} = F_x̄`, the inertia acting trivially since `F` is lisse at
`x`. The isomorphism is the unit of `j^* ⊣ j_*`
(`AlgebraicGeometry.WeilSheaf.IsLisse.isIso_upperStarLowerStarAdjunction_unit_app`).
(blueprint: `lemma-boundary-stalk--2`) -/
theorem WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    Nonempty (F ≅ (WeilSheaf.directImage j).obj ((WeilSheaf.upperStar j).obj F)) := by
  have := hF.isIso_upperStarLowerStarAdjunction_unit_app j hj
  exact ⟨eqToIso (Functor.id_obj F).symm ≪≫
    asIso ((WeilSheaf.upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app F) ≪≫
      eqToIso (Functor.comp_obj _ _ F)⟩

end AlgebraicGeometry
