/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.HomotopyInvariance
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.LowerShriekForget

/-!
# Weil complexes on the trivial line bundle

Let `π : Y ⟶ X` be the trivial line bundle `Y ≅ X ×_{k₀} 𝔸¹` over a `k₀`-scheme `X`, given by a
cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. This file proves the inputs from which the
rank-one Thom isomorphism `Rπ₀! π^* P ≅ P(-1)[-2]` (blueprint `lemma-integral-linear-character--1`,
stated in `WeilConjectures.WeilSheaf.FourierInversion.OtherSections`) follows:

- homotopy invariance: the unit `K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism
  (`WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`);
- the affine-line adjunction `Rπ₀! ⊣ π^*(1)[2]` from a Weil trace
  (`AlgebraicGeometry.WeilComplex.nonempty_adjunction_derivedLowerShriek_of_weilTrace`): the
  morphisms of Weil complexes are computed from the underlying `ℓ`-adic morphisms through free
  Weil objects, with which `Rπ₀!` commutes;
- the Thom isomorphism from these two
  (`AlgebraicGeometry.WeilComplex.upperStarCompDerivedLowerShriekIsoOfAdjunction`): `π^* ⋙ Rπ₀!`
  is left adjoint to `(1)[2] ⋙ π^* ⋙ Rπ_* ≅ (1)[2]`, whose left adjoint is also the inverse
  autoequivalence `(-1)[-2]`.

The Weil-equivariant trace of the affine line (`proposition-purity-trace-commute-frobenius`)
is not formalized for Weil complexes, so the Thom isomorphism itself is not deduced here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section TrivialLineBundle

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- **The affine-line adjunction for Weil complexes from a Weil trace** (the Weil form of
`lemma-affine-space-etale-localization--1` for `d = 1`). Let `π : Y ⟶ X` be a separated morphism of
finite type, for instance the trivial line bundle `Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, and let
`ε_P : Rπ₀! π^*(P(1)[2]) ⟶ P` be a natural morphism of Weil complexes whose underlying morphism
has the universal property of a counit of `Rπ̄_! ⊣ π̄^*(1)[2]` on the geometric fibres: for every
Weil complex `K` on `Y`, the map `φ ↦ Rπ̄_! φ ≫ For ε_P` out of
`Hom(For K, For π^*(P(1)[2]))` is bijective. Then `Rπ₀!` is left adjoint to `P ↦ π^*(P(1)[2])`
with counit `ε`. The morphisms of Weil complexes are computed from the underlying `ℓ`-adic
morphisms through free Weil objects, with which `Rπ₀!` commutes
(`AlgebraicGeometry.WeilComplex.isIso_freeComparison_rightDerivedLowerShriek`,
`AlgebraicGeometry.WeilComplex.bijective_map_comp_derivedLowerShriek`).

For the trivial line bundle such an `ε` is the Weil-equivariant trace of the affine line
(`proposition-purity-trace-commute-frobenius`); it is not formalized for Weil complexes. -/
theorem nonempty_adjunction_derivedLowerShriek_of_weilTrace
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (ε : ((tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) ⋙
        derivedLowerShriek k₀ l π ⟶ 𝟭 (WeilComplex k₀ l X))
    (hε : ∀ (K : WeilComplex k₀ l Y) (P : WeilComplex k₀ l X),
      Function.Bijective fun φ : forget.obj K ⟶ forget.obj
          (((tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙
            upperStar π).obj P) ↦
        (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l π
            (lowerShriekCompactification k₀ π)).map φ ≫
          (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l π
            (lowerShriekCompactification k₀ π)).inv.app _ ≫ forget.map (ε.app P)) :
    Nonempty (derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) := by
  refine ⟨Adjunction.ofBijectiveCounit (L := derivedLowerShriek k₀ l π)
    (R := (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) ε ?_⟩
  intro K P
  have key := bijective_map_comp_derivedLowerShriek (k₀ := k₀) (l := l) π (K := K)
    (P := ((tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π).obj P)
    (T := P) (ε.app P)
  exact key (fun n ↦ isIso_freeComparison_rightDerivedLowerShriek π K n) fun n ↦
    (Adjunction.bijective_map_comp_iff_of_iso _ _
      ((CategoryTheory.Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory.mapIso
          (((WeilComplex.objectProperty k₀ l Y).ι.commShiftIso n).app K) ≪≫
        ((CategoryTheory.Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory.commShiftIso n).app K.obj)).1
      (hε ((shiftFunctor _ n).obj K) P)

include hπ in
/-- **The Weil-equivariant trace of the affine line** (cross-section input: blueprint
`proposition-purity-trace-commute-frobenius` for the trivial line bundle, together with the
`ℓ`-adic form of `lemma-affine-space-etale-localization--1` for `d = 1` on the geometric fibres).
For the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X`
over `Spec k₀`, there is a natural morphism of Weil complexes `ε_P : Rπ₀! π^*(P(1)[2]) ⟶ P`, the
trace, whose underlying morphism is the counit of `Rπ̄_! ⊣ π̄^*(1)[2]` on the geometric fibres: for
every Weil complex `K` on `Y`, `φ ↦ Rπ̄_! φ ≫ For ε_P` is a bijection
`Hom(For K, For π^*(P(1)[2])) ≃ Hom(Rπ̄_! For K, For P)`.

The geometric adjunction is the `ℓ`-adic transport of
`AlgebraicGeometry.Etale.nonempty_adjunction_affineLine`; on the condensed `ℚ̄_ℓ`-model it follows
from `AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth` and
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`. Neither its comparison with `ℓ`-adic
sheaves on the geometric fibres nor the Weil structure on the trace is formalized: the Weil trace
cannot be lifted objectwise from the geometric one (`Hom(K̄, L̄[-1]) ≠ 0`), and there is no Weil
tensor product or Weil Chern class to construct it. -/
theorem exists_weilTrace_of_isPullback [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    ∃ ε : ((tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) ⋙
        derivedLowerShriek k₀ l π ⟶ 𝟭 (WeilComplex k₀ l X),
      ∀ (K : WeilComplex k₀ l Y) (P : WeilComplex k₀ l X),
        Function.Bijective fun φ : forget.obj K ⟶ forget.obj
            (((tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙
              upperStar π).obj P) ↦
          (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l π
              (lowerShriekCompactification k₀ π)).map φ ≫
            (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l π
              (lowerShriekCompactification k₀ π)).inv.app _ ≫ forget.map (ε.app P) :=
  sorry

include hπ in
/-- **The affine-line adjunction for Weil complexes** (the Weil form of
`lemma-affine-space-etale-localization--1` for `d = 1`). For the trivial line bundle
`π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the
direct image with compact support `Rπ₀!` of Weil complexes is left adjoint to `P ↦ π^*(P(1)[2])`,
with counit the Weil-equivariant trace
(`AlgebraicGeometry.WeilComplex.exists_weilTrace_of_isPullback`,
`AlgebraicGeometry.WeilComplex.nonempty_adjunction_derivedLowerShriek_of_weilTrace`). -/
theorem nonempty_adjunction_derivedLowerShriek_of_isPullback :
    Nonempty (derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) := by
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  obtain ⟨ε, hε⟩ := exists_weilTrace_of_isPullback π s hπ (l := l)
  exact nonempty_adjunction_derivedLowerShriek_of_weilTrace π ε hε

include hπ in
/-- Blueprint `lem-pur-a1-direct-image` (for all Weil complexes): **homotopy invariance**. For
the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square
`Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the unit `K ⟶ Rπ_* π^* K` of the adjunction `π^* ⊣ Rπ_*` of
Weil complexes is an isomorphism for every Weil complex `K` on `X`; that is, `π^*` is fully
faithful.

For `K = Λ_X` with finite étale coefficients over an algebraically closed field this is
`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`; for general `K` it follows from
the constant case by smooth base change (`theorem-smooth-base-change-classical-torsion--1`) and the
acyclicity of the affine line over strictly henselian bases. Here it is deduced from the case of a
reduced scheme (`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isClosedImmersion_of_isReduced`):
`K` is the direct image of its restriction to the reduced subscheme `X_red`, whose open complement
is empty, and smooth base change carries the unit along this direct image
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`). -/
theorem isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback
    (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian X := ⟨⟩
  -- the reduced closed subscheme `r : X_red ⟶ X`, with empty open complement `j`
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)
  let r := I.subschemeι
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨r ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : r.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  let j := (⊥ : X.Opens).ι
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have hr : Set.range r = (⊤ : TopologicalSpace.Closeds X) := by simp [r, I]
  have hc : IsCompl (Set.range r.base) (Set.range j.base) := by
    rw [Set.range_eq_empty j.base]
    rw [show Set.range r.base = Set.univ by simpa using hr]
    exact isCompl_top_bot
  -- `K` is the direct image of its restriction to `X_red`
  obtain ⟨M, ⟨e⟩⟩ := derivedLowerStar_essImage_of_isZero r j hc K (isZero_of_isEmpty _)
  have := isIso_unit_app_derivedLowerStar_obj π s hπ r M
    fun Y' _ π' s' _ hπ' _ _ _ ↦ isIso_unit_app_of_isClosedImmersion_of_isReduced ⊤ I.subscheme r
      (Set.subset_univ _) Y' π' s' hπ' M
  exact (upperStarDerivedLowerStarAdjunction π).unit.isoLocus.prop_of_iso e this

/-- **The Thom isomorphism from the affine-line adjunction and homotopy invariance.** If `Rπ₀!` is
left adjoint to `P ↦ π^*(P(1)[2])` and the unit of `π^* ⊣ Rπ_*` is an isomorphism, then
`Rπ₀! π^* P ≅ P(-1)[-2]` naturally in `P`: `π^* ⋙ Rπ₀!` is left adjoint to
`(1)[2] ⋙ π^* ⋙ Rπ_* ≅ (1)[2]`, whose left adjoint is also `(-1)[-2]`. -/
noncomputable def upperStarCompDerivedLowerShriekIsoOfAdjunction
    (adj : derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π)
    [IsIso (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit] :
    upperStar π ⋙ derivedLowerShriek k₀ l π ≅
      tateTwist k₀ l X (-1) ⋙ shiftFunctor (WeilComplex k₀ l X) (-2 : ℤ) :=
  (((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).comp adj).ofNatIsoRight
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (asIso (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit).symm ≪≫
      Functor.rightUnitor _)).leftAdjointUniq
    (tateTwistShiftEquiv k₀ l X (-1) 1 (-2) 2 (by norm_num) (by norm_num)).toAdjunction

end TrivialLineBundle

end AlgebraicGeometry.WeilComplex
