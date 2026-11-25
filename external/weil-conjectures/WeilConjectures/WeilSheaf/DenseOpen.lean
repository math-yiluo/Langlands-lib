/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# Lisse sheaves and dense opens

Let `j : U ↪ X` be a dense open immersion of `k₀`-schemes, with `X` smooth over `k₀`. Since the
fundamental group of a dense open of a connected normal scheme surjects onto that of the scheme,
lisse sheaves on `X` are determined by their restriction to `U`:

- if `X` is a smooth curve, `j̄_* ℚ̄_ℓ ≅ ℚ̄_ℓ`, from the description of a lisse Weil sheaf as the
  direct image of its restriction to `U` (blueprint `lemma-boundary-stalk--2`);
- if `X` is a smooth curve, the restriction `j^*` is fully faithful on lisse Weil sheaves;
- if `X` is a smooth geometrically connected curve, the restriction `j^*` carries irreducible
  lisse Weil sheaves to irreducible lisse Weil sheaves.

The last two are part (4) of the blueprint lemma `theorem-purity-real-sheaves-curves` (subsection
`lemma-boundary-stalk--2`). The geometric versions, for lisse `ℓ`-adic sheaves on the geometric
curves, are in `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.adicUpperStar_map_bijective`,
`AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem.adicUpperStar`).

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_adicLowerStar_unit_iso_geometricFiberMap`:
  `j̄_* ℚ̄_ℓ ≅ ℚ̄_ℓ`.
- `AlgebraicGeometry.WeilSheaf.upperStar_map_bijective_of_isLisse`: restriction to a dense open
  of a curve is fully faithful on lisse Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant`: restriction to a
  dense open of a curve preserves irreducibility.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtale

variable [Fact (ringChar k₀ ≠ l)]

/-- For a dense quasi-compact open immersion `j : U ↪ X` of `k₀`-schemes with `X` a smooth curve
over `k₀`, the pushforward `j̄_* ℚ̄_ℓ` of the constant sheaf of the geometric fiber `Ū` is the
constant sheaf of `X̄`: the constant Weil sheaf is lisse, hence the direct image of its
restriction to `U` (`AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`,
blueprint `lemma-boundary-stalk--2`), and the restriction of `ℚ̄_ℓ` is `ℚ̄_ℓ`. -/
theorem nonempty_adicLowerStar_unit_iso_geometricFiberMap
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].obj
        (AdicSheaf.unit l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  obtain ⟨e⟩ := (WeilSheaf.isLisse_adicConstant k₀ l X).nonempty_iso_directImage_upperStar j
    j.denseRange
  let E := ((WeilSheaf.objectProperty k₀ l X).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapIso e
  exact ⟨(Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].mapIso
    (adicUpperStarUnitIso l _).symm ≪≫ E.symm⟩

end ProEtale

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

/-- **Restriction to a dense open of a curve is fully faithful on lisse Weil sheaves.** Let `X` be
a smooth curve over `k₀`, `j : U ↪ X` a quasi-compact open immersion with dense image and `N` a
lisse Weil sheaf on `X`. Then `Hom(A, N) → Hom(j^* A, j^* N)` is bijective for every Weil sheaf
`A`: the unit `N ⟶ j_* j^* N` is an isomorphism
(`AlgebraicGeometry.WeilSheaf.IsLisse.isIso_upperStarLowerStarAdjunction_unit_app`), and under
the adjunction `j^* f` corresponds to `f` followed by the unit.
(blueprint: `theorem-purity-real-sheaves-curves`, part (4), subsection `lemma-boundary-stalk--2`) -/
theorem upperStar_map_bijective_of_isLisse
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (hj : Dense (Set.range j.base))
    (A : WeilSheaf k₀ l X) {N : WeilSheaf k₀ l X} (hN : N.IsLisse) :
    Function.Bijective
      ((upperStar j).map : (A ⟶ N) → ((upperStar j).obj A ⟶ (upperStar j).obj N)) := by
  have := hN.isIso_upperStarLowerStarAdjunction_unit_app j hj
  exact (upperStarLowerStarAdjunction j).map_bijective_of_isIso_unit_app A

/-- *Restriction to a dense open of a curve preserves irreducibility.* Let `X` be a smooth
geometrically connected quasi-compact curve over `k₀` and `j : U ↪ X` a dense open immersion.
The restriction `j^*` carries irreducible lisse Weil sheaves on `X` to irreducible lisse Weil
sheaves on `U`: the Weil group of `U` surjects onto that of `X`.

A lisse Weil subsheaf `G'` of `j^* M` has a lisse direct image `j_* G'`: on the geometric curves
this is `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.adicLowerStar_of_mono`, by the surjectivity
of `π₁(Ū) → π₁(X̄)`. As `j^* j_* G' ≅ G'`, the inclusion `G' ⟶ j^* M` is the restriction of a
monomorphism `j_* G' ⟶ M` by full faithfulness
(`AlgebraicGeometry.WeilSheaf.upperStar_map_bijective_of_isLisse`), to which the irreducibility
of `M` applies.
(blueprint: `theorem-purity-real-sheaves-curves`, part (4), subsection `lemma-boundary-stalk--2`) -/
theorem IsIrreducibleLisse.upperStar_of_isDominant
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {M : WeilSheaf k₀ l X} (hM : M.IsIrreducibleLisse) :
    ((upperStar j).obj M).IsIrreducibleLisse := by
  have : Smooth (X ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have hj : Dense (Set.range j.base) := j.denseRange
  have hMl : M.IsLisse := hM.1
  obtain ⟨-, hM0, hMirr⟩ := hM
  have hjM : ¬ IsZero ((upperStar j).obj M) := fun h ↦ hM0 (by
    have := hMl.isIso_upperStarLowerStarAdjunction_unit_app j hj
    exact ((lowerStar j).map_isZero h).of_iso
      (asIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).unit.app M)))
  refine ⟨IsLisse.upperStar hMl j, hjM, fun G' i _ hG' ↦ ?_⟩
  -- the geometric curve `X̄` is connected, regular and locally Noetherian
  have : ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (CommRingCat.of k₀))
      (Scheme.specAlgebraicClosure k₀).hom (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (IsPullback.of_hasPullback _ _)
  have : Smooth (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  have := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : Nonempty (U ↘ Spec (CommRingCat.of k₀)).geometricFiber := not_isEmpty_iff.1 fun _ ↦
    hjM (isZero_iff_isZero_carrier.2 (ProEtale.isZero_adicSheaf_of_isEmpty l _))
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j (Spec (CommRingCat.of k₀))]
    infer_instance
  have : Mono i.hom.hom.f := (carrierFunctor k₀ l U).map_mono i
  -- the direct image `j_* G'` is lisse and restricts to `G'`
  have hK : ((lowerStar j).obj G').IsLisse := ProEtale.IsAdicLisseSheaf.adicLowerStar_of_mono
    (Scheme.Hom.geometricFiberMap j (comp_over j _))
    (Scheme.Hom.dense_range_geometricFiberMap j hj) hMl hG' i.hom.hom.f
  let e : (upperStar j).obj ((lowerStar j).obj G') ≅ G' :=
    asIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app G')
  obtain ⟨g, hg⟩ := (upperStar_map_bijective_of_isLisse j hj _ hMl).2 (e.hom ≫ i)
  have : Mono ((upperStar j).map g) := by
    rw [hg]
    infer_instance
  have : Mono g := ⟨fun a b hab ↦ (upperStar_map_bijective_of_isLisse j hj _ hK).1 (by
    rw [← cancel_mono ((upperStar j).map g), ← Functor.map_comp, ← Functor.map_comp, hab])⟩
  obtain h | h := hMirr _ g inferInstance hK
  · exact Or.inl (((upperStar j).map_isZero h).of_iso e.symm)
  · have : IsIso (e.hom ≫ i) := by
      rw [← hg]
      infer_instance
    exact Or.inr (IsIso.of_isIso_comp_left e.hom i)

end WeilSheaf

end AlgebraicGeometry
