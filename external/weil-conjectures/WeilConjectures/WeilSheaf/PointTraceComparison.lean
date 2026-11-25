/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CohomologyNonneg
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.StalkFrobeniusPow
public import WeilConjectures.WeilSheaf.StalkRationalPoint
public import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# The Grothendieck–Lefschetz trace formula on the point

Let `G` be a Weil sheaf on `Spec k₀`, a scheme over itself through the identity, and let
`V = Γ(Spec k̄, G)` be its global sections with the geometric Frobenius `F`
(`AlgebraicGeometry.WeilSheaf.globalSections`). This file proves the Grothendieck–Lefschetz trace
formula for `G` directly, without the general machinery:

- *global side*: the direct image with compact support along the identity is the identity
  (`AlgebraicGeometry.WeilComplex.derivedLowerShriekIdObjIso`), so `H_c^i(Spec k̄, G)` is `V` for
  `i = 0` and zero otherwise, and `∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i) = Tr(Fᵐ | V)`;
- *local side*: the unique `𝔽_{qᵐ}`-point of `Spec k₀` gives a geometric point
  `s : Spec k̄ ≅ (Spec k₀)‾` which is an isomorphism, so restriction to the stalk at `s` is a
  linear isomorphism intertwining `Fᵐ` with the local Frobenius, and the trace function of `G` at
  this point is `Tr(Fᵐ | V)`.

## Main results

- `AlgebraicGeometry.WeilSheaf.finsum_trace_compactlySupportedCohomology_spec`: the global side.
- `AlgebraicGeometry.WeilSheaf.traceFunction_spec_eq_trace_globalSections`: the local side.
- `AlgebraicGeometry.WeilSheaf.finsum_trace_compactlySupportedCohomology_spec_eq_traceFunction`
  and `..._eq_finsum_traceFunction`: the Grothendieck–Lefschetz formula for Weil sheaves on
  `Spec k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- Two endomorphisms intertwined by a linear equivalence have the same trace. -/
theorem LinearMap.trace_eq_of_linearEquiv_comp_eq {R V W : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) {f : Module.End R V}
    {g : Module.End R W} (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    LinearMap.trace R W g = LinearMap.trace R V f := by
  have hg : g = e.conj f := by
    ext x
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    exact (LinearMap.congr_fun h x).symm
  rw [hg, LinearMap.trace_conj']

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The direct image with compact support along the identity is the identity: `R(𝟙)_! K ≅ K`,
the identity being proper (`AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar`)
and the pushforward along the identity being the identity. -/
noncomputable def WeilComplex.derivedLowerShriekIdObjIso (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) : (WeilComplex.derivedLowerShriek k₀ l (𝟙 X)).obj K ≅ K :=
  WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar (𝟙 X) K ≪≫ ObjectProperty.isoMk _
    ((Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X)).app K.obj ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).app K.obj ≪≫
      (Functor.mapDerivedCategoryIdIso _).app K.obj)

/-- `Spec k₀` has exactly one `K`-valued point over itself, for every field extension `K` of
`k₀`: the structure morphism `Spec K ⟶ Spec k₀`. -/
noncomputable instance Scheme.Hom.uniqueFieldPointsSpecSelf (K : Type u) [Field K]
    [Algebra k₀ K] :
    Unique ((Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints K) where
  default := ⟨Spec.map (CommRingCat.ofHom (algebraMap k₀ K)), Category.comp_id _⟩
  uniq y := Subtype.ext ((Category.comp_id _).symm.trans y.2)

namespace WeilSheaf

/-- **The global side of the trace formula on the point.** For a Weil sheaf `G` on `Spec k₀`,
the alternating sum of the traces of `Fᵐ` on the compactly supported cohomology
`H_c^i(Spec k̄, G)` is the trace of `Fᵐ` on the global sections `Γ(Spec k̄, G)`: the direct
image with compact support along the identity is the identity, so `H_c^0 = Γ(Spec k̄, G)` and
`H_c^i = 0` for `i ≠ 0`. -/
theorem finsum_trace_compactlySupportedCohomology_spec
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      (((toComplex.obj G).compactlySupportedCohomology i).frobeniusEnd ^ m) =
      LinearMap.trace (PadicAlgCl l) _ (G.globalSections.frobeniusEnd ^ m) := by
  let e := WeilComplex.derivedLowerShriekIdObjIso (l := l) (Spec (CommRingCat.of k₀))
    (toComplex.obj G)
  have h (i : ℤ) : LinearMap.trace (PadicAlgCl l) _
      (((toComplex.obj G).compactlySupportedCohomology i).frobeniusEnd ^ m) =
      LinearMap.trace (PadicAlgCl l) _
        (((WeilComplex.homologySheaf i).obj (toComplex.obj G)).globalSections.frobeniusEnd ^
          m) :=
    ((globalSectionsEquivOfIso ((WeilComplex.homologySheaf i).mapIso e)).trace_frobeniusEnd_pow
      m).symm
  rw [finsum_eq_single _ 0 fun i hi ↦ ?_, h, Int.negOnePow_zero, Units.val_one, one_smul]
  · exact ((globalSectionsEquivOfIso
      (toComplexCompHomologySheafIso.app G)).trace_frobeniusEnd_pow m).symm
  · have : Subsingleton
        ((WeilComplex.homologySheaf i).obj (toComplex.obj G)).globalSections.carrier :=
      subsingleton_globalSections_of_isZero (WeilComplex.isZero_homologySheaf_singleComplex hi G)
    rw [h, Subsingleton.elim (_ ^ m) 0, map_zero, smul_zero]

/-- **The local side of the trace formula on the point.** The trace function of a Weil sheaf
`G` on `Spec k₀` at the (unique) `𝔽_{qᵐ}`-point, `m ≥ 1`, is the trace of `Fᵐ` on the global
sections `Γ(Spec k̄, G)`: the geometric point over it is an isomorphism `Spec k̄ ≅ (Spec k₀)‾`,
so restriction to its stalk is a linear isomorphism intertwining `Fᵐ` with the local
Frobenius. -/
theorem traceFunction_spec_eq_trace_globalSections
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (m : ℕ) (hm : 1 ≤ m)
    (y : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ m)) :
    G.traceFunction m y =
      LinearMap.trace (PadicAlgCl l) _ (G.globalSections.frobeniusEnd ^ m) := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  set s := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint
    IsAlgClosed.lift y.1 y.2
  have hs := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) m IsAlgClosed.lift y
  have : IsIso (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsIso (𝟙 _))
  have : IsIso
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    pullback_snd_iso_of_left_iso _ _
  have : IsIso s := isIso_of_comp_hom_eq_id _
    (Scheme.Hom.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure _ _ _ _)
  let e : G.globalSections.carrier ≃ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
    WeilCoefficients.linearEquivOfIso (asIso (G.globalSectionsToStalkObj s))
  have he : e.toLinearMap = G.globalSectionsToStalkAt s m hs := rfl
  have hcomp := G.globalSectionsToStalkAt_comp_frobeniusEnd_pow s m hm hs
  rw [← he] at hcomp
  exact LinearMap.trace_eq_of_linearEquiv_comp_eq e hcomp

/-- The trace function of a Weil sheaf on `Spec k₀`, viewed as a Weil complex, at the
`𝔽_{qᵐ}`-point, `m ≥ 1`, is the trace of `Fᵐ` on the global sections. -/
theorem traceFunction_toComplex_spec_eq_trace_globalSections
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (m : ℕ) (hm : 1 ≤ m)
    (y : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ m)) :
    (toComplex.obj G).traceFunction m y =
      LinearMap.trace (PadicAlgCl l) _ (G.globalSections.frobeniusEnd ^ m) := by
  rw [WeilComplex.traceFunction_toComplex, traceFunction_spec_eq_trace_globalSections G m hm y]

/-- **The Grothendieck–Lefschetz trace formula for Weil sheaves on `Spec k₀`**, at the
unique `𝔽_{qᵐ}`-point, `m ≥ 1`: `∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(Spec k̄, G)) = t_{G,m}(y)`. -/
theorem finsum_trace_compactlySupportedCohomology_spec_eq_traceFunction
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (m : ℕ) (hm : 1 ≤ m)
    (y : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ m)) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      (((toComplex.obj G).compactlySupportedCohomology i).frobeniusEnd ^ m) =
      (toComplex.obj G).traceFunction m y := by
  rw [finsum_trace_compactlySupportedCohomology_spec,
    traceFunction_toComplex_spec_eq_trace_globalSections G m hm y]

/-- **The Grothendieck–Lefschetz trace formula for Weil sheaves on `Spec k₀`**, in the shape of
the general formula: for `m ≠ 0`,
`∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(Spec k̄, G)) = ∑_{y ∈ Spec k₀(𝔽_{qᵐ})} t_{G,m}(y)`. -/
theorem finsum_trace_compactlySupportedCohomology_spec_eq_finsum_traceFunction
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) {m : ℕ} (hm : m ≠ 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      (((toComplex.obj G).compactlySupportedCohomology i).frobenius.toLinearMap ^ m) =
      ∑ᶠ y : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ m),
        (toComplex.obj G).traceFunction m y := by
  refine .trans ?_ (finsum_unique _).symm
  exact finsum_trace_compactlySupportedCohomology_spec_eq_traceFunction G m
    (Nat.one_le_iff_ne_zero.2 hm) default

end WeilSheaf

end AlgebraicGeometry
