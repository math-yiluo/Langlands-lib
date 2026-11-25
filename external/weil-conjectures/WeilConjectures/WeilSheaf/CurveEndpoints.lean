/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZeroSpecializes
public import WeilConjectures.WeilSheaf.CohomologicalRange
public import WeilConjectures.WeilSheaf.CohomologyDegreeZero
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.ConstantTwistWeight
public import WeilConjectures.WeilSheaf.CurveTopCohomology
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarLowerStar

/-!
# The two endpoints of the compactly supported cohomology of a middle extension

For a dense open immersion `j : U₀ ↪ C₀` into a smooth geometrically connected affine curve
and a lisse Weil sheaf `F` on `U₀`, all the compactly supported cohomology of the ordinary
direct image `j_*F` outside degrees `0, 1, 2` vanishes, degree zero vanishes as well because a
nonzero global section of a lisse sheaf on a connected open has full support on a nonproper
curve, and degree two is the geometric coinvariants `V_{π₁(U)}` Tate-twisted by `(-1)`, by
global Verdier duality on the smooth nonproper curve `U`. Purity of `F` of weight `w`
therefore makes degree two pure of weight `w + 2`.

This leaves degree one, which is the only place where the Fourier argument of
`WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` is needed.

## Main statements

- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`: vanishing outside
  degrees `0, 1, 2`.
- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`: vanishing in
  degree zero.
- `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`: the
  coinvariant description of degree two.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: its
  purity.
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Compactification.over

universe u

open CategoryTheory TopologicalSpace Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

section Complement

omit [Finite k₀] [IsAffine C] in
/-- A smooth geometrically connected curve is irreducible. -/
lemma irreducibleSpace_of_geometricallyConnected
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] : IrreducibleSpace C := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) :=
    .of_smooth_of_geometricallyConnected _
  exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := C ↘ Spec (CommRingCat.of k₀))

omit [Finite k₀] in
include k₀ in
/-- A smooth affine curve is a noetherian topological space. -/
lemma noetherianSpace_of_curve : NoetherianSpace C := by
  have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian C := {}
  infer_instance

omit [Finite k₀] [IsAffine C] in
include k₀ in
/-- A smooth curve has dimension at most one. -/
lemma topologicalKrullDim_le_one_of_curve : topologicalKrullDim C ≤ 1 := by
  exact_mod_cast
    topologicalKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1

variable {U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsDominant j]

omit [Finite k₀] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j] in
include k₀ j in
/-- A dense open of a nonempty scheme is nonempty. -/
lemma nonempty_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    Nonempty U := by
  have : Surjective (C ↘ Spec (CommRingCat.of k₀)) := inferInstance
  obtain ⟨c, -⟩ := (C ↘ Spec (CommRingCat.of k₀)).surjective
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k₀))))
  by_contra hU
  rw [not_nonempty_iff] at hU
  have hd := j.denseRange
  rw [DenseRange, Set.range_eq_empty] at hd
  have h := hd.closure_eq
  rw [closure_empty] at h
  have hc : c ∈ (Set.univ : Set C) := trivial
  rw [← h] at hc
  exact hc


omit [Finite k₀] in
include k₀ in
/-- The complement of a dense open of a smooth geometrically connected curve is finite. -/
lemma finite_compl_range_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    (Set.range j.base)ᶜ.Finite := by
  have := irreducibleSpace_of_geometricallyConnected (k₀ := k₀) (C := C)
  have := noetherianSpace_of_curve (k₀ := k₀) (C := C)
  have := nonempty_of_isDominant (k₀ := k₀) j
  exact j.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
    (topologicalKrullDim_le_one_of_curve (k₀ := k₀)) (Set.range_nonempty _)

omit [Finite k₀] in
include k₀ j in
/-- A dense open of a smooth geometrically connected affine curve is affine. -/
lemma isAffine_of_isDominant [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    IsAffine U := by
  have := irreducibleSpace_of_geometricallyConnected (k₀ := k₀) (C := C)
  have := noetherianSpace_of_curve (k₀ := k₀) (C := C)
  have := nonempty_of_isDominant (k₀ := k₀) j
  exact isAffine_of_isOpenImmersion_of_topologicalKrullDim_le_one j
    (topologicalKrullDim_le_one_of_curve (k₀ := k₀))

omit [Finite k₀] in
/-- The closed complement of a dense open of a smooth geometrically connected affine curve, as a
finite `k₀`-scheme. -/
lemma exists_isClosedImmersion_isFinite_range_eq_compl
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ C)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsFinite (Z ↘ Spec (CommRingCat.of k₀))), Set.range i.base = (Set.range j.base)ᶜ := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds C)
  have hI : Set.range I.subschemeι.base = (Set.range j.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨I.subschemeι ≫ C ↘ _⟩
  have : I.subschemeι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hfin : Finite I.subscheme := by
    have := (finite_compl_range_of_isDominant (k₀ := k₀) j).to_subtype
    rw [← hI] at this
    exact Finite.of_equiv _ (Equiv.ofInjective _ I.subschemeι.isClosedEmbedding.injective).symm
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    show LocallyOfFiniteType (I.subschemeι ≫ C ↘ _) from inferInstance
  have : LocallyQuasiFinite (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  refine ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, inferInstance,
    IsFinite.of_locallyQuasiFinite _, hI⟩

end Complement

section Boundary

omit [Finite k₀] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] in
/-- A nonempty smooth affine curve `C` over a field is not closed in a proper scheme `Z`
containing it as an open: otherwise `C` would be proper and affine, hence of dimension zero. -/
lemma not_isClosed_range_of_isProper {K : Type u} [Field K] {C Z : Scheme.{u}} (i : C ⟶ Z)
    [IsOpenImmersion i] (g : Z ⟶ Spec (.of K)) [IsProper g]
    [SmoothOfRelativeDimension 1 (i ≫ g)] [IsAffine C] [Nonempty C] :
    ¬ IsClosed (Set.range i) := by
  intro h
  have : IsClosedImmersion i := .of_isPreimmersion i h
  have h1 := (isFinite_of_isProper_of_isAffine (i ≫ g)).2
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (i ≫ g) 1] at h1
  norm_num at h1

omit [Finite k₀] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] in
/-- Let `U ⊆ C ⊆ Z` be opens with `U` nonempty, `C` irreducible and not closed in `Z`. Then
every point of `U` generizes to a point (the generic point of `C`) specializing in `Z` to a
point outside `C`. -/
lemma exists_specializes_notMem_range {U C Z : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    [Nonempty U] [IrreducibleSpace C] (i : C ⟶ Z) (hi : ¬ IsClosed (Set.range i)) (y : U) :
    ∃ y' : U, y' ⤳ y ∧ ∃ x : Z, x ∉ Set.range i ∧ i (j y') ⤳ x := by
  have hη := genericPoint_spec C
  obtain ⟨y', hy'⟩ : genericPoint C ∈ Set.range j :=
    (hη.mem_open_set_iff j.isOpenEmbedding.isOpen_range).2
      ⟨j (Classical.arbitrary U), trivial, Set.mem_range_self _⟩
  refine ⟨y', j.isOpenEmbedding.isInducing.specializes_iff.1 (hy' ▸ hη.specializes trivial), ?_⟩
  have hsub : closure (Set.range i) ⊆ closure {i (j y')} := by
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨c, rfl⟩
    rw [← specializes_iff_mem_closure, hy']
    exact (hη.specializes trivial).map i.continuous
  obtain ⟨x, hx, hxi⟩ := Set.not_subset.1 fun h ↦ hi (closure_subset_iff_isClosed.1 h)
  exact ⟨x, hxi, specializes_iff_mem_closure.2 (hsub hx)⟩

end Boundary


section Localization

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j] [QuasiCompact j] in
lemma over_eq_comp : U ↘ Spec (CommRingCat.of k₀) = j ≫ C ↘ Spec (CommRingCat.of k₀) :=
  (comp_over j _).symm

omit [Finite k₀] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] in
include j in
lemma isSeparated_over_of_isOpenImmersion : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := by
  rw [over_eq_comp j]
  infer_instance

omit [Finite k₀] [IsAffine C] [QuasiCompact j] in
include j in
lemma locallyOfFiniteType_over_of_isOpenImmersion :
    LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
  rw [over_eq_comp j]
  infer_instance

omit [Finite k₀] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j] in
include j in
lemma quasiCompact_over_of_isOpenImmersion : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
  rw [over_eq_comp j]
  infer_instance

variable [IsDominant j] [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

-- the cohomology of the three terms of the triangle unfolds through the Weil structures
/-- *Localization in high degrees.* For a dense open immersion `j : U₀ ↪ C₀` into a smooth
geometrically connected affine curve and a Weil sheaf `F` on `U₀`, the boundary triangle
`RΓ_c(U, F) → RΓ_c(C, j_*F) → RΓ_c(Z, i^*j_*F) →`, whose third term is concentrated in degree
zero, gives Frobenius-equivariant isomorphisms `H_c^r(U, F) ≃ H_c^r(C, j_*F)` for `r ≥ 2`. -/
theorem nonempty_equiv_compactlySupportedCohomology_directImage_of_two_le
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] {r : ℤ} (hr : 2 ≤ r) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r)) := by
  obtain ⟨Z, _, i, _, _, _, hij⟩ := exists_isClosedImmersion_isFinite_range_eq_compl (k₀ := k₀) j
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  set A := (WeilSheaf.directImage j).obj F
  set B := (WeilSheaf.upperStar i).obj A
  obtain ⟨α, β, γ, hT⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed j i
    hij
    (WeilSheaf.toComplex.obj A)
  set T := Triangle.mk α β γ
  have hA : A = (WeilSheaf.lowerStar j).obj F := rfl
  let eU : (WeilComplex.upperStar j).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj F :=
    (WeilSheaf.toComplexCompUpperStarIso j).app A ≪≫
      WeilSheaf.toComplex.mapIso (hA ▸ WeilSheaf.upperStarDirectImageIso j F)
  let eZ : (WeilComplex.upperStar i).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj B :=
    (WeilSheaf.toComplexCompUpperStarIso i).app A
  let EU (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).mapIso eU) r
  let EZ (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).mapIso eZ) r
  -- the boundary has no cohomology outside degree `0`
  have hZ (r : ℤ) (hr : r ≠ 0) : Subsingleton (T.obj₃.cohomologyFrobeniusModule r).carrier := by
    have h := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite B hr
    exact ⟨fun a b ↦ (EZ r).toLinearEquiv.injective (h.elim _ _)⟩
  have hinj : Function.Injective (WeilComplex.cohomologyMap T.mor₁ r) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hZ (r - 1) (by omega)
    obtain ⟨y, rfl⟩ := (WeilComplex.exact_cohomologyδ_right T (r - 1) r (by omega) hT x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (WeilComplex.cohomologyMap T.mor₁ r) := by
    intro z
    have := hZ r (by omega)
    exact (WeilComplex.exact_cohomologyMap T r hT z).1 (Subsingleton.elim _ _)
  let E : (T.obj₁.cohomologyFrobeniusModule r).Equiv (T.obj₂.cohomologyFrobeniusModule r) :=
    ⟨LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩, WeilComplex.cohomologyMap_frobenius T.mor₁ r⟩
  exact ⟨(EU r).symm.trans E⟩

end Localization

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`: in negative degrees because `j_*F` is a sheaf, and in degrees
above two because the boundary triangle identifies `H_c^r(C, j_*F)` with `H_c^r(U, F)` for
`r ≥ 2` (`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_of_two_le`),
which vanishes for `r > 2` by Poincaré duality for the lisse sheaf `F` on the smooth curve `U₀`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse`). -/
theorem subsingleton_compactlySupportedCohomology_directImage (hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier := by
  rcases hr with hr | hr
  · exact WeilSheaf.subsingleton_globalSections_of_isZero
      (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg _ hr)
  · have := isSeparated_over_of_isOpenImmersion (k₀ := k₀) j
    have := locallyOfFiniteType_over_of_isOpenImmersion (k₀ := k₀) j
    have := quasiCompact_over_of_isOpenImmersion (k₀ := k₀) j
    have : SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀)) := by
      rw [over_eq_comp j]
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
    obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_of_two_le j F hr.le
    have := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse hF hr
    exact e.toLinearEquiv.toEquiv.symm.subsingleton

/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.

Concretely, for a compactification `C ⟶[i] Z ⟶ Spec k₀`, `H_c^0(C, j_*F) = Γ(Z̄, ī_! j̄_* F)`
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_forall_eq_zero`).
Such a section vanishes near the boundary `Z̄ \ C̄`, which is in the closure of the generic point
of the irreducible curve `C̄` since `C̄` is affine and not finite; as `F` is lisse, it vanishes
(`AlgebraicGeometry.ProEtale.eq_zero_of_forall_specializes_notMem_range`). -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier := by
  have := nonempty_of_isDominant (k₀ := k₀) j
  have : Nonempty (U ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    Scheme.Hom.nonempty_geometricFiber k₀ U
  let jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have : Nonempty (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    ⟨jb (Classical.arbitrary _)⟩
  -- the geometric fiber `C̄` is a smooth affine curve over `k̄`, irreducible being connected
  let q := (C ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : SmoothOfRelativeDimension 1 q :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.snd _ _))
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsRegular (C ↘ Spec (CommRingCat.of k₀)).geometricFiber := IsRegular.of_smooth q
  have : ConnectedSpace (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := C ↘ Spec (CommRingCat.of k₀)))
      _ _
  have : IrreducibleSpace (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    IsRegular.irreducibleSpace _
  have : IsAffine (C ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    have : IsAffineHom q := MorphismProperty.pullback_snd _ _ inferInstance
    isAffine_of_isAffineHom q
  refine WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_forall_eq_zero _
    fun c β ↦ ?_
  let i := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  have : IsProper (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    MorphismProperty.pullback_snd _ _
      (inferInstanceAs (IsProper (c.g ≫ Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))))
  have : SmoothOfRelativeDimension 1
      (i ≫ (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) := by
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
    infer_instance
  exact ProEtale.eq_zero_of_forall_specializes_notMem_range i jb hF β
    (exists_specializes_notMem_range jb i (not_isClosed_range_of_isProper i
      (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure))

/--
In degree two, the boundary localization sequence identifies `H_c^2(C, j_*F)` with
`H_c^2(U, F)`, which global Verdier duality on the smooth nonproper curve `U` identifies with the
geometric coinvariants `V_{π₁(U)}` of `F`, Tate-twisted by `(-1)`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`): the Frobenius
of the cohomology is `q` times the Frobenius of the coinvariants.

```
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
        │                 │
   Frob │                 │ q · Frob
        ▼                 ▼
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
```
-/
theorem nonempty_equiv_compactlySupportedCohomology_directImage_two
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) :
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  have := isSeparated_over_of_isOpenImmersion (k₀ := k₀) j
  have := isAffine_of_isDominant (k₀ := k₀) j
  have := nonempty_of_isDominant (k₀ := k₀) j
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [over_eq_comp j]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have : GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [over_eq_comp j]
    have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    have : GeometricallyIrreducible (C ↘ Spec (CommRingCat.of k₀)) :=
      .of_smooth_of_geometricallyConnected _
    have : Surjective (j ≫ C ↘ Spec (CommRingCat.of k₀)) :=
      ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
    infer_instance
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_of_two_le j F le_rfl
  obtain ⟨e'⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two F hF
  exact ⟨e.symm.trans e'⟩

/-- If `F` is moreover punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of
weight `w + 2`: the geometric coinvariants are pure of weight `w`
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`) and the Tate twist of
`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two` raises weights
by two. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι (w + 2) := by
  have := locallyOfFiniteType_over_of_isOpenImmersion (k₀ := k₀) j
  have := quasiCompact_over_of_isOpenImmersion (k₀ := k₀) j
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF
  have h := (WeilSheaf.isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist
    Nat.card_pos (-1)
  have hw2 : w - 2 * ((-1 : ℤ) : ℝ) = w + 2 := by push_cast; ring
  rw [hw2] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end AlgebraicGeometry
