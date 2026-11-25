/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UnitForget
public import WeilConjectures.SixFunctors.ProEtale.Adic.AffineLineLisse

/-!
# Homotopy invariance for Weil complexes with lisse cohomology

Let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle over a `k₀`-scheme `X` of finite type,
given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. This file proves that the unit
`K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism for every Weil complex `K` whose cohomology
sheaves are lisse (`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isLisse_homologySheaf`), from
the case of a lisse Weil sheaf placed in degree zero
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_toComplex_of_isLisse`), by dévissage along the
truncation triangles: the objects at which the unit of `π^* ⊣ Rπ_*` is invertible form a
triangulated subcategory (`CategoryTheory.Adjunction.isTriangulated_isoLocus_unit`).

The case of a lisse Weil sheaf is the `ℓ`-adic Weil form of the acyclicity of the affine line.
Forgetting the Weil structures reflects isomorphisms and carries the unit to the unit of the
geometric fibre `π̄ : Ȳ ⟶ X̄`
(`AlgebraicGeometry.NativeBaseChange.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isIso`),
which is the affine line over `X̄`
(`AlgebraicGeometry.WeilComplex.exists_iso_affineSpace_geometricFiber_of_isPullback`); there the
unit is invertible at lisse sheaves
(`AlgebraicGeometry.ProEtale.isIso_adicUnit_app_singleFunctor_of_isAdicLisseSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The unit of the Weil adjunction `φ^* ⊣ Rφ_*` at a Weil complex `K` is an isomorphism if and
only if the unit of the derived adjunction on pro-étale Weil sheaves is one at `K`. -/
lemma isIso_upperStarDerivedLowerStarAdjunction_unit_app_iff {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app K) ↔
      IsIso ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l φ).unit.app K.obj) := by
  rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _), upperStarDerivedLowerStarAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

omit [Finite k₀] [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] in
include hπ in
/-- The base change `π̄ : Ȳ ⟶ X̄` of the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` to the
algebraic closure of `k₀` is the affine line over the geometric fibre `X̄`: there is an
isomorphism `Ȳ ≅ 𝔸¹_X̄` over `X̄`. Both are base changes of `𝔸¹_{k₀} ⟶ Spec k₀` along
`X̄ ⟶ X ⟶ Spec k₀`. -/
lemma exists_iso_affineSpace_geometricFiber_of_isPullback :
    ∃ e : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      𝔸(ULift.{u} (Fin 1); (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      e.hom ≫ (𝔸(ULift.{u} (Fin 1); (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ↘
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) = NativeBaseChange.geometricMap k₀ π := by
  have h₁ := (Scheme.Hom.isPullback_geometricFiberMap π
    (comp_over π (Spec (CommRingCat.of k₀)))).paste_vert hπ
  have h₂ := (AffineSpace.isPullback_map (n := PUnit.{u + 1})
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ X ↘ Spec (CommRingCat.of k₀))).flip
  refine ⟨h₁.isoIsPullback _ _ h₂ ≪≫ AffineSpace.reindexIso _
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u + 1}), ?_⟩
  simp [NativeBaseChange.geometricMap]

set_option linter.unusedSectionVars false in
include hπ in
/-- Blueprint `lem-pur-a1-direct-image` (for lisse Weil sheaves): **homotopy invariance for lisse
Weil sheaves**. For the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` and a lisse Weil sheaf
`L` on `X`, the unit `L ⟶ Rπ_* π^* L` of `π^* ⊣ Rπ_*` is an isomorphism.

Forgetting the Weil structures reflects isomorphisms and carries the unit to the unit of the
derived adjunction `π̄^* ⊣ Rπ̄_*` of `ℓ`-adic sheaves on the geometric fibres
(`AlgebraicGeometry.NativeBaseChange.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isIso`).
The base change `π̄` is the affine line over `X̄`
(`AlgebraicGeometry.WeilComplex.exists_iso_affineSpace_geometricFiber_of_isPullback`), and the
underlying `ℓ`-adic sheaf of `L` is lisse, so this is homotopy invariance for lisse `ℓ`-adic
sheaves over the algebraically closed field `k̄`
(`AlgebraicGeometry.ProEtale.isIso_adicUnit_app_singleFunctor_of_isAdicLisseSheaf`). -/
theorem isIso_unit_app_toComplex_of_isLisse (L : WeilSheaf k₀ l X) (hL : L.IsLisse) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app
      (WeilSheaf.toComplex.obj L)) := by
  rw [isIso_upperStarDerivedLowerStarAdjunction_unit_app_iff]
  refine NativeBaseChange.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isIso k₀ l π _ ?_
  obtain ⟨e, he⟩ := exists_iso_affineSpace_geometricFiber_of_isPullback π s hπ
  have hl : IsUnit ((l : ℕ) : AlgebraicClosure k₀) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k₀ ≠ l) ?_
    rw [Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
    have : (ringChar (AlgebraicClosure k₀)).Prime := by
      rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
      exact CharP.prime_ringChar k₀
    exact (Nat.prime_dvd_prime_iff_eq this Fact.out).1 ((ringChar.spec _ l).1 h)
  have h := ProEtale.isIso_adicUnit_app_singleFunctor_of_isAdicLisseSheaf hl
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _ e he hL
  exact (NatTrans.isIso_app_iff_of_iso _
    (((Endofunctor.IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app L.obj)).2 h

include hπ in
/-- **Homotopy invariance for Weil complexes with lisse cohomology.** For the trivial line bundle
`π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` and a Weil complex `K` on `X` whose cohomology sheaves are lisse, the
unit `K ⟶ Rπ_* π^* K` is an isomorphism. By dévissage along the truncation triangles, this
reduces to lisse Weil sheaves placed in degree zero
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_toComplex_of_isLisse`). -/
theorem isIso_unit_app_of_isLisse_homologySheaf (K : WeilComplex k₀ l X)
    (hK : ∀ n : ℤ, ((homologySheaf n).obj K).IsLisse) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) := by
  let P : ObjectProperty (ProEtaleWeilSheaf k₀ l X) :=
    fun F ↦ ∃ h : WeilSheaf.objectProperty k₀ l X F, WeilSheaf.IsLisse ⟨F, h⟩
  have : P.IsClosedUnderIsomorphisms := ⟨fun e ⟨h, hL⟩ ↦
    ⟨(WeilSheaf.objectProperty k₀ l X).prop_of_iso e h,
      ProEtale.IsAdicLisseSheaf.of_iso ((Endofunctor.IsoAlgebra.forget _).mapIso e) hL⟩⟩
  rw [isIso_upperStarDerivedLowerStarAdjunction_unit_app_iff]
  refine _root_.DerivedCategory.prop_of_bounded
    (Q := (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l π).unit.isoLocus)
    P (fun F ⟨h, hL⟩ ↦ ?_) K.obj K.property.1
    fun n ↦ ⟨K.property.2 n, hK n⟩
  have := isIso_unit_app_toComplex_of_isLisse π s hπ ⟨F, h⟩ hL
  rwa [isIso_upperStarDerivedLowerStarAdjunction_unit_app_iff] at this

end AlgebraicGeometry.WeilComplex
