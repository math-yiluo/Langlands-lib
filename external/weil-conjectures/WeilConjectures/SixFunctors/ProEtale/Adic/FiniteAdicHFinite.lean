/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CompositionPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius

/-!
# Finiteness of `Hⁿ(S_proét, ℤ/ℓᵐ)` over a separably closed field

Let `k` be a separably closed field in which `ℓ` is invertible and `S` a separated `k`-scheme of
finite type. The cohomology groups `Hⁿ(S, ℤ/ℓᵐ)` are finite
(`AlgebraicGeometry.ProEtale.finite_finiteAdicH`): through the comparison
`Hⁿ(S_proét, ℤ/ℓᵐ) ≅ Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n])`, `Λ = ℤ/ℓᵐ`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), they are the cohomology groups of
`RΓ(S, Λ)`, a perfect complex of `Λ`-modules
(`AlgebraicGeometry.Etale.isPerfect_rightDerivedGlobalSections`, blueprint
`lemma-perfect-complexes-geometric-point`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [IsSepClosed k] {S : Scheme.{u}}
  (a : S ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
  [CompactSpace S] [QuasiSeparatedSpace S]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
include a in
/-- The classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`, form a finite group, for `S`
separated of finite type over a separably closed field in which `ℓ` is invertible. -/
theorem finite_unitShift (hl : (l : k) ≠ 0) (m : ℕ) (n : ℤ) :
    Finite (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦n⟧) := by
  let Λ := ULift.{u + 1} (ZMod (l ^ m))
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨l ^ m, Nat.pos_of_ne_zero (NeZero.ne _), ULift.ext (by simp [Λ]), by
      simpa using ((Ne.isUnit (pow_ne_zero m hl)).map (Scheme.ΓSpecIso (.of k)).inv.hom)⟩
  have hK : Etale.DerivedCategory.boundedConstructibleFiniteTor Λ S
      (𝟙_ (Etale.DerivedCategoryModule Λ S)) :=
    ⟨(Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S).prop_of_iso
        (Etale.constantComplexIsoSingleFunctor Λ S).symm
        (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
      (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) S).prop_of_iso
        (Etale.constantComplexIsoSingleFunctor Λ S).symm
        ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_tensorIso (λ_ _))⟩⟩
  have hP := Etale.isPerfect_rightDerivedGlobalSections Λ a _ hK
  let RΓ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let C := (Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctor.obj
    (𝟙_ (Etale.DerivedCategoryModule Λ S))
  let H0 := _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0
  let e : H0.obj (RΓ.obj (C⟦n⟧)) ≅
      (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).obj
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) S).obj
          (𝟙_ (Etale.DerivedCategoryModule Λ S))) :=
    H0.mapIso ((RΓ.commShiftIso n).app C) ≪≫ (H0.shiftIso n 0 n (by simp)).app _ ≪≫
      (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).mapIso
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _)
  have := hP.finite_homology n
  have : Module.Finite Λ (H0.obj (RΓ.obj (C⟦n⟧))) := Module.Finite.equiv e.toLinearEquiv.symm
  have : Finite (H0.obj (RΓ.obj (C⟦n⟧))) := Module.finite_of_finite Λ
  have : Finite ((_root_.DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ) ⟶
      RΓ.obj (C⟦n⟧)) :=
    Finite.of_equiv _ (_root_.DerivedCategory.homSingleRingEquiv _).symm
  have : Finite (𝟙_ (Etale.DerivedCategoryModule Λ (Spec (.of k))) ⟶ C⟦n⟧) :=
    RΓ.finite_hom_of_fullyFaithful (Etale.rightDerivedGlobalSectionsUnitIso Λ k) (Iso.refl _)
  let adj := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a
  let eU := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a
  exact Finite.of_equiv (𝟙_ (Etale.DerivedCategoryModule Λ (Spec (.of k))) ⟶ C⟦n⟧)
    ((Iso.homCongr (Iso.refl _)
      (((Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctor.commShiftIso n).app
        (𝟙_ (Etale.DerivedCategoryModule Λ S)))).symm.trans
      ((adj.homEquiv _ _).symm.trans (eU.homCongr (Iso.refl _))))

include a in
/-- **Finiteness of `Hⁿ(S, ℤ/ℓᵐ)`**, for `S` separated of finite type over a separably closed
field in which `ℓ` is invertible. -/
theorem finite_finiteAdicH (hl : (l : k) ≠ 0) (m n : ℕ) : Finite (FiniteAdicH S l m n) :=
  have := finite_unitShift l a hl m n
  Finite.of_equiv _ (unitShiftAddEquivFiniteAdicH l m S n).toEquiv

end AlgebraicGeometry.ProEtale
