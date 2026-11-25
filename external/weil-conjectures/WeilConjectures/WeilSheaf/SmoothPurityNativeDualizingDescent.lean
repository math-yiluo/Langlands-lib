/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeProperDualizing
public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescentPullback

/-!
# Descent of the exceptional unit through a compactification

Proper direct image followed by open restriction describes the exceptional
inverse image. The proper descended trace and the pullback comparison identify
its unit value with native descent of the finite-base dualizing complex.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over
attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

local instance instFactPrimeRingChar_smoothPurityNativeDualizingDescent
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance : (boundedConstructible (condensedRingObj
    (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))).IsMonoidal :=
  CondensedRing.isMonoidal_boundedConstructible l (CondensedRing.point k₀)
noncomputable local instance : MonoidalCategory (BoundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀)))) :=
  ObjectProperty.fullMonoidalSubcategory _
local instance instLocallyOfFiniteType_smoothPurityNativeDualizingDescent
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_smoothPurityNativeDualizingDescent
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_smoothPurityNativeDualizingDescent
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

/-- Open restriction of a descended finite-base dualizing object is the descended
finite-base dualizing object of the open subscheme. -/
noncomputable def nativeOpenDualizingDescentIso
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (i : X ⟶ Z) [i.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion i] :
    (upperStar (k₀ := k₀) (l := l) i).obj
      ((finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := Z)).obj
        (CondensedRing.dualizingComplex l (Over.mk (Z ↘ Spec (CommRingCat.of k₀))))) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
        (CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀)))) := by
  let Z₀ := Over.mk (Z ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType Z₀.hom := ‹LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))›
  have : QuasiCompact Z₀.hom := ‹QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))›
  have : IsSeparated Z₀.hom := ‹IsSeparated (Z ↘ Spec (CommRingCat.of k₀))›
  let j : Over.mk (X ↘ Spec (CommRingCat.of k₀)) ⟶ Z₀ :=
    Over.homMk i (comp_over i (Spec (CommRingCat.of k₀)))
  have : IsOpenImmersion j.left := ‹IsOpenImmersion i›
  let e₀ : (finiteBaseTracePullback (k₀ := k₀) (l := l) i).obj
      (CondensedRing.dualizingComplex l Z₀) ≅
      CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))) :=
    (CondensedRing.dualizingComplexIsoUpperStar l j).symm
  exact finiteBaseNativeDescentUpperStarIso (k₀ := k₀) (l := l) i
    (CondensedRing.dualizingComplex l Z₀) ≪≫
    (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).mapIso e₀

/-- The exceptional inverse image of the descended unit is native descent of the
finite-base dualizing complex, including the Weil structure. -/
theorem nonempty_shriekRightAdjoint_finiteBaseNativeDescent_dualizing_iso
    {R : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ R) :
    Nonempty (R.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)
      (X := Spec (CommRingCat.of k₀))).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
        (CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))))) := by
  let c := structureMorphismCompactification (k₀ := k₀) X
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated (c.Z ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c.g (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k₀)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  have := isLeftAdjoint_derivedLowerStar_of_isProper (k₀ := k₀) (l := l) c.g
  let adjg := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) c.g)
  have e : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
      extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((derivedLowerShriekCompιIso k₀ l c).app K))
      (fun φ ↦ by
        apply (objectProperty k₀ l (Spec (CommRingCat.of k₀))).ι.map_injective
        exact (derivedLowerShriekCompιIso k₀ l c).hom.naturality φ)
  let eR := adj.rightAdjointUniq
    (((extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) c.i).comp adjg).ofNatIsoLeft e.symm)
  obtain ⟨eZ⟩ :=
    nonempty_rightAdjoint_finiteBaseNativeDescent_dualizing_iso (k₀ := k₀) (l := l) c.g adjg
  let b := (upperStar (k₀ := k₀) (l := l) c.i).mapIso eZ
  exact ⟨eR.app _ ≪≫ b ≪≫ nativeOpenDualizingDescentIso (k₀ := k₀) (l := l) c.i⟩

end AlgebraicGeometry.WeilComplex
