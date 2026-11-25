/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityCondensedCarrier

/-!
# Universality of the geometric carrier of a descended proper trace

The descent comparison identifies this carrier with ordinary proper base
change. Thus invertibility of exceptional base change proves its universal
property on bounded constructible geometric complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The universal property of a trace, with the hom-map formed over abstract categories. -/
def Functor.TraceUniversalAt {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    (K : C) {P : C} {N : D} (τ : L.obj P ⟶ N) : Prop :=
  Function.Bijective fun φ : K ⟶ P ↦ L.map φ ≫ τ

/-- Transfer a universal trace along specified source and target coordinates. -/
lemma Functor.bijective_map_comp_of_trace_coordinates
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {K P P' : C} {N₀ N N' : D} (e : P ≅ P') (e' : N ≅ N')
    (β : L.obj P' ⟶ N₀) (ε : N₀ ⟶ N) (τ : L.obj P ⟶ N')
    (hτ : τ = L.map e.hom ≫ β ≫ ε ≫ e'.hom)
    (h : Function.Bijective fun φ : K ⟶ P' ↦ L.map φ ≫ β ≫ ε) :
    L.TraceUniversalAt K τ := by
  dsimp only [Functor.TraceUniversalAt]
  rw [hτ]
  simpa only [Category.assoc] using Functor.bijective_map_comp_iso_trace L e e' (β ≫ ε) h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Coefficients

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y} {h : f ≫ t = s}
  (hc : UpperStarWeilCompatible Λ f h)
  {P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))}
  {N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj Λ Y))}
  (ε : (lowerStar Λ f).rightDerivedFunctor.obj P ⟶ N)

/-- Descent preserves geometric universality in arbitrary coefficient coordinates. -/
theorem geometricFiberWeilDirectTrace_universal
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u + 1})
      (condensedRingObj Λ s.geometricFiber)))
    (hε : Function.Bijective fun φ : K ⟶
        (upperStar Λ s.geometricFiberProj).mapDerivedCategory.obj P ↦
      (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor.map φ ≫
        (rightDerivedLowerStarBaseChangeIso Λ
          (Scheme.Hom.isPullback_geometricFiberMap f h).flip).inv.app P ≫
        (upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε) :
    (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor.TraceUniversalAt K
      ((Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
        (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)).inv.app
          ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ≫
        (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
          (geometricFiberWeilDirectTrace Λ hc ε)) := by
  exact Functor.bijective_map_comp_of_trace_coordinates
    (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor
    ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.forget _)).app P)
    ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
      (Endofunctor.IsoAlgebra.forget _)).symm.app N)
    ((rightDerivedLowerStarBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap f h).flip).inv.app P)
    ((upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε) _
    (geometricFiberWeilDirectTrace_forget Λ hc ε) hε

end Coefficients

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left]

local instance instFactPrimeRingCharAlgebraicClosure_smoothPurityDescendedProperUniversality
    : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance instFactNeNatRingCharAlgebraicClosure_smoothPurityDescendedProperUniversality
    : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

/-- The geometric fibre of an arrow, viewed over the algebraic closure. -/
noncomputable abbrev traceGeometricFiberOverMap :
    Over.mk X.hom.geometricFiberToAlgebraicClosure ⟶
      Over.mk Y.hom.geometricFiberToAlgebraicClosure :=
  Over.homMk (Scheme.Hom.geometricFiberMap f.left (Over.w f)) (by
    simp [Scheme.Hom.geometricFiberToAlgebraicClosure, Scheme.Hom.geometricFiberMap])

local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedProperUniversality
    : LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedProperUniversality
    : QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedProperUniversality
    : IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedProperUniversality_2
    : LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedProperUniversality_2
    : QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedProperUniversality_2
    : IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : IsProper (traceGeometricFiberOverMap f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f.left (Over.w f) inferInstance

variable (hc : UpperStarWeilCompatible (Profinite.padicAlgClRingObj l) f.left (Over.w f))
  {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶ (boundedConstructibleUpperShriek l f).obj N)

/-- The actual descended trace is geometrically universal when the exceptional
base-change component is invertible. -/
theorem bijective_map_comp_geometricFiberWeilDirectTrace_of_isIso [IsIso γ]
    [IsIso ((upperShriekBaseChangeOfMap l (f := f) (f' := traceGeometricFiberOverMap f)
      (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip).app N)]
    (K : Dᵇc(X.hom.geometricFiber)⟦Profinite.padicAlgClRingObj l⟧) :
    (lowerStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap f.left (Over.w f))).rightDerivedFunctor.TraceUniversalAt K.obj
      ((Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
        (lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
          f.left (Over.w f))).inv.app
            ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
              X.hom).mapDerivedCategory.obj
              P.obj) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        (geometricFiberWeilDirectTrace (Profinite.padicAlgClRingObj l) hc
          (((boundedConstructibleLowerStar l f).map γ ≫
            (lowerStarUpperShriekAdjunction l f).counit.app N).hom))) := by
  apply geometricFiberWeilDirectTrace_universal (Profinite.padicAlgClRingObj l) hc
  exact bijective_map_comp_properTrace_levelwise_of_isIso l f
    (traceGeometricFiberOverMap f)
    (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip γ K

/-- The actual descended trace is geometrically universal for a smooth proper map. -/
theorem bijective_map_comp_geometricFiberWeilDirectTrace [IsIso γ]
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : Dᵇc(X.hom.geometricFiber)⟦Profinite.padicAlgClRingObj l⟧) :
    (lowerStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap f.left (Over.w f))).rightDerivedFunctor.TraceUniversalAt K.obj
      ((Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
        (lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
          f.left (Over.w f))).inv.app
            ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
              X.hom).mapDerivedCategory.obj
              P.obj) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        (geometricFiberWeilDirectTrace (Profinite.padicAlgClRingObj l) hc
          (((boundedConstructibleLowerStar l f).map γ ≫
            (lowerStarUpperShriekAdjunction l f).counit.app N).hom))) := by
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l
    (f := f) (f' := traceGeometricFiberOverMap f) d
    (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip N
  exact bijective_map_comp_geometricFiberWeilDirectTrace_of_isIso l f hc γ K

end AlgebraicGeometry.ProEtale.CondensedRing
