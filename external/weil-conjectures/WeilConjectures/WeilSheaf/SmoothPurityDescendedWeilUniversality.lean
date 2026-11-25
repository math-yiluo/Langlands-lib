/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality

/-! # Universality of the finite-base descended trace in the Weil category -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left]

local instance descendedWeilUniversalityInst1 : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance descendedWeilUniversalityInst2 : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

local instance descendedWeilUniversalityInst3 :
    LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance descendedWeilUniversalityInst4 :
    QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance descendedWeilUniversalityInst5 :
    IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance descendedWeilUniversalityInst6 :
    LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance descendedWeilUniversalityInst7 :
    QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance descendedWeilUniversalityInst8 :
    IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance descendedWeilUniversalityInst9 : IsProper (traceGeometricFiberOverMap f).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    f.left (Over.w f) inferInstance

variable (hc : UpperStarWeilCompatible (Profinite.padicAlgClRingObj l) f.left (Over.w f))
  {P : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧}
  {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧}
  (γ : P ⟶ (boundedConstructibleUpperShriek l f).obj N)

/-- The free Weil resolution lifts geometric universality of a descended proper trace. -/
theorem geometricFiberWeilDirectTrace_weilUniversal [IsIso γ]
    [IsIso ((upperShriekBaseChangeOfMap l (f := f) (f' := traceGeometricFiberOverMap f)
      (Scheme.Hom.isPullback_geometricFiberMap f.left (Over.w f)).flip).app N)]
    (K : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar (Profinite.padicAlgClRingObj l) X.hom.geometricGaloisFrobenius.asIso.inv)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      X.hom.geometricFiber) ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K)) :
    (geometricFiberMapWeilLowerStar (Profinite.padicAlgClRingObj l)
      f.left (Over.w f)).rightDerivedFunctor.TraceUniversalAt K
      (geometricFiberWeilDirectTrace (Profinite.padicAlgClRingObj l) hc
        (((boundedConstructibleLowerStar l f).map γ ≫
          (lowerStarUpperShriekAdjunction l f).counit.app N).hom)) := by
  dsimp only [Functor.TraceUniversalAt]
  refine Endofunctor.IsoAlgebra.bijective_map_comp_rightDerived_of_bounded
    (lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
      f.left (Over.w f))
    (condensed_trace_preservesCoproduct (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap f.left (Over.w f))) _ K hK.1 ?_
  intro n
  exact bijective_map_comp_geometricFiberWeilDirectTrace_of_isIso l f hc γ
    ⟨_, ObjectProperty.le_shift (P := boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) X.hom.geometricFiber)) n _ hK⟩

end AlgebraicGeometry.ProEtale.CondensedRing
