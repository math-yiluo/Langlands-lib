/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurity
public import WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
public import WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTrace
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTraceCriterion
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-!
# The Weil orientation from the descended finite-field trace (sorry ①, sub-problem A1+A2)

Let `f : X ⟶ Y` be smooth separated of pure relative dimension `d` over the finite field `k₀`.
The target `WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
asks for an isomorphism `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of underlying complexes on the geometric fibre
`X̄` which commutes with the Frobenius structures. By the reductions R1/R2 it is enough to produce
an orientation `o : f̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` whose trace `f̄_! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` is Frobenius
equivariant.

## The route: descend the trace from `k₀` (A2) and test it geometrically (A1')

* **A2 (Frobenius stability).** The smooth trace `Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` exists over
  the finite field `k₀` itself (`AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace`, smooth
  purity holds over any field of characteristic `p ≠ ℓ`). Its pullback to the geometric fibre is a
  morphism of *Weil* complexes `descendedSmoothTrace : Rf₀! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ`
  (K4's `traceOfDescendedSmoothTrace`, through the condensed descent
  `geometricFiberWeilSmoothTrace`), because the geometric Frobenius of `X̄ = X ×_{k₀} k̄` lies
  over `X`. Hence its underlying trace is automatically Frobenius equivariant
  (naturality of `Endofunctor.IsoAlgebra.derivedStrIso`): no normalization is needed for
  equivariance. This is the
  precise content of "integration on `𝔸¹` is defined over `k₀`".
* **A1' (universality).** What remains is that the descended trace is *universal*, i.e. its
  transpose `ℚ̄_ℓ(d)[2d] ⟶ f̄^! ℚ̄_ℓ` on `X̄` is an isomorphism: the hypothesis
  `DescendedSmoothTraceUniversal`. Mathematically this is the compatibility of `Rf^!` with the
  change of base field `k₀ ⟶ k̄` for the *non-proper* smooth `f` (the exceptional base change map
  of the compact-support adjunction is an isomorphism at `ℚ̄_ℓ`). The library proves it for
  smooth *proper* `f` along weakly étale base change
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale`) and
  for arbitrary proper `f` over a point (`isIso_upperShriekBaseChangeOfMap_app_unit_point`); the
  non-proper smooth relative case is open. Through K4's free Weil resolution criterion
  (`isIso_homEquiv_of_geometric_trace`) it lifts to invertibility of the native transpose.
* **A3 (Tate datum).** The source of the descended trace is the descent of the root-defined Tate
  line; its identification with the native cyclotomic Tate twist is the sheaf-level encoding
  `α` (`WeilSheaf.purity_nonempty_toCondensedTateDescentIso`, kernel-cost only, handled
  separately). It enters only through `finiteBaseNativeDescentTateIso`.

The main results are
`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_descendedTrace`
(the Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` as an isomorphism of Weil complexes) and
`WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_descendedTrace`
(the statement of sorry ①), both from `α` and `DescendedSmoothTraceUniversal`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance instFactPrimeRingChar_smoothPurityDescendedTraceEquivariance
    : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩

variable {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ)

local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedTraceEquivariance
    : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedTraceEquivariance
    : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedTraceEquivariance
    : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance instLocallyOfFiniteType_weilSheafSmoothPurityDescendedTraceEquivariance_2
    : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance instQuasiCompactHomScheme_weilSheafSmoothPurityDescendedTraceEquivariance_2
    : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance instIsSeparatedHomScheme_weilSheafSmoothPurityDescendedTraceEquivariance_2
    : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

/-- The native Tate line `ℚ̄_ℓ,X(d)[2d]` as a Weil complex (the target of the orientation in
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`). -/
noncomputable abbrev purityTateShift : WeilComplex k₀ l X :=
  ((tateTwist k₀ l X d).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧

/-- The sheaf-level Tate encoding (A3): the native cyclotomic Tate sheaf is descent of the
finite-base root-defined Tate sheaf. Provided by
`WeilSheaf.purity_nonempty_toCondensedTateDescentIso`. -/
abbrev TateEncoding :=
  (ProEtaleWeilSheaf.toCondensed k₀ l X).obj (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d)

variable {d} (α : TateEncoding (k₀ := k₀) (l := l) (X := X) d)

/-- Native descent of the finite-base Tate line is the native Tate line, given the encoding. -/
noncomputable def descendedTateIso :
    (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)) ≅
      purityTateShift (k₀ := k₀) (l := l) (X := X) d :=
  finiteBaseNativeDescentTateIso d (2 * d) α ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso (tateTwistConstantSingleIso d).symm

/-- The condensed realization of the native Tate line is condensed descent of the finite-base
Tate line: the source identification of the descended trace. -/
noncomputable def descendedTateSourceIso :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj
        (purityTateShift (k₀ := k₀) (l := l) (X := X) d).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
          (CondensedRing.boundedConstructibleTateTwist l
            (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)).obj :=
  (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.mapIso
      ((objectProperty k₀ l X).ι.mapIso (descendedTateIso α).symm) ≪≫
    (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := X)).app
      (CondensedRing.boundedConstructibleTateTwist l
        (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d))

/-- The condensed realization of the constant Weil complex is condensed descent of the
finite-base unit: the target identification of the descended trace. -/
noncomputable def descendedUnitTargetIso :
    (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj (𝟙_ _) :=
  letI : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)).IsMonoidal :=
    CondensedRing.isMonoidal_boundedConstructible l (Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
  letI := ObjectProperty.fullMonoidalSubcategory
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y))
  (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.mapIso
      ((objectProperty k₀ l Y).ι.mapIso
        (finiteBaseNativeDescentUnitIso (k₀ := k₀) (l := l) (X := Y)).symm) ≪≫
    (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := Y)).app (𝟙_ _)

/-- **A2: the descended smooth trace.** The finite-field smooth trace
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y`, pulled back to the geometric fibre as a morphism of Weil
complexes `Rf₀! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ`. Its underlying geometric trace is Frobenius equivariant
because it is a morphism of Weil complexes (naturality of
`Endofunctor.IsoAlgebra.derivedStrIso`). -/
noncomputable def descendedSmoothTrace :
    (derivedLowerShriek k₀ l f).obj (purityTateShift (k₀ := k₀) (l := l) (X := X) d) ⟶
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y) :=
  traceOfDescendedSmoothTrace f d (purityTateShift (k₀ := k₀) (l := l) (X := X) d)
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))
    (descendedTateSourceIso α) (descendedUnitTargetIso (k₀ := k₀) (l := l) (Y := Y))

/-- **A1' (universality of the descended trace).** The underlying geometric trace
`f̄_! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` on the geometric fibre is universal: composing with it identifies
`Hom(K[n], ℚ̄_ℓ(d)[2d])` with `Hom(f̄_! K[n], ℚ̄_ℓ)` for every bounded constructible `K`.
Equivalently, its transpose `ℚ̄_ℓ(d)[2d] ⟶ f̄^! ℚ̄_ℓ` is an isomorphism: this is the
compatibility of `Rf^!` with the base change `k₀ ⟶ k̄` for the non-proper smooth `f`
(blueprint `proposition-compatibility-purity-base-change` across the field extension). -/
def DescendedSmoothTraceUniversal : Prop :=
  ∀ (K : WeilComplex k₀ l X) (n : ℤ), Function.Bijective
    fun φ : (shiftFunctor _ n).obj (forget.obj K) ⟶
        forget.obj (purityTateShift (k₀ := k₀) (l := l) (X := X) d) ↦
      (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f
        (lowerShriekCompactification k₀ f)).map φ ≫
      (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
        (lowerShriekCompactification k₀ f)).inv.app
          (purityTateShift (k₀ := k₀) (l := l) (X := X) d).obj ≫
      forget.map (descendedSmoothTrace f α)

variable [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The transpose of the descended trace under `Rf₀! ⊣ Rf^!` is invertible once the trace is
geometrically universal (free Weil resolution, `isIso_homEquiv_of_geometric_trace`). -/
theorem isIso_homEquiv_descendedSmoothTrace (h : DescendedSmoothTraceUniversal f α)
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J) :
    IsIso (adj.homEquiv _ _ (descendedSmoothTrace f α)) :=
  isIso_homEquiv_of_geometric_trace f adj (descendedSmoothTrace f α) h

/-- **The Weil orientation of a smooth morphism from the descended trace**: for any right
adjoint `J` of `Rf₀!`, `J ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` as Weil complexes. -/
theorem nonempty_rightAdjoint_obj_adicConstant_iso_of_descendedTrace
    (h : DescendedSmoothTraceUniversal f α)
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J) :
    Nonempty (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      purityTateShift (k₀ := k₀) (l := l) (X := X) d) :=
  have := isIso_homEquiv_descendedSmoothTrace f α h adj
  ⟨(asIso (adj.homEquiv _ _ (descendedSmoothTrace f α))).symm⟩

variable [HasUpperShriek k₀ l f]

/-- The Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of Weil complexes
(`nonempty_upperShriek_obj_adicConstant_iso_of_smooth`), from the Tate encoding and the
universality of the descended trace. -/
theorem nonempty_upperShriek_obj_adicConstant_iso_of_descendedTrace
    (h : DescendedSmoothTraceUniversal f α) :
    Nonempty ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) :=
  nonempty_rightAdjoint_obj_adicConstant_iso_of_descendedTrace f α h
    (derivedLowerShriekUpperShriekAdjunction f)

/-- **Sorry ① from the descended trace**: the statement of
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`, from the Tate encoding `α` (A3)
and the universality of the descended trace (A1'). The equivariance (A2) is automatic: the
orientation is a morphism of Weil complexes. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_descendedTrace
    (h : DescendedSmoothTraceUniversal f α) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨e⟩ := nonempty_upperShriek_obj_adicConstant_iso_of_descendedTrace f α h
  exact ⟨forget.mapIso e, ((Endofunctor.IsoAlgebra.derivedStrIso _).hom.naturality e.hom.hom).symm⟩

end AlgebraicGeometry.WeilComplex
