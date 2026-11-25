/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData

/-! # Ring stages before localization in exceptional coefficient assembly

This partial datum contains only finite and integral stages. Field-stage operations,
localization comparisons and common-field comparisons are constructed separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

/-- Finite and integral coefficient operations, with the actual scalar restrictions,
proper/open normalized counit mates, and shift-compatible ambient realizations.
There are no rational or closed operations in this datum.
Source: Zheng, Lemma 5.22 and Proposition 5.24; coefficient construction steps 1--4
(blueprint: def-sf-ring-stage-assembly-data). -/
structure RingStageAssembly (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  operation (c : Compactification f) (s : RingStage.{max u v} l) :
    Operation.{u, v} l Ω X Y (s.stage l)
  left (c : Compactification f) (s : RingStage.{max u v} l) :
    LeftRealization.{u, v} l Ω c s (operation c s)
  finiteRight (c : Compactification f) (E : FieldStage.{max u v} l) (n : ℕ+) :
    (operation c (.finite E n)).G ⋙ RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n) ≅
      RingStage.inclusion.{u, v} l Ω Y (RingStage.finite E n) ⋙
        @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) _
          (Padic.finite_coefficientExtensionRing l E.carrier n n.pos) X Y f c
  integralLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  integralLeft_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    ((sfIntegralConstructible l E.carrier Y).ι.map
        ((integralLeft c E).hom.app K)) =
      (left c (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  scalar {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u, v} l Ω a (endpoint X Y side)
  finiteScalar_eq {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u, v} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    CounitComparison.{u, v} l Ω (operation c s) (operation c t)
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    CounitQNormalized.{u, v} l Ω c a (scalar a ha true) (scalar a ha false)
      (left c s) (left c t) (comparison c a ha)
  scalarComposition {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u, v} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  scalarIdentity {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u, v} l Ω h (endpoint X Y side) (scalar a ha side)

  leftShift (c : Compactification f) (s : RingStage.{max u v} l) :
    (left c s).hom.CommShift ℤ

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Adjoin rational and closed operations to the two ring-stage families.
This is a case distinction on the existing stage index, with no choice of data.
Source: the four coefficient stages of the exceptional construction
(blueprint: def-sf-ring-stage-assembly-data). -/
def RingStageAssembly.extendOperation
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (rational : ∀ (_c : Compactification f) (E : FieldStage.{max u v} l),
      Operation.{u, v} l Ω X Y (.rational E))
    (closed : ∀ _c : Compactification f, Operation.{u, v} l Ω X Y .closed)
    (c : Compactification f) (s : Stage.{max u v} l) : Operation.{u, v} l Ω X Y s :=
  match s with
  | .finite E n => A.operation c (.finite E n)
  | .integral E => A.operation c (.integral E)
  | .rational E => rational c E
  | .closed => closed c

/-- Assemble the ring record from its ring-only fields and the supplied field operations.
All scalar functors and mates are reused from the ring datum, and none is chosen again.
Source: coefficient construction steps 1--5
(blueprint: def-sf-ring-stage-assembly-data). -/
def RingStageAssembly.complete
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (rational : ∀ (_c : Compactification f) (E : FieldStage.{max u v} l),
      Operation.{u, v} l Ω X Y (.rational E))
    (closed : ∀ _c : Compactification f, Operation.{u, v} l Ω X Y .closed)
    (rationalLeft : ∀ (c : Compactification f) (E : FieldStage.{max u v} l),
      (rational c E).F ≅
        sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
          c E.carrier) : CoefficientConstructionRing.{u, v} l Ω D hl (f := f) where
  operation := A.extendOperation l Ω D hl rational closed
  left c s := match s with
    | .finite E n => A.left c (.finite E n)
    | .integral E => A.left c (.integral E)
  finiteRight := A.finiteRight
  integralLeft := A.integralLeft
  integralLeft_normalized := A.integralLeft_normalized
  rationalLeft := rationalLeft
  scalar := A.scalar
  finiteScalar_eq := A.finiteScalar_eq
  finiteScalar_normalized := A.finiteScalar_normalized
  integralScalar_eq := A.integralScalar_eq
  integralScalar_normalized := A.integralScalar_normalized
  comparison c {s t} a ha := by
    cases s with
    | finite E n =>
      cases t with
      | finite L m => exact A.comparison c (s := .finite E n) (t := .finite L m) a ha
      | integral L => exact A.comparison c (s := .finite E n) (t := .integral L) a ha
    | integral E =>
      cases t with
      | finite L m => exact A.comparison c (s := .integral E) (t := .finite L m) a ha
      | integral L => exact A.comparison c (s := .integral E) (t := .integral L) a ha
  comparison_normalized c {s t} a ha := by
    cases s with
    | finite E n =>
      cases t with
      | finite L m =>
        exact A.comparison_normalized c (s := .finite E n) (t := .finite L m) a ha
      | integral L =>
        exact A.comparison_normalized c (s := .finite E n) (t := .integral L) a ha
    | integral E =>
      cases t with
      | finite L m =>
        exact A.comparison_normalized c (s := .integral E) (t := .finite L m) a ha
      | integral L =>
        exact A.comparison_normalized c (s := .integral E) (t := .integral L) a ha
  scalarComposition := A.scalarComposition
  scalarIdentity := A.scalarIdentity

end WeilConjectures.ConstructibleExceptionalCoefficients
