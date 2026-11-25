/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData

/-! # Whole-system scalar transport before selected finite-level compatibility
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26.
(blueprint: def-sf-exceptional-integral-system-scalar-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The coefficient systems, their normalized reduction comparison, and the transported
adjunction square, before selecting a ramified finite level.
Source: Zheng, Construction 4.1 and Lemma 5.22.
(blueprint: def-sf-exceptional-integral-system-scalar-core). -/
structure SystemScalarCore (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) where
  coefficient (side : Bool) : CoefficientExtensionSystems l E.carrier L.carrier i
    (endpoint X Y side)
  coefficient_model (side : Bool) : CoefficientExtensionReductionData
    l E.carrier L.carrier i (endpoint X Y side)
    (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus (coefficient side)
  scalar (side : Bool) : (sequenceProperty l E (endpoint X Y side)).FullSubcategory ⥤
    (sequenceProperty l L (endpoint X Y side)).FullSubcategory
  scalar_eq (side : Bool) : scalar side ⋙ (sequenceProperty l L (endpoint X Y side)).ι =
    (sequenceProperty l E (endpoint X Y side)).ι ⋙ (coefficient side).scalar.T
  reduction (side : Bool) :
    (d.scalar (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i) side).functor ⋙
        (tr.reconstruction L side).equivalence.functor ≅
      (tr.reconstruction E side).equivalence.functor ⋙ scalar side
  reduction_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((sequenceProperty l L (endpoint X Y side)).ι.map ((reduction side).hom.app K))
      ((coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus
        (coefficient side) (coefficient_model side)).hom.app K.obj)
  q : tr.F E ⋙ scalar false ≅ scalar true ⋙ tr.F L
  b : tr.G E ⋙ scalar true ≅ scalar false ⋙ tr.G L
  counit (N : (sequenceProperty l E Y).FullSubcategory) :
    q.hom.app ((tr.G E).obj N) ≫ (tr.F L).map (b.hom.app N) ≫
      (tr.adjunction L).counit.app ((scalar false).obj N) =
        (scalar false).map ((tr.adjunction E).counit.app N)
  q_reduction (K : C.{u} l Ω X (.integral E)) :
    (tr.reconstruction L false).equivalence.functor.map
        ((Mates.q l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app K) ≫
      (tr.reductionF L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) true).functor.obj K) ≫
      (tr.F L).map ((reduction true).hom.app K) =
    (reduction false).hom.app ((operation (.integral E)).F.obj K) ≫
      (scalar false).map ((tr.reductionF E).hom.app K) ≫
        q.hom.app ((tr.reconstruction E true).equivalence.functor.obj K)
  b_reduction (N : C.{u} l Ω Y (.integral E)) :
    (tr.reconstruction L true).equivalence.functor.map
        ((Mates.b l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app N) ≫
      (tr.reductionG L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) false).functor.obj N) ≫
      (tr.G L).map ((reduction false).hom.app N) =
    (reduction true).hom.app ((operation (.integral E)).G.obj N) ≫
      (scalar true).map ((tr.reductionG E).hom.app N) ≫
        b.hom.app ((tr.reconstruction E false).equivalence.functor.obj N)

/-- Selected finite-level comparisons for an already constructed whole-system scalar
functor and its left mate. The right selected equation is deliberately absent: it
follows by taking transposes from the left equation and the two counit identities.
Source: Zheng, Construction 4.1 and Proposition 5.26.
(blueprint: def-sf-exceptional-integral-system-selected-left). -/
structure SystemSelectedLeft (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left tr d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (core : SystemScalarCore l Ω D hl c operation left tr d E L i) where
  selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool) :
    core.scalar side ⋙ (tr.reconstruction L side).evaluation z.m ≅
      (tr.reconstruction E side).evaluation z.n ⋙
        (d.scalar z.change z.allowed side).functor
  selected_square (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}) :
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T
  selected_balanced (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι.map
        ((red L z.m).evaluation side |>.hom.app
            ((d.scalar (s := .integral E) (t := .integral L)
              (PurCompactSupport.completedChange l E.carrier L.carrier i)
              (Allowed.integral E L i) side).functor.obj K)) ≫
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
        (endpoint X Y side)).ι.map
        (((tr.reconstruction L side).evaluation z.m).map ((core.reduction side).hom.app K) ≫
          (selected e he z side).hom.app
            ((tr.reconstruction E side).equivalence.functor.obj K) ≫
          (d.scalar z.change z.allowed side).functor.map
            (((red E z.n).evaluation side).inv.app K)))
      ((pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
          (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side))).map
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare
          ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
            (endpoint X Y side)) (z.change.map (endpoint X Y side))
          ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
            (endpoint X Y side))
          ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
            (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app K.obj)
  q_selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E X).FullSubcategory) :
    ((tr.reconstruction L false).evaluation z.m).map (core.q.hom.app N) ≫
      (tr.evaluationF L z.m).hom.app ((core.scalar true).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).F.map
        ((selected e he z true).hom.app N) =
    (selected e he z false).hom.app ((tr.F E).obj N) ≫
      (d.scalar z.change z.allowed false).functor.map
        ((tr.evaluationF E z.n).hom.app N) ≫
      (Mates.q l Ω d z.change z.allowed).hom.app
        (((tr.reconstruction E true).evaluation z.n).obj N)

end WeilConjectures.ExceptionalIntegralScalar
