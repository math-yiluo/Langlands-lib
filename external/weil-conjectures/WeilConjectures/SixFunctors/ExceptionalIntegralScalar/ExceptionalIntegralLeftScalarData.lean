/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Left scalar comparisons before taking exceptional right mates

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: def-sf-exceptional-integral-left-scalar-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Restricted scalar extensions and normalized left proper/open comparisons.
This record contains no right comparison or exceptional-adjunction equation.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: def-sf-exceptional-integral-left-scalar-data). -/
structure LeftMates {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)) where
  scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u} l Ω a (endpoint X Y side)
  scalarShift {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : (scalar a ha side).realization.hom.CommShift ℤ
  finiteScalar_eq {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  q {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    (operation s).F ⋙ (scalar a ha false).functor ≅
      (scalar a ha true).functor ⋙ (operation t).F
  qShift {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) : (q a ha).hom.CommShift ℤ
  q_normalized {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (K : C.{u} l Ω X (s.stage l)) :
    (RingStage.inclusion.{u} l Ω Y t).map ((q a ha).hom.app K) ≫
        (left t).hom.app ((scalar a ha true).functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map
          ((scalar a ha true).realization.hom.app K) =
      (scalar a ha false).realization.hom.app ((operation s).F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map ((left s).hom.app K) ≫
        (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u} l Ω X s).obj K)
  scalarComposition {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  leftCocycle {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d)
      (K : C.{u} l Ω X (s.stage l)) :
    (scalar b hb false).functor.map ((q a ha).hom.app K) ≫
        (q b hb).hom.app ((scalar a ha true).functor.obj K) ≫
        (operation r).F.map ((scalarComposition a b d h ha hb hd true).iso.hom.app K) =
      (scalarComposition a b d h ha hb hd false).iso.hom.app ((operation s).F.obj K) ≫
        (q d hd).hom.app K
  scalarIdentity {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u} l Ω h (endpoint X Y side) (scalar a ha side)
  identityLeft {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u} l Ω X (s.stage l)) :
    (q a ha).hom.app K ≫
        (operation s).F.map ((scalarIdentity a h ha true).iso.hom.app K) =
      (scalarIdentity a h ha false).iso.hom.app ((operation s).F.obj K)
  tor_interval (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) (K : C.{u} l Ω (endpoint X Y side) (.integral E)) (a b : ℤ)
      (h : ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
        (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension l E.carrier (endpoint X Y side) n).obj K.obj) a b) :
    ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier (endpoint X Y side) n).obj
        ((scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).functor.obj K).obj) a b

/-- The prescribed right mate, constructed using the two fixed adjunctions.
Source: Zheng, Lemma 5.22; the inverse of the normalized left comparison is
transposed, so its counit equation is fixed rather than additional data.
(blueprint: def-sf-exceptional-integral-left-scalar-data). -/
def LeftMates.mate {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (z : LeftMates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) :
    (operation s).G ⋙ (z.scalar a ha true).functor ⟶
      (z.scalar a ha false).functor ⋙ (operation t).G :=
  (mateEquiv (operation s).adjunction (operation t).adjunction (z.q a ha).inv)

end WeilConjectures.ExceptionalIntegralScalar
