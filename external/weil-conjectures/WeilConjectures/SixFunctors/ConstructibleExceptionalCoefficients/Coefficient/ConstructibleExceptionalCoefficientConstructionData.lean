/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData

/-! # Normalized coefficient adjunction construction before coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The individual invertible coefficient mate with its defining counit equation.
Source: coefficient transpose construction
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CounitComparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    [TX.CommShift ℤ] [TY.CommShift ℤ] where
  q : A.F ⋙ TY ≅ TX ⋙ B.F
  b : A.G ⋙ TX ≅ TY ⋙ B.G
  counit (L : C.{u, v} l Ω Y s) :
    q.hom.app (A.G.obj L) ≫ B.F.map (b.hom.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/-- The counit transpose respects the units, by naturality and the triangles.
Source: coefficient transpose calculation
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
theorem comparison_unit_of_counit
    {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    (q : A.F ⋙ TY ≅ TX ⋙ B.F) (b : A.G ⋙ TX ⟶ TY ⋙ B.G)
    (hc : ∀ L, q.hom.app (A.G.obj L) ≫ B.F.map (b.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L))
    (K : C.{u, v} l Ω X s) :
    TX.map (A.adjunction.unit.app K) ≫ b.app (A.F.obj K) ≫
      B.G.map (q.hom.app K) = B.adjunction.unit.app (TX.obj K) := by
  apply (B.adjunction.homEquiv _ _).symm.injective
  change B.F.map _ ≫ B.adjunction.counit.app _ =
    B.F.map _ ≫ B.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [B.adjunction.counit_naturality]
  rw [← Category.assoc (B.F.map (b.app _))]
  have hc' := hc (A.F.obj K)
  have htrans : B.F.map (b.app (A.F.obj K)) ≫
      B.adjunction.counit.app (TY.obj (A.F.obj K)) =
      q.inv.app (A.G.obj (A.F.obj K)) ≫
        TY.map (A.adjunction.counit.app (A.F.obj K)) := by
    rw [← hc', ← Category.assoc, ← Category.assoc]
    simp only [Iso.inv_hom_id_app, Category.id_comp]
  rw [htrans]
  have hn := q.inv.naturality (A.adjunction.unit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (TY.map _) (TY.map _), ← TY.map_comp]
  erw [A.adjunction.left_triangle_components K]
  change q.inv.app K ≫ TY.map (𝟙 (A.F.obj K)) ≫ q.hom.app K =
    B.F.map (B.adjunction.unit.app (TX.obj K)) ≫
      B.adjunction.counit.app (B.F.obj (TX.obj K))
  rw [TY.map_id]
  calc
    _ = q.inv.app K ≫ q.hom.app K :=
      congrArg (fun h ↦ q.inv.app K ≫ h) (Category.id_comp (q.hom.app K))
    _ = 𝟙 _ := q.inv_hom_id_app K
    _ = _ := (B.adjunction.left_triangle_components (TX.obj K)).symm

/-- Complete a counit-normalized invertible mate using the triangle identities.
Source: the coefficient comparison construction, inverse-transpose argument
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitComparison.complete {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    [TX.CommShift ℤ] [TY.CommShift ℤ]
    (d : CounitComparison.{u, v} l Ω A B TX TY) : Comparison.{u, v} l Ω A B TX TY where
  q := d.q
  b := d.b
  unit := comparison_unit_of_counit.{u, v} l Ω A B TX TY d.q d.b.hom d.counit
  counit := d.counit
  qShift := d.qShift
  bShift := d.bShift

/-- The right coefficient cocycle follows from the left cocycle by taking transposes.
Source: mate pasting, blueprint coefficient adjunction Step 6
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
theorem comparison_right_cocycle_of_left
    {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s}
    {B : Operation.{u, v} l Ω X Y t} {D : Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    [TX.CommShift ℤ] [TY.CommShift ℤ] [UX.CommShift ℤ] [UY.CommShift ℤ]
    [VX.CommShift ℤ] [VY.CommShift ℤ]
    (a : Comparison.{u, v} l Ω A B TX TY) (b : Comparison.{u, v} l Ω B D UX UY)
    (d : Comparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY)
    (hleft : ∀ K, UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫
      D.F.map (αX.hom.app K) = αY.hom.app (A.F.obj K) ≫ d.q.hom.app K)
    (L : C.{u, v} l Ω Y s) :
    UX.map (a.b.hom.app L) ≫ b.b.hom.app (TY.obj L) ≫ D.G.map (αY.hom.app L) =
      αX.hom.app (A.G.obj L) ≫ d.b.hom.app L := by
  apply (D.adjunction.homEquiv _ _).symm.injective
  change D.F.map _ ≫ D.adjunction.counit.app _ =
    D.F.map _ ≫ D.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [D.adjunction.counit_naturality]
  apply (cancel_epi (UY.map (a.q.hom.app (A.G.obj L)) ≫
    b.q.hom.app (TX.obj (A.G.obj L)))).1
  simp only [Category.assoc]
  have hn := b.q.hom.naturality (a.b.hom.app L)
  dsimp only [Functor.comp_map] at hn
  have hα := αY.hom.naturality (A.adjunction.counit.app L)
  dsimp only [Functor.comp_map] at hα
  calc
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        b.q.hom.app (B.G.obj (TY.obj L)) ≫
        D.F.map (b.b.hom.app (TY.obj L)) ≫
        D.adjunction.counit.app (UY.obj (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% hn]
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        UY.map (B.adjunction.counit.app (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% (b.counit (TY.obj L))]
    _ = UY.map (TY.map (A.adjunction.counit.app L)) ≫ αY.hom.app L := by
      rw [← UY.map_comp_assoc, ← UY.map_comp_assoc, Category.assoc, a.counit]
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫
        VY.map (A.adjunction.counit.app L) := hα
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫ d.q.hom.app (A.G.obj L) ≫
        D.F.map (d.b.hom.app L) ≫ D.adjunction.counit.app (VY.obj L) := by
      rw [d.counit L]
    _ = _ := by rw [← reassoc_of% (hleft (A.G.obj L))]

/-- A counit-normalized field comparison retaining the endpoint shift structures.
Source: field coefficient comparisons
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CounitFieldComparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t) where
  [shiftX : TX.CommShift ℤ]
  [shiftY : TY.CommShift ℤ]
  comparison : CounitComparison.{u, v} l Ω A B TX TY

/-- Left comparison with the output shift structures retained in its type.
Source: blueprint coefficient q (blueprint:
lem-sf-constructible-exceptional-coefficient-construction).
-/
def CounitFieldComparison.q {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : A.F ⋙ TY ≅ TX ⋙ B.F :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.q

/-- Right comparison with the output shift structures retained in its type.
Source: blueprint coefficient b (blueprint:
lem-sf-constructible-exceptional-coefficient-construction).
-/
def CounitFieldComparison.b {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : A.G ⋙ TX ≅ TY ⋙ B.G :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.b

/-- Complete the field-stage mate while keeping its chosen shift structures.
Source: the same inverse-transpose argument
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitFieldComparison.complete {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : FieldComparison.{u, v} l Ω A B TX TY :=
  letI := d.shiftX
  letI := d.shiftY
  { shiftX := d.shiftX
    shiftY := d.shiftY
    comparison := d.comparison.complete l Ω }

/-- Canonical q normalization before completing its unit equation.
Source: proper/open scalar mate
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitQNormalized {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)
    {s t : RingStage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (rA : LeftRealization.{u, v} l Ω c s A) (rB : LeftRealization.{u, v} l Ω c t B)
    (d : CounitComparison.{u, v} l Ω A B SX.functor SY.functor) : Prop :=
  ∀ K : C.{u, v} l Ω X (s.stage l),
    (RingStage.inclusion.{u, v} l Ω Y t).map (d.q.hom.app K) ≫
        rB.hom.app (SX.functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
      SY.realization.hom.app (A.F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
        (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u, v} l Ω X s).obj K)

/-- Projection of the constructed scalar mate.
Source: coefficient comparison
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def Scalar.counitQ {X Y : Scheme.{max u v}} {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (d : CounitComparison.{u, v} l Ω A B SX.functor SY.functor) :
    A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F :=
  d.q

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRing (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  operation (c : Compactification f) (s : Stage.{max u v} l) : Operation.{u, v} l Ω X Y s
  left (c : Compactification f) (s : RingStage.{max u v} l) :
    LeftRealization.{u, v} l Ω c s (operation c (s.stage l))
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
  rationalLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.rational E)).F ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
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
    CounitComparison.{u, v} l Ω (operation c (s.stage l)) (operation c (t.stage l))
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

/-- The action of a localized functor on the unchanged objects and integral arrows.
Source: raw coefficient localization
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def localizedAction {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Fi : A ⥤ B) (Fr : C ⥤ D) (LX : A ⥤ C) (LY : B ⥤ D) : Prop :=
  (∀ K : A, Fr.obj (LX.obj K) = LY.obj (Fi.obj K)) ∧
  (∀ (K L : A) (h : K ⟶ L), HEq (Fr.map (LX.map h)) (LY.map (Fi.map h)))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionFields (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{max u v} l) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.counitQ.{u, v} l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))

  rationalAction (c : Compactification f) (E : FieldStage.{max u v} l) :
    localizedAction (R.operation c (.integral E)).F (R.operation c (.rational E)).F
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)

/-- Coefficient squares determine the action on common representatives.
Source: common-stage construction on the colimit Hom groups
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def representativeAction
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi) : Prop :=
  ∀ (K : A) (L : B) (a : TX.obj K ⟶ L),
    FΩ.map (tauX.inv.app K ≫ IXj.map a) =
      qi.inv.app K ≫ tauY.inv.app (Fi.obj K) ≫ IYj.map (q.hom.app K) ≫
        IYj.map (Fj.map a) ≫ qj.hom.app L

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionCommon (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational (commonField.{u, v} l Ω i)))
      (R.operation c .closed)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K)))

  common_morphism_normalized (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j) :
    representativeAction
      (R.operation c (.rational (commonField l Ω i))).F
      (R.operation c (.rational (commonField l Ω j))).F (R.operation c .closed).F
      (rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X)
      (rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y)
      (commonInclusion l Ω X i) (commonInclusion l Ω X j)
      (commonInclusion l Ω Y i) (commonInclusion l Ω Y j)
      (F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q
      (commonComparison c i).q (commonComparison c j).q
      (commonTransition l Ω X i j h) (commonTransition l Ω Y i j h)

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRefinements (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((refinement r (.rational (commonField.{u, v} l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion.{u, v} l Ω X i).obj K)

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstruction (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 where
  ring : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)
  fields : CoefficientConstructionFields.{u, v} l Ω D hl ring
  common : CoefficientConstructionCommon.{u, v} l Ω D hl ring fields
  refinements : CoefficientConstructionRefinements.{u, v} l Ω D hl ring fields common
  /-- Retain the identity comparison of raw localization used in the construction.
  This prevents independent rescaling of rationalLeft at each coefficient field.
  Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; raw localization
  (blueprint: def-sf-constructible-exceptional-coefficient-construction-data). -/
  localizationIdentity (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((fields.rationalizationComparison c E).q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj
        ((ring.operation c (.integral E)).F.obj K)))

end ConstructibleExceptionalCoefficients
end WeilConjectures
