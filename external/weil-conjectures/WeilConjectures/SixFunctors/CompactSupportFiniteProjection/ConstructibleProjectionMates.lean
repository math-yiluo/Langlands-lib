/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
/-! # Canonical constructible projection mates
Source: projection-formula construction, proof steps 1--6
(blueprint: def-sf-constructible-projection-mates).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe u v w v' w' a b c d ha hb hc hd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The identity base-change square retaining a prescribed compactification.
Source: the chosen compactification paragraph of the projection transformation
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProjectionSquare {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X
  Y' := Y
  Z := ⟨Over.mk (c.g ≫ Y.obj.hom), by
    have := c.isProper
    have := Y.property.1
    have := Y.property.2
    change LocallyOfFiniteType (c.g ≫ Y.obj.hom) ∧ QuasiCompact (c.g ≫ Y.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  Z' := ⟨Over.mk (c.g ≫ Y.obj.hom), by
    have := c.isProper
    have := Y.property.1
    have := Y.property.2
    change LocallyOfFiniteType (c.g ≫ Y.obj.hom) ∧ QuasiCompact (c.g ≫ Y.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  f := f
  f' := f
  g := 𝟙 Y
  g' := 𝟙 X
  i := ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ Y.obj.hom) c.comm.symm).trans f.hom.w)))
  i' := ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ Y.obj.hom) c.comm.symm).trans f.hom.w)))
  p := ObjectProperty.homMk (Over.homMk c.g)
  p' := ObjectProperty.homMk (Over.homMk c.g)
  h := 𝟙 _
  open_i := c.isOpenImmersion
  open_i' := c.isOpenImmersion
  proper_p := c.isProper
  proper_p' := c.isProper
  factorization := by ext; exact c.comm
  factorization' := by ext; exact c.comm
  square := IsPullback.of_id_fst
  properSquare := IsPullback.of_id_fst
  openSquare := IsPullback.of_id_fst
  squareComm := by simp
  properComm := by simp
  openComm := by simp

/-- Components of the specified compactification projection in operation coordinates.
Source: def-exchange-projection, the counit mate followed by open projection
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProjectionComponent {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : B X) (L : B Y) :
    ((T Y).obj ((S.support f c).obj K)).obj L ⟶
      (S.support f c).obj (((T X).obj K).obj ((S.pull f).obj L)) :=
  (A (compactSupportProjectionSquare f c)).projectionComponent K L

/-- Identity-open square for the proper comparison, in the original object coordinates.
Source: the proper clause (blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProperSquare {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X
  Y' := Y
  Z := X
  Z' := X
  f := f
  f' := f
  g := 𝟙 Y
  g' := 𝟙 X
  i := 𝟙 X
  i' := 𝟙 X
  p := f
  p' := f
  h := 𝟙 X
  open_i := inferInstance
  open_i' := inferInstance
  proper_p := inferInstance
  proper_p' := inferInstance
  factorization := by simp
  factorization' := by simp
  square := IsPullback.of_id_fst
  properSquare := IsPullback.of_id_fst
  openSquare := IsPullback.of_id_fst
  squareComm := by simp
  properComm := by simp
  openComm := by simp

/-- The same counit mate for a proper map, without the open factor.
Source: proper identification clause of the projection formula
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProperProjection {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : B X) (L : B Y) :
    ((T Y).obj ((S.direct f).obj K)).obj L ⟶
      (S.direct f).obj (((T X).obj K).obj ((S.pull f).obj L)) :=
  eqToHom (by
    simp only [(A (compactSupportProperSquare f)).tensorY,
      (A (compactSupportProperSquare f)).properPush]
    rfl) ≫
  (((A (compactSupportProperSquare f)).stage.properAdjunction.rightAdjointProjectionMap
    (A (compactSupportProperSquare f)).stage.tensorPullback.hom).app K).app L ≫
  eqToHom (by
    simp only [(A (compactSupportProperSquare f)).tensorBar,
      (A (compactSupportProperSquare f)).properPush,
      (A (compactSupportProperSquare f)).properPull]
    rfl)

/-- Tensoring a comparison in the first slot, then applying a realization.
Source: coefficient transport of projection (blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorLeftRealization {A : Type v} [Category.{w} A]
    {B : Type v'} [Category.{w'} B] (T : A ⥤ A ⥤ A) (V : A ⥤ B)
    {K K' : A} (e : K ≅ K') (L : A) :
    V.obj ((T.obj K).obj L) ≅ V.obj ((T.obj K').obj L) :=
  V.mapIso ((T.mapIso e).app L)

/-- Cancel the inner coefficient unit, tensor a pullback comparison, and apply
compact support and realization. Source: finite projection
(blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorTargetRealization
    {A : Type a} [Category.{ha} A] {B : Type b} [Category.{hb} B]
    {C : Type c} [Category.{hc} C] {D : Type d} [Category.{hd} D]
    (R : A ≌ B) (V : C ⥤ D) (F : A ⥤ C) (T : A ⥤ A ⥤ A)
    (K : A) {L : B} {L' : A} (e : R.inverse.obj L ≅ L') :
    V.obj (F.obj (R.inverse.obj (R.functor.obj ((T.obj K).obj (R.inverse.obj L))))) ≅
      V.obj (F.obj ((T.obj K).obj L')) :=
  V.mapIso (F.mapIso ((R.unitIso.app _).symm ≪≫ (T.obj K).mapIso e))

/-- Conjugation of an ambient arrow, lifted through a full subcategory.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def projectionFullConjugate {A : Type v} [Category.{w} A] {P : ObjectProperty A}
    {K L : P.FullSubcategory} {U V : A} (e : K.obj ≅ U) (e' : L.obj ≅ V)
    (a : U ⟶ V) : K ⟶ L :=
  ObjectProperty.homMk (e.hom ≫ a ≫ e'.inv)

/-- Evaluate the proper/open projection with its tensor-coordinate endpoints exposed.
Doing the endpoint conversion at an arbitrary coefficient category prevents repeated
reduction of derived tensor constructions after specializing the coefficients.
Source: the canonical proper/open mate, current projection-formula construction
(blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorCoordinateComponent (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ((AlgebraicGeometry.ProEtale.derivedTensor A Y).obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor).obj K)).obj L ⟶
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor).obj
        (((AlgebraicGeometry.ProEtale.derivedTensor A X).obj K).obj
          ((AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor.obj L)) :=
  ((projectionMapOfCompactification A c).app K).app L

/-- The tensor-coordinate evaluation inherits invertibility of the published mate.
Source: the same proper/open projection (blueprint: def-sf-constructible-projection-mates). -/
theorem projectionTensorCoordinateComponent_isIso (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : IsIso (((projectionMapOfCompactification A c).app K).app L)) :
    IsIso (projectionTensorCoordinateComponent A c K L) := by
  exact h

/-- The coordinate presentation evaluates the published projection, without a new choice.
Source: the same proper/open projection (blueprint: def-sf-constructible-projection-mates). -/
theorem projectionTensorCoordinateComponent_eq (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    projectionTensorCoordinateComponent A c K L =
      ((projectionMapOfCompactification A c).app K).app L := by
  rfl

namespace CompactSupportFiniteProjection
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorFiniteOperations D C E n hn)

/-- The canonical derived coefficient realization, with the positive exponent retained.
Source: the finite clause (blueprint: def-sf-constructible-projection-mates). -/
def realization (X : SixFunctorSpace D) :
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ≌
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) :=
  sixFunctorFiniteRealization D C E n hn X

/-- The recorded fixed-scalar tensor with its derived-category type exposed.
Source: finite tensor convention (blueprint: def-sf-constructible-projection-mates). -/
def fixedTensor (X : SixFunctorSpace D) :
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) :=
  AlgebraicGeometry.ProEtale.derivedTensor
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) X.obj.left

/-- The K-flat left-derived inverse image, with a fixed exposed category type.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedDerivedPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) :=
  (AlgebraicGeometry.ProEtale.upperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left).leftDerivedFunctor

/-- The published normalization of K-flat inverse image by exact inverse image.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedPullComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    fixedDerivedPull (C := C) (E := E) (n := n) f ≅
      sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left :=
  AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left

/-- The existing proper/open projection in a compact exposed signature.
Source: def-exchange-projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    ((fixedTensor (C := C) (E := E) (n := n) Y).obj
      ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj K)).obj L ⟶
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      (((fixedTensor (C := C) (E := E) (n := n) X).obj K).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  projectionTensorCoordinateComponent
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) c K L

/-- The finite signed derived tensor, transported through the published coefficient
realization. This is a change of presentation of the existing tensor.
Source: the finite projection display (blueprint: def-sf-constructible-projection-mates). -/
def tensor (X : SixFunctorSpace D) :
    proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (Functor.postcompose₂.obj (realization (C := C) (E := E) (n := n) (hn := hn) X).functor).obj
    ((((Functor.whiskeringLeft₂ _).obj
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj
      (fixedTensor (C := C) (E := E) (n := n) X))

private theorem torAmplitudeIso (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨h.1, ?_⟩
  intro V P hV f hf hP M i hi
  obtain ⟨eV⟩ := hV
  exact h.2 V P ⟨eV ≪≫ e.symm⟩ f hf hP M i hi

private theorem etaleBoundedIff (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : AlgebraicGeometry.Etale.DerivedCategoryModule A X) :
    AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A X K ↔
      AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private theorem fixedEtaleOrigin (X : SixFunctorSpace D)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let A := Padic.coefficientExtensionRing C.l E n
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    ∃ L : AlgebraicGeometry.Etale.DerivedCategoryModule (ULift.{u + 1} A) X.obj.left,
      AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left L ∧
      Nonempty ((AlgebraicGeometry.ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left).mapDerivedCategory.obj L ≅
          (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) := by
  classical
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let U := AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left
  obtain ⟨a, ha⟩ := K.property.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X.obj.left A).2.2.1
    K.obj).mpr ⟨K.property.2, min a b, b, min_le_right _ _, hv⟩
  refine ⟨L.obj, (etaleBoundedIff _ _ _).1 L.property, ⟨?_⟩⟩
  apply R.functor.preimageIso
  exact ((Functor.mapDerivedCategoryCompIso U
    (sfIntrinsicModuleEquivalence X.obj.left A).functor).app L.obj) ≪≫
      eL ≪≫ (R.counitIso.app K.obj).symm

/-- Exactly the typing facts for the partial finite tensor and finite-Tor pullback.
There is no finite-Tor assumption on the first input.
Source: the domains of the projection formula (blueprint: def-sf-constructible-projection-mates).
Proof (postponed): use the finite constructible etale-origin equivalence and its
Tor comparison. On etale representatives, tensor with a bounded flat model of the
second input preserves bounded constructibility. Exact inverse image preserves the
same flat interval. Transport through the canonical coefficient equivalence and
finitePullback. These assertions involve all representatives and all morphisms. -/
theorem domains :
    (∀ (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
      intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left
        (((tensor (C := C) (E := E) (n := n) (hn := hn) X).obj K.obj).obj L.obj)) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      finiteTorConstructible C.l E n hn X.obj.left ((S.finite.pull f).obj
        ⟨L.obj, L.property.1⟩).obj) := by
  classical
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  constructor
  · intro X K L
    let R := realization (C := C) (E := E) (n := n) (hn := hn) X
    let U := AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left
    obtain ⟨K', hK', ⟨eK⟩⟩ := fixedEtaleOrigin X K
    obtain ⟨L', hL', ⟨eL⟩⟩ := fixedEtaleOrigin X ⟨L.obj, L.property.1⟩
    obtain ⟨a, b, ht⟩ := L.property.2
    have hfixed := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X.obj.left a b ht.1 (R.inverse.obj L.obj)).1
        (torAmplitudeIso _ _ (R.counitIso.app L.obj).symm ht)
    have hetale := (AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
      (Λ := ULift.{u + 1} A) a b L').1
        ((DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eL.symm hfixed)
    have hT := AlgebraicGeometry.Etale.boundedConstructible_tensor
      (ULift.{u + 1} A) X.obj.left hK' hL' ⟨a, b, hetale⟩
    let eT := (asIso ((U.mapDerivedCategoryTensorComparison.app K').app L')) ≪≫
      MonoidalCategory.tensorIso eK eL
    have himage := ((finiteRing_constructibleDerived_origin X.obj.left A).2.2.1
      (((tensor (C := C) (E := E) (n := n) (hn := hn) X).obj K.obj).obj L.obj)).mp
      ⟨⟨_, (etaleBoundedIff _ _ _).2 hT⟩,
        ⟨((Functor.mapDerivedCategoryCompIso U
          (sfIntrinsicModuleEquivalence X.obj.left A).functor).app _).symm ≪≫
            R.functor.mapIso eT⟩⟩
    refine ⟨?_, himage.1⟩
    obtain ⟨c, d, _, hv⟩ := himage.2
    apply (Set.finite_Icc c d).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hv i (.inl h))),
      le_of_not_gt (fun h ↦ hi (hv i (.inr h)))⟩
  · intro X Y f L
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let U := AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left
    let e : ((S.finite.pull f).obj ⟨L.obj, L.property.1⟩).obj ≅
        RX.functor.obj (U.mapDerivedCategory.obj (RY.inverse.obj L.obj)) :=
      (S.finitePullback f).app ⟨L.obj, L.property.1⟩ ≪≫
        ((Functor.mapDerivedCategoryCompIso
          (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
          (U ⋙ (sfIntrinsicModuleEquivalence X.obj.left A).functor)).symm ≪≫
          Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm).app L.obj
    obtain ⟨a, b, h⟩ := L.property.2
    have hfixed := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A Y.obj.left a b h.1 (RY.inverse.obj L.obj)).1
        (torAmplitudeIso _ _ (RY.counitIso.app L.obj).symm h)
    have hpull := AlgebraicGeometry.ProEtale.torAmplitudeIn_leftDerivedUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left a b hfixed
    have hexact := (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left).app _) hpull
    refine ⟨((S.finite.pull f).obj ⟨L.obj, L.property.1⟩).property, a, b, ?_⟩
    exact torAmplitudeIso _ _ e.symm
      ((intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
        A X.obj.left a b h.1 _).2 hexact)

/-- The partial tensor on its full first and finite-Tor second domains.
Source: the finite coefficient clause (blueprint: def-sf-constructible-projection-mates). -/
def partialTensor (X : SixFunctorSpace D) :
    sixFunctorFiniteCategory D C E n hn X ⥤
      finiteTorConstructibleCategory C.l E n hn X.obj.left ⥤
        sixFunctorFiniteCategory D C E n hn X :=
  Functor.currying.inverse.obj
    ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).lift
      ((((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι).prod
        (finiteTorConstructible C.l E n hn X.obj.left).ι) ⋙
          Functor.uncurry.obj (tensor (C := C) (E := E) (n := n) (hn := hn) X))
      (fun KL ↦ (domains S).1 X KL.1 KL.2))

/-- The restriction of the recorded inverse image to finite-Tor inputs.
Source: the finite coefficient clause (blueprint: def-sf-constructible-projection-mates). -/
def torPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    finiteTorConstructibleCategory C.l E n hn Y.obj.left ⥤
      finiteTorConstructibleCategory C.l E n hn X.obj.left :=
  (finiteTorConstructible C.l E n hn X.obj.left).lift
    ((ObjectProperty.ιOfLE (show finiteTorConstructible C.l E n hn Y.obj.left ≤
      intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left from fun _ h ↦ h.1)) ⋙
        S.finite.pull f ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι)
    (fun L ↦ (domains S).2 f L)

/-- The prescribed support realization, including cancellation of the coefficient
unit. Thus no free comparison of support functors is introduced.
Source: finite compactification construction (blueprint: def-sf-constructible-projection-mates). -/
def supportRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X) :
    ((S.finite.support f c).obj K).obj ≅
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.obj
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (S.finiteSupport f c).app K ≪≫
    (sixFunctorFiniteSupport D C E n hn f c).mapIso
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).counitIso.app K.obj).symm ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c).app
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)

/-- Canonical cancellation of the coefficient equivalence in inverse image.
Source: finite pullback construction (blueprint: def-sf-constructible-projection-mates). -/
def pullRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sixFunctorFiniteCategory D C E n hn Y) :
    ((S.finite.pull f).obj L).obj ≅
      (realization (C := C) (E := E) (n := n) (hn := hn) X).functor.obj
        ((sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (S.finitePullback f).app L ≪≫
    ((Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence Y.obj.left (Padic.coefficientExtensionRing C.l E n)).inverse
      (AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left ⋙
        (sfIntrinsicModuleEquivalence X.obj.left
          (Padic.coefficientExtensionRing C.l E n)).functor)).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm).app L.obj

/-- Support realization in fixed-scalar coordinates, cancelling the unit before
applying tensor. Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedSupportRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X) :
    (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj
      ((S.finite.support f c).obj K).obj ≅
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  RY.inverse.mapIso (supportRealization S f c K) ≪≫
    (RY.unitIso.app ((sfFixedCompactSupport
      (Padic.coefficientExtensionRing C.l E n) c).obj (RX.inverse.obj K.obj))).symm

/-- Tensor the fixed support comparison and realize it back. Source: finite projection
(blueprint: def-sf-constructible-projection-mates). -/
def sourceComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  projectionTensorLeftRealization TY RY.functor
    (fixedSupportRealization S f c K) (RY.inverse.obj L.obj)

/-- Pullback in fixed-scalar coordinates, with the coefficient unit cancelled.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedPullRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sixFunctorFiniteCategory D C E n hn Y) :
    (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj
      ((S.finite.pull f).obj L).obj ≅
    (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  RX.inverse.mapIso (pullRealization S f L) ≪≫
    (RX.unitIso.app ((sfFixedDerivedPullback
      (Padic.coefficientExtensionRing C.l E n) f.hom.left).obj
        (RY.inverse.obj L.obj))).symm ≪≫
    (fixedPullComparison (C := C) (E := E) (n := n) f).symm.app (RY.inverse.obj L.obj)

/-- Target realization of the finite partial tensor projection.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def targetComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  supportRealization S f c (((partialTensor S X).obj K).obj ((torPull S f).obj L)) ≪≫
    projectionTensorTargetRealization RX RY.functor F TX (RX.inverse.obj K.obj)
      (fixedPullRealization S f ⟨L.obj, L.property.1⟩)

/-- The finite projection on the full bounded constructible first domain. The
published proper-counit/open projection is conjugated only by the explicit source
and target comparisons above, then lifted through the full inclusion.
Source: the finite projection display (blueprint: def-sf-constructible-projection-mates). -/
def component {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    ((partialTensor S Y).obj ((S.finite.support f c).obj K)).obj L ⟶
      (S.finite.support f c).obj
        (((partialTensor S X).obj K).obj ((torPull S f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  projectionFullConjugate (sourceComparison S f c K L) (targetComparison S f c K L)
    ((realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.map
      (fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)
        ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)))

/-- The restricted pullback compositor is the recorded compositor, lifted through
its full finite-Tor inclusion. Source: composition clause
(blueprint: def-sf-constructible-projection-mates). -/
def torPullComposition {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    (torPull S (f ≫ g)).obj L ≅ (torPull S f).obj ((torPull S g).obj L) :=
  ObjectProperty.isoMk _
    ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
      ((S.finite.pullComposition f g).app ⟨L.obj, L.property.1⟩))

/-- The proper counit projection in these coordinates. The identity-open
compactification cancels via the specified proper identification.
Source: proper clause (blueprint: def-sf-constructible-projection-mates). -/
def properComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    ((partialTensor S Y).obj ((S.finite.direct f).obj K)).obj L ⟶
      (S.finite.direct f).obj (((partialTensor S X).obj K).obj ((torPull S f).obj L)) :=
  ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
    component S f (.ofIsProper f.hom.left) K L ≫
    (S.finite.properIdentity f).hom.app
      (((partialTensor S X).obj K).obj ((torPull S f).obj L))

/-- Finite projection coherence on the full first and finite-Tor second domains.
Every arrow is the explicit canonical component above. Source: finite coefficient
and coherence clauses (blueprint: def-sf-constructible-projection-mates). -/
structure Laws : Prop where
  isIso : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      IsIso (component S f c K L)
  naturality : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : sixFunctorFiniteCategory D C E n hn X}
    {L L' : finiteTorConstructibleCategory C.l E n hn Y.obj.left},
    ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((partialTensor S Y).map ((S.finite.support f c).map a)).app L ≫
          ((partialTensor S Y).obj ((S.finite.support f c).obj K')).map b ≫
          component S f c K' L' =
        component S f c K L ≫
          (S.finite.support f c).map
            (((partialTensor S X).map a).app ((torPull S f).obj L) ≫
              ((partialTensor S X).obj K').map ((torPull S f).map b))
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((partialTensor S Y).map ((S.finite.comparison f c d).hom.app K)).app L ≫
          component S f d K L =
        component S f c K L ≫
          (S.finite.comparison f c d).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L))
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left),
      ((partialTensor S Z).map ((S.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f cf).obj K) L ≫
          (S.finite.support g cg).map
            (component S f cf K ((torPull S g).obj L)) =
        component S (f ≫ g) cfg K L ≫
          (S.finite.composition f g cf cg cfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom))
  pentagon : ∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sixFunctorFiniteCategory D C E n hn X),
    HEq ((S.finite.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.finite.support h ch).map ((S.finite.composition f g cf cg cfg).hom.app K))
      ((S.finite.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.finite.composition g h cg ch cgh).hom.app ((S.finite.support f cf).obj K))
  proper : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((partialTensor S Y).map ((S.finite.properIdentification f c).hom.app K)).app L ≫
          properComponent S f K L =
        component S f c K L ≫
          (S.finite.properIdentification f c).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L))

end CompactSupportFiniteProjection
end WeilConjectures
