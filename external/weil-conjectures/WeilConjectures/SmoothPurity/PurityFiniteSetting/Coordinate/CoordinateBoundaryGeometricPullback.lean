/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-! # Geometric pullback of the actual coordinate Kummer boundary

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-affine-line-orientation.proof.md, geometric-fibre sentence; Milne,
Lectures on Etale Cohomology, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-coordinate-boundary-geometric-pullback).

The section-class conversion below derives evaluation of the actual constant unit.
All coefficient maps are the pure-tensor maps of the affine-line datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u' v v' w w' d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Abelian.Ext

/-- The coefficient-adjusted degree-one pullback identity, with abstract categories
so the two Yoneda compositions share their category instances without re-expansion.
Source: Kummer naturality and coefficient extension
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinatePullbackIdentity
    {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    {D : Type v'} [Category.{w'} D] [Abelian D] [IsGrothendieckAbelian.{u'} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A F : C} {A' F' : D} (x : Ext.{u} A F 1) (y : Ext.{u'} A' F' 1)
    (a : L.obj A ⟶ A') (b : L.obj F ⟶ F') : Prop :=
  (x.mapExactFunctor L).comp (Ext.mk₀ b) (add_zero 1) =
    (Ext.mk₀ a).comp y (zero_add 1)

/-- Evaluation on a degree-one Ext class as a morphism under an additive functor.
The degree-zero derived unit and canonical shifts specify the morphism.
Source: Milne, Theorem 9.4, Ext description
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateSectionMap
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    [HasDerivedCategory.{u'} C] [EnoughInjectives C] [HasKInjectiveResolutions C]
    {D : Type v'} [Category.{w'} D] [Abelian D] [HasDerivedCategory.{d} D]
    (E : C ⥤ D) [E.Additive] {B F : C} (c : Ext.{u} B F 1) :
    E.obj B ⟶ (DerivedCategory.Plus.homologyFunctor D 1).obj
      (E.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj F)) :=
  E.toRightDerivedZero.app B ≫
    (E.homologyRightDerivedFunctorObjSingleFunctorIso B 0).inv ≫
    (DerivedCategory.homologyFunctor D 0).map
      (E.rightDerivedFunctor.map c.hom ≫
        (E.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app _) ≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso (1 : ℤ) 0 1 (add_zero 1)).hom.app _ ≫
    (Functor.isoWhiskerRight E.rightDerivedFunctorPlusCompatibility.symm
      (DerivedCategory.homologyFunctor D 1)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj F)

end CategoryTheory.Abelian.Ext

namespace WeilConjectures.PurityFiniteSetting

/-- Evaluation of a derived module class on the constant unit, using the canonical
right-derived comparison and shift maps. Source: Milne, Theorem 9.4, Ext description
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateClassSection (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (c : Abelian.Ext (P.constantEtale T) F 1) :
    (Sheaf.sectionHypercohomologyFunctor T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.mk (𝟙 T)) 1).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
  (Abelian.Ext.coordinateSectionMap
    (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) T) c)
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
        (Scheme.Etale.isTerminalMkId T)).homEquiv _ _ (𝟙 (P.constantEtale T))) 1)

/-- The canonical open evaluation comparison, derived from localization of the etale site.
Source: Milne, Section 9, restriction to the complementary open
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateOpenSectionsIso (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) U ≅
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk j)) :=
  Functor.isoWhiskerRight
    (Etale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} P.Coefficient) j inferInstance)
    (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) U) ≪≫
      (let e : Scheme.Etale.mk j ≅ (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj
          (Scheme.Etale.mk (𝟙 U)) :=
        MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
       NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op)
         (fun φ ↦ (φ.hom.naturality e.inv.op).symm)).symm

/-- The zero section is the published affine-space closed immersion.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
instance coordinateBoundaryZeroClosed (Y : Scheme.{u}) : IsClosedImmersion (zeroSection Y) :=
  inferInstanceAs (IsClosedImmersion (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y))

/-- The coordinate open is the actual basic-open immersion.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
instance coordinateBoundaryOpen (Y : Scheme.{u}) : IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion ((Line Y).basicOpen (coordinate Y)).ι)

/-- The ordinary degree-zero etale coefficient complex.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateEtaleInput (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.twistEtale h T)

/-- The exact small pro-etale image of the ordinary input.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateProInput (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj
    (P.coordinateEtaleInput h T)

/-- Canonical bounded-below derived localization, with no finiteness assumption on X.
Source: Milne, Section 9; Stacks 08FI
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateOpenDerivedIso (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).mapDerivedCategoryPlus ⋙
        (Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) U).rightDerivedFunctorPlus ≅
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk j))).rightDerivedFunctorPlus :=
  letI := (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) j).preservesInjectiveObjects_of_preservesFiniteLimits
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)).symm _ ≪≫
    Functor.rightDerivedFunctorPlusCompIso' _ _ (P.coordinateOpenSectionsIso j)

/-- Read the actual etale coordinate class as evaluation on the complement object.
The open coefficient inverse is the inverse of the pure-tensor pullback map, and the
open-site identification is the unique isomorphism over X.
Source: Milne, Theorem 9.4; blueprint affine-line geometric-fibre sentence
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateEtaleOpenClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (eU : Scheme.Etale.mk (openImmersion Y) ≅
      Scheme.Etale.mk (zeroSection Y).openComplement.ι) :
    (Sheaf.sectionHypercohomologyFunctor (Line Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).obj
        (P.coordinateEtaleInput h (Line Y)) :=
  let j := openImmersion Y
  let E := Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured Y)
  letI := P.isIso_twistEtalePullback h j
    (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
  let b := (DerivedCategory.Plus.singleFunctor _ 0).map
      (inv (P.twistEtalePullback h j)) ≫
    (Functor.mapDerivedCategoryPlusSingleFunctor
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j) 0).inv.app
        (P.twistEtale h (Line Y))
  let x := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
      (E.rightDerivedFunctorPlus.map b ≫
        (P.coordinateOpenDerivedIso j).hom.app (P.coordinateEtaleInput h (Line Y)))
    (P.coordinateClassSection (Punctured Y) (P.twistEtale h (Punctured Y))
      (P.kummerEtale h (Punctured Y)
        (P.exponent_isUnit (Punctured Y) (puncturedProjection Y ≫ a)) (coordinateUnit Y)))
  (Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorPlusNatIso
      (F := sheafToPresheaf (Line Y).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (openImmersion Y))))
      (G := sheafToPresheaf (Line Y).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (zeroSection Y).openComplement.ι)))
      ((sheafSections (Line Y).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)).mapIso eU.op).symm)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1)).hom.app
      (P.coordinateEtaleInput h (Line Y)) x

/-- Normalized data for the coordinate boundary on the two sites. The complement is
identified over the line, both boundaries have the snake sign, and both Hom
identifications have the evaluation-at-one normalization of supportedHom_pullback.
Source: Milne, Theorem 9.4 and Example 9.5; blueprint geometric-fibre sentence
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
structure CoordinateBoundaryModel (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) where
  complementIso : Scheme.Etale.mk (openImmersion Y) ≅
    Scheme.Etale.mk (zeroSection Y).openComplement.ι
  boundaryEtale : Sheaf.SupportSequenceBoundary (Line Y).smallEtaleTopology
    (ModuleCat.{u + 1} P.Coefficient) (Etale.supportRestrictionArrow (zeroSection Y)) ⊤
  boundaryPro : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y))
    (ModuleCat.{u + 1} P.Coefficient) (ProEtale.supportRestrictionArrow (zeroSection Y)) ⊤
  etale_normalized : supportBoundaryNormalization (Line Y).smallEtaleTopology P.Coefficient
    (Etale.supportRestrictionArrow (zeroSection Y)) boundaryEtale
  pro_normalized : supportBoundaryNormalization (Scheme.ProEt.topology (Line Y)) P.Coefficient
    (ProEtale.supportRestrictionArrow (zeroSection Y)) boundaryPro
  chiEtale : (etaleSupportHomPair P (zeroSection Y)).Identification
  chiPro : (proEtaleSupportHomPair P (zeroSection Y)).Identification

/-- The pro-etale open class is the canonical comparison image of the ordinary
Kummer class, through the actual root-tensor coefficient identification.
Source: affine-line datum, final comparison paragraph
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateBoundaryModel.openProClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}} (D : CoordinateBoundaryModel P Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y))
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1).obj
        (P.coordinateProInput h (Line Y)) :=
  (ProEtale.finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
    (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).app
      (P.coordinateEtaleInput h (Line Y)) (P.coordinateEtaleOpenClass h Y a D.complementIso)

/-- The actual ordinary supported coordinate boundary, not a chosen generator.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateBoundaryModel.alphaEtale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}} (D : CoordinateBoundaryModel P Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    (etaleSupportHomPair P (zeroSection Y)).group (P.coordinateEtaleInput h (Line Y)) 2 :=
  (D.boundaryEtale 1).app ⟨P.coordinateEtaleInput h (Line Y), trivial⟩
    (P.coordinateEtaleOpenClass h Y a D.complementIso)

/-- The same supported boundary on the small pro-etale site, with the same sign.
Source: Milne, Theorem 9.4; blueprint site refinement
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateBoundaryModel.alphaPro (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}} (D : CoordinateBoundaryModel P Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    (proEtaleSupportHomPair P (zeroSection Y)).group (P.coordinateProInput h (Line Y)) 2 :=
  (D.boundaryPro 1).app ⟨P.coordinateProInput h (Line Y), trivial⟩ (D.openProClass P h a)

/-- The existing affine-space map, with domain and codomain named by the datum.
Source: affine-line base change
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateLineMap {T Y : Scheme.{u}} (g : T ⟶ Y) : Line T ⟶ Line Y :=
  AffineSpace.map (ULift.{u} (Fin 1)) g

/-- The etale coefficient pullback, using the single-complex and root-tensor maps.
This helper is defined for every scheme morphism, including non-finite-type ones.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateEtaleCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T S : Scheme.{u}} (f : T ⟶ S) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategoryPlus.obj
      (P.coordinateEtaleInput h S) ⟶ P.coordinateEtaleInput h T :=
  (Functor.mapDerivedCategoryPlusSingleFunctor
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f) 0).hom.app (P.twistEtale h S) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map (P.twistEtalePullback h f)

/-- The pro-etale coefficient map, through the canonical comparison of inverse images.
Source: affine-line datum, site comparison
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateProCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T S : Scheme.{u}} (f : T ⟶ S) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategoryPlus.obj
      (P.coordinateProInput h S) ⟶ P.coordinateProInput h T :=
  (supportHomDerivedComparison P f).inv.app (P.coordinateEtaleInput h S) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.map
      (P.coordinateEtaleCoefficientPullback h f)

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.SupportHomPair

variable {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
  {B : S.Site ⥤ T.Site} [hB : B.IsContinuous S.topology T.topology]
  {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
    Sheaf T.topology (ModuleCat.{u + 1} A)}
  {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- Derived support pullback followed by the specified coefficient identification.
This uses Transport.derivedMap, whose kernel inclusion fixes the underived pullback.
Source: Milne, Section 9, functoriality of supported sections
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def Transport.coefficientGroupMap (e : Transport S T B L adj)
    {K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory.Plus (Sheaf T.topology (ModuleCat.{u + 1} A))}
    (b : L.mapDerivedCategoryPlus.obj K ⟶ K') (a : ℤ) : S.group K a ⟶ T.group K' a :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
      (e.derivedMap.app K) ≫
    (Sheaf.supportHypercohomologyFunctor T.topology
      (ModuleCat.{u + 1} A) T.restriction a).map b

/-- Exact inverse image of the derived Hom, precomposed with c inverse and then
postcomposed with the coefficient comparison and its canonical shift.
Source: Milne, Ext description and closed exchange
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def Transport.coefficientHomMap (e : Transport S T B L adj)
    {K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory.Plus (Sheaf T.topology (ModuleCat.{u + 1} A))}
    (b : L.mapDerivedCategoryPlus.obj K ⟶ K') (a : ℤ)
    (f : S.derivedHom K a) : T.derivedHom K' a :=
  e.homMap K a f ≫ (DerivedCategory.Plus.ι.map b)⟦a⟧'

/-- The two coefficient-adjusted compatibility equalities for specified classes.
Source: Milne, Theorem 9.4 and Ext description
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def Transport.CoefficientCompatible (e : Transport S T B L adj)
    (chi : S.Identification) (chi' : T.Identification)
    {K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory.Plus (Sheaf T.topology (ModuleCat.{u + 1} A))}
    (b : L.mapDerivedCategoryPlus.obj K ⟶ K') (a : ℤ)
    (x : S.group K a) (y : T.group K' a) : Prop :=
  e.coefficientGroupMap b a x = y ∧
    chi'.chi K' a y = e.coefficientHomMap b a (chi.chi K a x)

end AlgebraicGeometry.SupportHomPair

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary etale model of the coordinate class, with the unchanged exponent
and pure-tensor coefficient morphism of the datum.
Source: affine-line datum (blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def coordinateEtaleKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :=
  P.kummerEtale h (Punctured Y)
    (P.exponent_isUnit (Punctured Y) (puncturedProjection Y ≫ a)) (coordinateUnit Y)

/-- Ordinary and pro-etale pullback of the actual coordinate Kummer classes.
Source: affine-line datum and its geometric fibre
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateKummerPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  Abelian.Ext.coordinatePullbackIdentity
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
    (P.coordinateEtaleKummer h Y a) (P.coordinateEtaleKummer h T (g ≫ a))
    ((Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
        (ModuleCat.of P.Coefficient P.Coefficient))
    (P.twistEtalePullback h (puncturedMap g)) ∧
  Abelian.Ext.coordinatePullbackIdentity
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
    (P.coordinateKummer h Y a) (P.coordinateKummer h T (g ≫ a))
    ((ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
        (P.constantEtale (Punctured Y)) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured T)).map
        ((Scheme.upperStarConstantSheafIso
          (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
            (ModuleCat.of P.Coefficient P.Coefficient)))
    ((ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
        (P.twistEtale h (Punctured Y)) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured T)).map
        (P.twistEtalePullback h (puncturedMap g)))

/-- Both supported boundary equalities and both normalized derived-Hom equalities.
The support maps are the recorded right-derived kernel maps, and the Hom maps use
closed exchange inverses and canonical shifts.
Source: Milne, Theorem 9.4; supported-Hom pullback
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateBoundaryPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (D : CoordinateBoundaryModel P Y) (D' : CoordinateBoundaryModel P T)
    (e : etaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (coordinateLineMap g))
    (p : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (coordinateLineMap g)) : Prop :=
  e.CoefficientCompatible
    (hB := Etale.isContinuous_overPullback (coordinateLineMap g))
    D.chiEtale D'.chiEtale
    (P.coordinateEtaleCoefficientPullback h (coordinateLineMap g)) 2
    (D.alphaEtale P h a) (D'.alphaEtale P h (g ≫ a)) ∧
  p.CoefficientCompatible
    (hB := Scheme.ProEt.isContinuous_overPullback (coordinateLineMap g))
    D.chiPro D'.chiPro
    (P.coordinateProCoefficientPullback h (coordinateLineMap g)) 2
    (D.alphaPro P h a) (D'.alphaPro P h (g ≫ a))

/-- Site comparison of the actual boundary and its supported-Hom representative.
Source: blueprint site refinement; normalized support comparison
(blueprint: lem-pur-coordinate-boundary-geometric-pullback). -/
def CoordinateBoundarySiteAgreement (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) (D : CoordinateBoundaryModel P Y)
    (v : siteSupportHomTransport P (zeroSection Y)) : Prop :=
  v.CoefficientCompatible (hB := Scheme.isContinuous_toProEt (Line Y))
    D.chiEtale D.chiPro (𝟙 (P.coordinateProInput h (Line Y))) 2
    (D.alphaEtale P h a) (D.alphaPro P h a)

/-- Coordinate Kummer boundaries and their normalized supported-Hom representatives
commute with every geometric pullback. In coefficientGroupMap, the map is the
right-derived support-kernel pullback. In coefficientHomMap it is exact inverse image,
precomposition by the canonical supported-constant comparison inverse, and the
canonical coefficient and shift comparisons. No finite-type condition is imposed on
Spec Omega. Both coordinate classes use the same P.exponent and rootCoefficientMap.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-affine-line-orientation.proof.md, geometric-fibre sentence; Milne, Theorem 9.4
and Example 9.5 (blueprint: lem-pur-coordinate-boundary-geometric-pullback).

Proof, following the four steps of the node:
1. On every affine chart the base changes of R[t], R[t,t^-1] and R[t]/(t) are
Omega[t], Omega[t,t^-1] and Omega. This gives Cartesian zero-section and open squares,
and pulls the coordinate to the coordinate without any finite-type condition on Omega.
2. Relative Kummer coefficient normalization gives naturality of the actual ordinary
boundary followed by z mapping to z tensor 1. The same exponent m=ell^(n/e) and the
same scalar one are used after pullback. Relative Kummer site normalization transports
these exact classes through the canonical twist and site comparisons.
3. Functoriality of thm-pur-with-support-exactness for these two pairs gives pullback
of alpha equal to the boundary of the pulled-back coordinate class. The injective
snake normalization fixes the sign. The identical argument applies to the finite
coefficient small pro-etale images, and their comparison ladder identifies boundaries.
4. Apply lem-pur-supported-hom-pullback in degree 2 to F in degree zero. Its normalized
Hom transport gives chi(alpha')=h^*chi(alpha) composed with c inverse, through the
coefficient and shift comparisons. Its two site comparisons and coherence square
identify the etale and pro-etale representatives. Thus the result identifies the
actual coordinate boundary with its original coefficient map, rather than a generator. -/
theorem coordinate_boundary_geometric_pullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ D : CoordinateBoundaryModel P Y,
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (CommRingCat.of Ω) ⟶ Y),
    ∃ D' : CoordinateBoundaryModel P (Spec (CommRingCat.of Ω)),
    ∃ e : etaleSupportHomTransport P (zeroSection Y)
      (zeroSection (Spec (CommRingCat.of Ω))) (coordinateLineMap g),
    ∃ p : proEtaleSupportHomTransport P (zeroSection Y)
      (zeroSection (Spec (CommRingCat.of Ω))) (coordinateLineMap g),
    ∃ v : siteSupportHomTransport P (zeroSection Y),
    ∃ v' : siteSupportHomTransport P (zeroSection (Spec (CommRingCat.of Ω))),
      P.CoordinateKummerPullback h g a ∧
      P.CoordinateBoundaryPullback h g a D D' e p ∧
      P.CoordinateBoundarySiteAgreement h a D v ∧
      P.CoordinateBoundarySiteAgreement h (g ≫ a) D' v' ∧
      SupportHomSquareCoherent P (zeroSection Y) (zeroSection (Spec (CommRingCat.of Ω)))
        (coordinateLineMap g) e p v v' := by
  sorry

end WeilConjectures.PurityFiniteSetting
