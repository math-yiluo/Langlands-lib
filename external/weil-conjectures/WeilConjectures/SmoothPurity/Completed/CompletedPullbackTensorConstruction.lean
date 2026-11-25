/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorIntegralConstruction
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalization
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonCanonicalIdentification
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonScalarLimitImage
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorProofImplementations
import WeilConjectures.SmoothPurity.Finite.FiniteQuotientPullbackDescent
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorQuotientRepresentatives
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorComparison
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Integral and rational pullback/tensor constructions

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tensor-construction).

## Main definitions

* `canonicalIntegralPullbackTensor` is the prescribed comparison.
* The helper declarations fix its representative normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section QuotientCompatibility
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Cache additive finite inverse image with the explicitly sized coefficient ring.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
instance pullbackTensorFiniteAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
  sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f

/-- Cache the actual quotient extension's published additive structure.
Source: Stacks 06YY (blueprint: def-pur-completed-pullback-tensor-construction). -/
instance pullbackTensorQuotientAdditive (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E W h).Additive :=
  coefficientFiniteQuotientExtensionAdditive l E W h

/-- The quotient/pullback comparison preserves the two actual adjunction units.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: tensor association and constant inverse image identify the two ordinary
functors. Both iterated units send x to 1 tensor f*x. Their equality determines
the comparison on the generators of the two left adjoints, proving uniqueness. -/
theorem pullbackTensorQuotientOrdinary_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x) := by
  exact completedPullbackTensorQuotientOrdinary l E f h

/-- The unit-normalized ordinary quotient/pullback comparison.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotientOrdinary_existsUnique l E f h)

attribute [local irreducible] pullbackTensorQuotientOrdinary

/-- Finite constant-coefficient inverse image preserves K-flat complexes.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: use the constant-ring pullback/tensor comparison and exact inverse image.
Apply the K-flat criterion, or transport the recorded ringed pullback preservation
along the unit-normalized finite realization. No coefficient Tor-dimension is used. -/
theorem pullbackTensorFiniteGood {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact completedPullbackTensorFiniteGood l E f n P hP

/-- The ordinary quotient/pullback comparison on complexes, with both composition
identifications and all additive instances supplied explicitly.
Source: Stacks 06YY, 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicPullback
      (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
    (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
      (sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    letI := coefficientFiniteQuotientExtensionAdditive l E X h
    letI := coefficientFiniteQuotientExtensionAdditive l E Y h
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (m + 1)) f
    letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    exact Functor.mapHomologicalComplexCompIso
      (F := sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f)
      (G := coefficientFiniteQuotientExtension l E X h) (Iso.refl _) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex
        (F := sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
          coefficientFiniteQuotientExtension l E X h)
        (G := coefficientFiniteQuotientExtension l E Y h ⋙
          sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
        (pullbackTensorQuotientOrdinary l E f h) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := coefficientFiniteQuotientExtension l E Y h)
        (G := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
        (Iso.refl _) (.up ℤ)).symm

attribute [local irreducible] pullbackTensorQuotientComplex

/-- The full K-flat normalization of quotient pullback, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f) : Prop :=
  ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (pullbackTensorFiniteGood l E f m P hP)).hom ≫
          DerivedCategory.Q.map ((pullbackTensorQuotientComplex l E f h).hom.app P)

attribute [local irreducible] pullbackTensorQuotientNormalization

section QuotientDescent
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived

/-- The quotient/pullback isomorphism is fixed by its full K-flat counit square.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: the preceding ordinary comparison on K-flat representatives identifies
the two derived functors. The universal quotient counit and exact-pullback
factorization give precisely this square. K-flat localization determines a
unique natural isomorphism from the displayed squares. -/
theorem pullbackTensorQuotient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      pullbackTensorQuotientNormalization l E f h e := by
  unfold pullbackTensorQuotientNormalization
  exact finiteQuotientPullbackDescent l E f h
    (pullbackTensorQuotientComplex l E f h) (pullbackTensorFiniteGood l E f m)

end QuotientDescent

/-- The derived quotient/pullback comparison with its fixed K-flat normalization.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotient_existsUnique l E f h)

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] finitePullbackTensorConstructionIso
  finitePullbackTensorConstruction coefficientFiniteQuotientDerived
  coefficientFiniteQuotientModel pullbackTensorQuotient

private theorem pullbackTensorQuotientComplex_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ) :
    ((pullbackTensorQuotientComplex l E f h).hom.app P).f i =
      (pullbackTensorQuotientOrdinary l E f h).hom.app (P.X i) := by
  unfold pullbackTensorQuotientComplex
  simp

-- Give the quotient tensorator its intrinsic source and target once. This avoids
-- reducing the entire chosen evaluation calculus at every whiskering below.
private def quotientTensorForDescent (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    finiteIntrinsicDerivedTensor l E W m ⋙ coefficientFiniteQuotientDerived l E W h ≅
      (coefficientFiniteQuotientDerived l E W h).prod
        (coefficientFiniteQuotientDerived l E W h) ⋙ finiteIntrinsicDerivedTensor l E W n :=
  (pullbackTensorCalculus l E W).quotientCalculus.tensor h

attribute [local irreducible] quotientTensorForDescent

private theorem quotientTensorForDescent_app (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory W (finiteCoefficientRing l E (m + 1))) :
    (quotientTensorForDescent l E W h).hom.app (M, N) =
      ((pullbackTensorCalculus l E W).quotientCalculus.tensor h).hom.app (M, N) := by
  unfold quotientTensorForDescent
  rfl

-- This descent only uses naturality and resolving isomorphisms. Keeping it
-- abstract avoids normalizing concrete derived-category functors in its proof.
private theorem quotientTensor_square_of_resolutions
    {A B C D K : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* K]
    (q : K ⥤ A) (P : ObjectProperty K)
    (res : ∀ M : A, ∃ U : K, P U ∧ Nonempty (q.obj U ≅ M))
    (Fm : A ⥤ B) (Fn : C ⥤ D) (QX : B ⥤ D) (QY : A ⥤ C)
    (Tm : A × A ⥤ A) (TX : B × B ⥤ B) (TY : C × C ⥤ C) (Tn : D × D ⥤ D)
    (μm : Tm ⋙ Fm ≅ Fm.prod Fm ⋙ TX) (μn : TY ⋙ Fn ≅ Fn.prod Fn ⋙ Tn)
    (τX : TX ⋙ QX ≅ QX.prod QX ⋙ Tn) (τY : Tm ⋙ QY ≅ QY.prod QY ⋙ TY)
    (e : Fm ⋙ QX ≅ QY ⋙ Fn)
    (h : ∀ U V : K, P U → P V →
      QX.map (μm.hom.app (q.obj U, q.obj V)) ≫
        τX.hom.app (Fm.obj (q.obj U), Fm.obj (q.obj V)) ≫
        Tn.map (Prod.mkHom (e.hom.app (q.obj U)) (e.hom.app (q.obj V))) =
      e.hom.app (Tm.obj (q.obj U, q.obj V)) ≫
        Fn.map (τY.hom.app (q.obj U, q.obj V)) ≫
        μn.hom.app (QY.obj (q.obj U), QY.obj (q.obj V)))
    (M N : A) :
    QX.map (μm.hom.app (M, N)) ≫ τX.hom.app (Fm.obj M, Fm.obj N) ≫
        Tn.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (Tm.obj (M, N)) ≫ Fn.map (τY.hom.app (M, N)) ≫
        μn.hom.app (QY.obj M, QY.obj N) := by
  let a : Tm ⋙ Fm ⋙ QX ⟶ (QY ⋙ Fn).prod (QY ⋙ Fn) ⋙ Tn :=
    Functor.whiskerRight μm.hom QX ≫
      Functor.whiskerLeft (Fm.prod Fm) τX.hom ≫
      Functor.whiskerRight (NatTrans.prod e.hom e.hom) Tn
  let b : Tm ⋙ Fm ⋙ QX ⟶ (QY ⋙ Fn).prod (QY ⋙ Fn) ⋙ Tn :=
    Functor.whiskerLeft Tm e.hom ≫ Functor.whiskerRight τY.hom Fn ≫
      Functor.whiskerLeft (QY.prod QY) μn.hom
  have hab : a = b := tensorNatTrans_ext_resolving q P res a b (by
    intro U V hU hV
    exact h U V hU hV)
  exact NatTrans.congr_app hab (M, N)

/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: on flat-term K-flat representatives, the representative lemma computes both
paths by the formula 1 tensor f*(x tensor y) mapping to f*(1 tensor x) tensor
f*(1 tensor y). The ordinary unit, cochain degree, and derived counit equations
supply its normalization hypotheses. The two paths are natural transformations.
Every derived object is isomorphic to a localized flat-term K-flat complex;
naturality along these resolving isomorphisms extends the square to all inputs. -/
theorem canonicalFinitePullbackTensor_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))) :
    (coefficientFiniteQuotientDerived l E X h).map
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorQuotient l E f h).hom.app M)
          ((pullbackTensorQuotient l E f h).hom.app N)) =
    (pullbackTensorQuotient l E f h).hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom := by
  have hsq := quotientTensor_square_of_resolutions
    (A := proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1)))
    (B := proEtaleDerivedCategory X (finiteCoefficientRing l E (m + 1)))
    (C := proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (D := proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))
    (DerivedCategory.Q (C := normalizedDVRModules l E Y m))
    (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m))
    (finiteTensor_flat_representatives l E Y m)
    (finiteDerivedPullback l E m f) (finiteDerivedPullback l E n f)
    (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E Y h)
    (finiteIntrinsicDerivedTensor l E Y m) (finiteIntrinsicDerivedTensor l E X m)
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    (finitePullbackTensorConstructionIso l E f m) (finitePullbackTensorConstructionIso l E f n)
    (quotientTensorForDescent l E X h) (quotientTensorForDescent l E Y h)
    (pullbackTensorQuotient l E f h) (by
      intro P Q hP hQ
      have hr := finitePullbackTensor_quotient_representatives l E f h
        (pullbackTensorQuotientOrdinary l E f h)
        (by
          unfold pullbackTensorQuotientOrdinary pullbackTensorUniqueChoice
          exact (pullbackTensorQuotientOrdinary_existsUnique l E f h).exists.choose_spec)
        (pullbackTensorQuotientComplex l E f h)
        (pullbackTensorQuotientComplex_f l E f h)
        (pullbackTensorFiniteGood l E f m) (pullbackTensorQuotient l E f h)
        (by
          unfold pullbackTensorQuotient pullbackTensorUniqueChoice
          simpa only [pullbackTensorQuotientNormalization] using
            (pullbackTensorQuotient_existsUnique l E f h).exists.choose_spec) P Q hP hQ
      dsimp only [Functor.comp_obj] at hr ⊢
      simp only [finiteEvaluationComparison_app, quotientTensorForDescent_app] at hr ⊢
      exact hr) M N
  unfold canonicalFinitePullbackTensor
  dsimp only [Functor.comp_obj] at hsq ⊢
  simp only [finiteEvaluationComparison_app, quotientTensorForDescent_app] at hsq ⊢
  exact hsq
/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: on a flat K-flat pair the two routes carry 1 tensor f*(x tensor y)
to f*(1 tensor x) tensor f*(1 tensor y). The quotient tensor comparison is
normalized on these same generators. Totalize and use the quotient counits
and K-flat localization to obtain the displayed derived equation. -/
def canonicalFinitePullbackTensor_quotient_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))) :=
    (coefficientFiniteQuotientDerived l E X h).map
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorQuotient l E f h).hom.app M)
          ((pullbackTensorQuotient l E f h).hom.app N)) =
    (pullbackTensorQuotient l E f h).hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom
end QuotientCompatibility

section LocalizationComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Rationalization fixes the comparison arrow itself, not just its isomorphism class.
Source: blueprint scalar localization paragraph (blueprint:
def-pur-completed-pullback-tensor-construction).
Proof: apply the recorded localization functor to the integral comparison and its
inverse. Its object formula agrees with the rational operations. The localized
inverse identities make this an isomorphism; equality of homs determines it uniquely. -/
theorem canonicalRationalPullbackTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj (((@rationalDerivedTensor l _ E
      _ _ _ Y hY)).obj (M,N)) ≅
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).obj
          (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M, ((@rationalDerivedPullback l
            _ E _ _ _ X Y f hX hY)).obj N),
      HEq e.hom ((sfRationalConstructibleLocalization l E X).map
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj).hom) := by
  let T (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
  let F := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
  let e := (sfRationalConstructibleLocalization l E X).mapIso
    ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj)
  have hs : (rationalDerivedPullback l E f).obj
      ((rationalDerivedTensor l E Y).obj (M,N)) =
        (sfRationalConstructibleLocalization l E X).obj
          ((constructibleIntegralPullback l E f).obj
            ((constructibleIntegralTensor l E Y).obj (M.obj,N.obj))) := by
    dsimp only [rationalDerivedPullback, rationalDerivedTensor]
    rw [F, T Y (M,N)]
    rfl
  have ht : (rationalDerivedTensor l E X).obj
      ((rationalDerivedPullback l E f).obj M, (rationalDerivedPullback l E f).obj N) =
        (sfRationalConstructibleLocalization l E X).obj
          ((constructibleIntegralTensor l E X).obj
            ((constructibleIntegralPullback l E f).obj M.obj,
              (constructibleIntegralPullback l E f).obj N.obj)) := by
    dsimp only [rationalDerivedPullback, rationalDerivedTensor]
    rw [T X, F M, F N]
    rfl
  refine ⟨eqToIso hs ≪≫ e ≪≫ (eqToIso ht).symm, ?_, ?_⟩
  · apply (conj_eqToHom_iff_heq _ e.hom hs ht).mp
    rfl
  · intro e' he'
    apply Iso.ext
    apply eq_of_heq
    exact he'.trans ((conj_eqToHom_iff_heq _ e.hom hs ht).mp rfl).symm

/-- The localized canonical integral comparison.
Source: blueprint scalar localization paragraph (blueprint:
def-pur-completed-pullback-tensor-construction). -/
def canonicalRationalPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@RationalPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  pullbackTensorUniqueChoice
    ((@canonicalRationalPullbackTensor_existsUnique l _ E _ _ _ X Y f hX hY) M N)
end LocalizationComparison

section CommonComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The rational comparison in any common finite stage, with all four prescribed
pullback/tensor transition comparisons included.
Source: blueprint common-stage paragraph
(blueprint: def-pur-completed-pullback-tensor-construction).
-/
def pullbackTensorAtCommonStage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageTensorObject l Ω Y P Q).stage ≤ L) :
    (commonStagePullbackObject l Ω f (commonStageTensorObject l Ω Y P Q)).toStage h ≅
      (commonStageTensorObject l Ω X
        (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)).toStage h :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω Y P Q) L h ≪≫
  ((@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X Y f
    hX hY)).mapIso
    (commonStageTensorComparison l Ω Y P Q L h) ≪≫
  (@canonicalRationalPullbackTensor l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _
    _ X Y f hX hY) _ _ ≪≫
  ((@rationalDerivedTensor l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
    hX)).mapIso
    (Iso.prod (commonStagePullbackComparison l Ω f P L
      (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)).symm
      (commonStagePullbackComparison l Ω f Q L
        (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)).symm) ≪≫
  (commonStageTensorComparison l Ω X
    (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q) L h).symm

end CommonComparison

section ScalarCompatibility
attribute [local irreducible] pullbackTensorCalculus
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-construction).
Proof: use one flat K-flat representative pair and the actual quotient models
for O_L/varpi_L^m. Both paths send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The equality respects every quotient map;
apply the actual coherent-system limit and its normalized substitutions. -/
theorem canonicalIntegralPullbackTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).map ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (integralTensorScalarComparison l E L ι X
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
      ((@constructibleIntegralTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom (integralPullbackScalarComparison l E L ι f M).hom
          (integralPullbackScalarComparison l E L ι f N).hom) =
    (integralPullbackScalarComparison l E L ι f
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
      ((@constructibleIntegralPullback l _ L _ _ _ X Y f hX hY)).map
        (integralTensorScalarComparison l E L ι Y M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj N)).hom := by
  classical
  let q := integralOperationsGoodLocalization l E Y
  let weak := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  have : q.IsLocalization weak := integralOperationsGoodLocalization_isLocalization l E Y
  have : q.EssSurj := Localization.essSurj q weak
  let inputs : Fin 3 → sfIntegralConstructibleCategory l E Y := ![M, N, M]
  let P (i : Fin 3) := q.objPreimage (inputs i).obj
  let φ (i : Fin 3) : DerivedCategory.Q.obj (P i).obj ≅ (inputs i).obj :=
    q.objObjPreimageIso (inputs i).obj
  obtain ⟨good, invertible, _hnorm, _hpres, _hnatural⟩ :=
    CompletedQuotient.completedComparisonQuotientNormalization l E (𝟙 X) f inputs P φ
  have hcanonical := (CompletedQuotient.completedComparisonCanonicalIdentification
    l E L (𝟙 X) f inputs P φ good invertible).1
  have hscalar := (CompletedQuotient.completedComparisonScalarLimitImage
    l E L ι (𝟙 X) f inputs P φ good invertible).2
  unfold CompletedQuotient.ScalarLimitImage at hscalar
  obtain ⟨ρX, ρY, SX, SY, goodL, invertibleL, _hsquare, hcanonicalL, hpaths⟩ := hscalar
  have h := hpaths (CompletedQuotient.scalarLeft l E L ι f
    (CompletedQuotient.quotient l E (P 0).obj)
    (CompletedQuotient.quotient l E (P 1).obj)).hom (Or.inl rfl)
  rw [hcanonical, hcanonicalL] at h
  apply ObjectProperty.hom_ext
  exact h.2.symm.trans h.1

section RationalScalarProof

private theorem comparisonMapHEq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C}
    {a : X ⟶ Y} {b : X' ⟶ Y'} (h : HEq a b) (hx : X = X') (hy : Y = Y') :
    HEq (F.map a) (F.map b) := by
  cases hx; cases hy; cases h
  rfl

private theorem comparisonApplyHEq {A : Sort*} {B : A → Sort*}
    {a b : A} (h : a = b) (g : ∀ a, B a) : HEq (g a) (g b) := by
  cases h
  rfl

private theorem comparisonProdHEq {C : Type*} [Category* C]
    {A B A' B' D E D' E' : C}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : D ⟶ E} {b' : D' ⟶ E'}
    (h : HEq a a') (h' : HEq b b')
    (ha : A = A') (hb : B = B') (hd : D = D') (he : E = E') :
    HEq (Prod.mkHom a b) (Prod.mkHom a' b') := by
  cases ha; cases hb; cases hd; cases he
  cases h; cases h'
  rfl

private theorem comparisonLocalizationMapHEq
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) {A B : C} (a : A ⟶ B) :
    HEq ((ScalarLocalization.localization R C p).map a)
      ((1 : Localization.Away p) ⊗ₜ[R] a) := by
  rfl

attribute [local irreducible] canonicalIntegralPullbackTensor
attribute [local irreducible] integralPullbackScalarComparison integralTensorScalarComparison
  constructibleIntegralPullback constructibleIntegralTensor sfConstructibleIntegralScalarExtension

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-construction).
Proof: localize the preceding integral equality. Each operation comparison is
by definition the image of its integral component. Bilinearity then gives the
same square on every rational input, including identity scalar extensions. -/
theorem canonicalRationalPullbackTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (rationalTensorScalarComparison l E L ι X).hom.app
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,((@rationalDerivedPullback l _ E
          _ _ _ X Y f hX hY)).obj N) ≫
      ((@rationalDerivedTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom ((rationalPullbackScalarComparison l E L ι f).hom.app M)
          ((rationalPullbackScalarComparison l E L ι f).hom.app N)) =
    (rationalPullbackScalarComparison l E L ι f).hom.app
      (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) ≫
      ((@rationalDerivedPullback l _ L _ _ _ X Y f hX hY)).map
        ((rationalTensorScalarComparison l E L ι Y).hom.app (M,N)) ≫
      ((@canonicalRationalPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)).hom := by
  let Q (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u}) :=
    sfRationalConstructibleLocalization l K W
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let s (W : Scheme.{u}) := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let F (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] := constructibleIntegralPullback l K f
  let r (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] := rationalDerivedPullback l K f
  let T (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)] := constructibleIntegralTensor l K W
  let t (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)] := rationalDerivedTensor l K W
  have hs (W : Scheme.{u}) (A : sfRationalConstructibleCategory l E W) :
      (s W).obj A = (Q L W).obj ((S W).obj A.obj) :=
    sfRationalScalarExtension_obj l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A
  have hr (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (A : sfRationalConstructibleCategory l K Y) :
      (r K).obj A = (Q K X).obj ((F K).obj A.obj) :=
    by simpa only [r, F, Q, rationalDerivedPullback,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l K f).exists.choose_spec.2.1 A
  have ht (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)]
      (AB : sfRationalConstructibleCategory l K W × sfRationalConstructibleCategory l K W) :
      (t K W).obj AB = (Q K W).obj ((T K W).obj (AB.1.obj, AB.2.obj)) :=
    by simpa only [t, T, Q, rationalDerivedTensor,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l K W).exists.choose_spec.1 AB
  have ms (W : Scheme.{u}) {A B : sfIntegralConstructibleCategory l E W} (a : A ⟶ B) :
      HEq ((s W).map ((Q E W).map a)) ((Q L W).map ((S W).map a)) := by
    have h := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A B a 1
    simp only [map_one] at h
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((S W).map a)
    convert h.trans hm.symm using 0
    rfl
  have mr {A B : sfIntegralConstructibleCategory l L Y} (a : A ⟶ B) :
      HEq ((r L).map ((Q L Y).map a)) ((Q L X).map ((F L).map a)) := by
    have h := (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.2.2 A B a 1
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((F L).map a)
    convert h.trans hm.symm using 0
    rfl
  have mt {A A' B B' : sfIntegralConstructibleCategory l L X}
      (a : A ⟶ A') (b : B ⟶ B') :
      HEq ((t L X).map (Prod.mkHom ((Q L X).map a) ((Q L X).map b)))
        ((Q L X).map ((T L X).map (Prod.mkHom a b))) := by
    obtain ⟨β, hβ, hp⟩ := (rationalDerivedTensor_existsUnique l L X).exists.choose_spec.2
      ((Q L X).obj A) ((Q L X).obj A') ((Q L X).obj B) ((Q L X).obj B')
    dsimp only [t, rationalDerivedTensor]
    rw [hβ]
    have h := hp a b 1 1
    simp only [one_mul] at h
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((T L X).map (Prod.mkHom a b))
    convert h.trans hm.symm using 0
    rfl
  have hmu (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (A B : sfRationalConstructibleCategory l K Y) :
      HEq (canonicalRationalPullbackTensor l K f A B).hom
        ((Q K X).map (canonicalIntegralPullbackTensor l K f A.obj B.obj).hom) :=
    by simpa only [canonicalRationalPullbackTensor, pullbackTensorUniqueChoice, Q] using
      (canonicalRationalPullbackTensor_existsUnique l K f A B).exists.choose_spec
  have hp (A : sfRationalConstructibleCategory l E Y) :
      HEq ((rationalPullbackScalarComparison l E L ι f).hom.app A)
        ((Q L X).map (integralPullbackScalarComparison l E L ι f A.obj).hom) :=
    by simpa only [rationalPullbackScalarComparison, Q] using
      (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec A
  have hq (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (A B : sfRationalConstructibleCategory l E W) :
      HEq ((rationalTensorScalarComparison l E L ι W).hom.app (A,B))
        ((Q L W).map (integralTensorScalarComparison l E L ι W A.obj B.obj).hom) :=
    by simpa only [rationalTensorScalarComparison, Q] using
      (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec A B
  -- The six vertices have the prescribed integral object formulas.
  have hsrc : (s X).obj ((r E).obj ((t E Y).obj (M,N))) =
      (Q L X).obj ((S X).obj ((F E).obj ((T E Y).obj (M.obj,N.obj)))) := by
    rw [hs, hr, ht]
    rfl
  have hmid : (s X).obj ((t E X).obj ((r E).obj M,(r E).obj N)) =
      (Q L X).obj ((S X).obj ((T E X).obj ((F E).obj M.obj,(F E).obj N.obj))) := by
    rw [hs, ht, hr, hr]
    rfl
  have hmid' : (t L X).obj ((s X).obj ((r E).obj M),(s X).obj ((r E).obj N)) =
      (Q L X).obj ((T L X).obj ((S X).obj ((F E).obj M.obj),
        (S X).obj ((F E).obj N.obj))) := by
    rw [ht, hs, hs, hr, hr]
    rfl
  have htgt : (t L X).obj ((r L).obj ((s Y).obj M),(r L).obj ((s Y).obj N)) =
      (Q L X).obj ((T L X).obj ((F L).obj ((S Y).obj M.obj),
        (F L).obj ((S Y).obj N.obj))) := by
    rw [ht, hr, hr, hs, hs]
    rfl
  have hmidR : (r L).obj ((s Y).obj ((t E Y).obj (M,N))) =
      (Q L X).obj ((F L).obj ((S Y).obj ((T E Y).obj (M.obj,N.obj)))) := by
    rw [hr, hs, ht]
    rfl
  have hmidR' : (r L).obj ((t L Y).obj ((s Y).obj M,(s Y).obj N)) =
      (Q L X).obj ((F L).obj ((T L Y).obj ((S Y).obj M.obj,(S Y).obj N.obj))) := by
    rw [hr, ht, hs, hs]
    rfl
  -- Identify all six arrows with their integral localizations.
  have h1 := (comparisonMapHEq (s X) (hmu E M N)
    (by rw [hr, ht]; rfl) (by rw [ht, hr, hr]; rfl)).trans
      (ms X (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom)
  have h2 := (hq X ((r E).obj M) ((r E).obj N)).trans
    (comparisonApplyHEq (congrArg₂ Prod.mk (hr E M) (hr E N))
      (fun AB : sfRationalConstructibleCategory l E X ×
          sfRationalConstructibleCategory l E X ↦
        (Q L X).map (integralTensorScalarComparison l E L ι X AB.1.obj AB.2.obj).hom))
  have h3 := (comparisonMapHEq (t L X)
    (comparisonProdHEq (hp M) (hp N)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl))
    (congrArg₂ Prod.mk (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl))
    (congrArg₂ Prod.mk (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl))).trans
        (mt (integralPullbackScalarComparison l E L ι f M.obj).hom
          (integralPullbackScalarComparison l E L ι f N.obj).hom)
  have h4 := (hp ((t E Y).obj (M,N))).trans
    (comparisonApplyHEq (ht E Y (M,N))
      (fun A : sfRationalConstructibleCategory l E Y ↦
        (Q L X).map (integralPullbackScalarComparison l E L ι f A.obj).hom))
  have h5 := (comparisonMapHEq (r L) (hq Y M N) (by dsimp only [Functor.comp_obj]; rw [hs, ht]; rfl)
    (by dsimp only [Functor.comp_obj, Functor.prod_obj]; rw [ht, hs, hs]; rfl)).trans
      (mr (integralTensorScalarComparison l E L ι Y M.obj N.obj).hom)
  have h6 := (hmu L ((s Y).obj M) ((s Y).obj N)).trans
    (comparisonApplyHEq (congrArg₂ Prod.mk (hs Y M) (hs Y N))
      (fun AB : sfRationalConstructibleCategory l L Y ×
          sfRationalConstructibleCategory l L Y ↦
        (Q L X).map (canonicalIntegralPullbackTensor l L f AB.1.obj AB.2.obj).hom))
  -- Functoriality transports the integral square to the rational square.
  apply eq_of_heq
  exact (heq_comp hsrc hmid htgt h1 (heq_comp hmid hmid' htgt h2 h3)).trans
    ((heq_of_eq (by
      have h := congrArg (Q L X).map
        (canonicalIntegralPullbackTensor_scalar l E L ι f M.obj N.obj)
      simp only [Functor.map_comp] at h
      convert h using 0
      rfl)).trans
      (heq_comp hsrc hmidR htgt h4 (heq_comp hmidR hmidR' htgt h5 h6)).symm)

end RationalScalarProof

/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-construction).
Proof: use one flat K-flat representative pair and the actual quotient models
for O_L/varpi_L^m. Both paths send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The equality respects every quotient map;
apply the actual coherent-system limit and its normalized substitutions. -/
def canonicalIntegralPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalIntegralPullbackTensor_scalar l E L ι f M N)

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-construction).
Proof: localize the preceding integral equality. Each operation comparison is
by definition the image of its integral component. Bilinearity then gives the
same square on every rational input, including identity scalar extensions. -/
def canonicalRationalPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalRationalPullbackTensor_scalar l E L ι f M N)

end ScalarCompatibility

end WeilConjectures
