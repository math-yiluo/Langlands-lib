/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
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

/-! # K-flat models of the augmented derived DVR reduction tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence normalizedDVRKFlatComparison
  normalizedDVRResCompletedComp
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- The canonical size witness, registered only in this file. -/
abbrev normalizedDVRKFlatReductionModelLocal1 :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
attribute [local instance 4000] normalizedDVRKFlatReductionModelLocal1
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRKFlatReductionModelLocal2 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVRKFlatReductionModelLocal2
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRKFlatReductionModelLocal3 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVRKFlatReductionModelLocal3

local instance : Category.{max (t + 2) (u + 1)}
    (DerivedCategory (scalarReductionSource l E X)) := inferInstance

private theorem representativeComparison_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    IsIso (normalizedDVRKFlatComparison l E X n P) := by
  have := unrestrictedTowerCounit_isIso l E X n P hP
  unfold normalizedDVRKFlatComparison
  infer_instance

/-- The canonical K-flat augmented quotient tower computes the derived reduction
units and their quotient transitions, for an arbitrary derived object.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 03EK, 06YY and 06YL;
blueprint lemma-sp-tower-adjunction-foundation--2, final proof paragraph.
(blueprint: lem-coef-normalized-dvr-kflat-reduction-model).

Proof: choose a complex representing M and a K-flat resolution with flat terms.
The universal scalar-extension counit, invertible on that resolution, and the exact
restriction localization comparison give the isomorphisms a. Naturality transports
them from the representative to M. The normalized derived adjunction identifies its
unit, followed by this counit, with the localized ordinary tensor unit. This is the
first equation. For adjacent quotients form the finite-linear tensor map sending
b tensor x to rho(b) tensor x. Its adjoint is the smaller tensor unit, since rho(1)=1.
The derived adjunction and its counit compatibility therefore identify this map
with the displayed adjoint transition. After restriction its localization is exactly
the recorded integralTowerTransition: both maps have the same pure-tensor formula,
and uniqueness of sheafification proves their equality. These equations are unchanged
under the representative isomorphism. The isomorphism e is the localized resolution
map followed by the representative isomorphism; the comparison composes functor images
and universal counits.
Zero objects and the empty scheme obey the same formulas. -/
theorem normalizedDVR_kflat_reduction_model
    (adj : ∀ n : ℕ, scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n)
    (hunit : ∀ (n : ℕ) (P : CochainComplex (scalarReductionSource l E X) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted l E X) P →
      (adj n).unit.app (DerivedCategory.Q.obj P) ≫ normalizedDVRKFlatComparison l E X n P =
        DerivedCategory.Q.map (integralTowerUnit l E X D hl P n))
    (M : completedIntegralDerivedCategory l E X D hl) :
    ∃ (P : CochainComplex (scalarReductionSource l E X) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted l E X) P ∧
      ∃ (e : DerivedCategory.Q.obj P ≅ M)
        (a : ∀ n : ℕ,
          (scalarReductionDerivedRestriction l E X n).obj
              ((scalarReductionDerivedExtension l E X n).obj M) ≅
            DerivedCategory.Q.obj (unrestrictedTowerComplex l E X n P)),
      (∀ n : ℕ,
        (adj n).unit.app M ≫
            (a n).hom = e.inv ≫
          DerivedCategory.Q.map (integralTowerUnit l E X D hl P n)) ∧
      (∀ n : ℕ,
        (scalarReductionDerivedRestriction l E X (n + 1)).map
            (((adj (n + 1)).homEquiv
              M ((normalizedDVRRes l E X n.le_succ).obj
                ((scalarReductionDerivedExtension l E X n).obj M))).symm
              ((adj n).unit.app M ≫
                (normalizedDVRResCompletedComp l E X D hl n.le_succ).inv.app
                  ((scalarReductionDerivedExtension l E X n).obj M))) ≫
          (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.app
            ((scalarReductionDerivedExtension l E X n).obj M) ≫ (a n).hom =
        (a (n + 1)).hom ≫
          DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) := by
  let G := DerivedCategory.Q.objPreimage M
  let eG : DerivedCategory.Q.obj G ≅ M := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) G
  have : QuasiIso q := hq
  let e : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map q) ≪≫ eG
  let a (n : ℕ) :=
    (scalarReductionDerivedRestriction l E X n).mapIso
        ((scalarReductionDerivedExtension l E X n).mapIso e.symm) ≪≫
      @asIso _ _ _ _ (normalizedDVRKFlatComparison l E X n P)
        (representativeComparison_isIso l E X n P hP)
  refine ⟨P, hP, e, a, ?_, ?_⟩
  · intro n
    have hn := (adj n).unit.naturality
      e.inv
    have hu := hunit n P hP
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, hu]
  · intro n
    simpa only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
      Category.assoc] using
      normalizedDVR_kflat_transition l E X D hl P hP M e n (adj (n + 1)) (adj n)
        (hunit (n + 1) P hP) (hunit n P hP)

end WeilConjectures
