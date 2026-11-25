/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.Supporting.StrictDvrCoefficientSequence
import WeilConjectures.SixFunctors.Supporting.StrictDvrFlatTensorSequence

/-! # Simultaneous strict DVR reductions and residue-kernel triangles

Source: Stacks Project, sites-cohomology.tex, Tag 0942, lemma-bounded, proof (1),
specialized to the constant DVR coefficient quotients.
(blueprint: lem-sf-strict-dvr-reduction-triangles)

The index `n : ℕ` always means exponent `n + 1`. In particular index zero is the
residue coefficient. The completed ring, finite scalar extension, scalar restriction,
pure tensors and quotient chain transitions are the existing unrestricted constructions.
Their scalar-first tensor convention is the canonical symmetry presentation of
`P ⊗ C_n`; no tensor or coefficient tower is redefined here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

private theorem transport_shortExact_triangle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    {K₁ K₂ K₃ : DerivedCategory A}
    (e₁ : DerivedCategory.Q.obj S.X₁ ≅ K₁)
    (e₂ : DerivedCategory.Q.obj S.X₂ ≅ K₂)
    (e₃ : DerivedCategory.Q.obj S.X₃ ≅ K₃) :
    ∃ δ : K₃ ⟶ K₁⟦(1 : ℤ)⟧,
      Triangle.mk (e₁.inv ≫ DerivedCategory.Q.map S.f ≫ e₂.hom)
        (e₂.inv ≫ DerivedCategory.Q.map S.g ≫ e₃.hom) δ ∈
          CategoryTheory.Pretriangulated.distinguishedTriangles := by
  let δ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧'
  refine ⟨δ, ?_⟩
  apply (distinguished_iff_of_iso
    (Triangle.isoMk (DerivedCategory.triangleOfSES hS)
      (Triangle.mk _ _ δ) e₁ e₂ e₃ ?_ ?_ ?_)).1
    (DerivedCategory.triangleOfSES_distinguished hS)
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES, δ]

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The quotient coefficient itself, as a module over the completion via its projection.
Source: Stacks 0942, proof (1), coefficient terms
(blueprint: lem-sf-strict-dvr-reduction-triangles). -/
abbrev strictDvrCoefficientModule (n : ℕ) : scalarReductionSource l E X :=
  (scalarReductionRestriction l E X n).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E X n))

/-- A constant coefficient section represented by an integer of the coefficient field.
This is the unit of the recorded constant-sheaf sheafification applied to its quotient.
Source: Stacks 0942, proof (1), DVR kernel identification
(blueprint: lem-sf-strict-dvr-reduction-triangles). -/
def strictDvrConstantSection (n : ℕ) (U : X.ProEtᵒᵖ)
    (r : Padic.coefficientExtensionIntegers l E) :
    (strictDvrCoefficientModule l E X n).val.obj U :=
  (toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) r))

/-- The object `Res_{π_n}(K ⊗ᴸ_B C_n)`, using the existing universal derived extension
and exact derived restriction, at exponent `n + 1`.
Source: Stacks 06YY and 0942, proof (1)
(blueprint: lem-sf-strict-dvr-reduction-triangles). -/
abbrev strictDvrDerivedReduction
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (scalarReductionDerivedRestriction l E X n).obj
    ((scalarReductionDerivedExtension l E X n).obj K)

/-- Simultaneous comparison normalized by the universal scalar-extension counit on
the same K-flat complex and the same isomorphism to `K` at every level.
Source: Stacks 06YT, 06YY and 0942, proof (1)
(blueprint: lem-sf-strict-dvr-reduction-triangles).
The identity resolution of `P` supplies its K-flat computation; the final map is
the functorial image of `e`, so no level-dependent resolution is chosen. -/
def strictDvrReductionComparison
    {K : DerivedCategory (scalarReductionSource l E X)}
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    DerivedCategory.Q.obj (unrestrictedTowerComplex l E X n P) ≅
      strictDvrDerivedReduction l E X K n :=
  ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.app _).symm ≪≫
    (scalarReductionRestriction l E X n).mapDerivedCategory.mapIso
      ((unrestrictedTowerResolutionIso l E X n (𝟙 P) ⟨inferInstance, hP⟩).symm ≪≫
        (scalarReductionDerivedExtension l E X n).mapIso e)

/-- The canonical derived quotient transition, expressed in the fixed simultaneous
K-flat computation. The chain map is the published `id ⊗ q_n`, characterized on
sheafified pure tensors; both changes of coordinates are the universal comparisons.
Source: Stacks 06YT, 06YY and 0942, proof (1)
(blueprint: lem-sf-strict-dvr-reduction-triangles).
Resolution independence is the quotient-transition clause of
`unrestrictedReductionTowerWellDefined`. -/
def strictDvrDerivedQuotientTransition
    {K : DerivedCategory (scalarReductionSource l E X)}
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P)
    (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    strictDvrDerivedReduction l E X K (n + 1) ⟶ strictDvrDerivedReduction l E X K n :=
  (strictDvrReductionComparison l E X P hP e (n + 1)).inv ≫
    DerivedCategory.Q.map (unrestrictedTowerTransition l E X P n) ≫
      (strictDvrReductionComparison l E X P hP e n).hom

/-- A single flat-term K-flat representative computes every positive coefficient
reduction with the actual residue-kernel chain maps and canonical quotient transitions.
Source: Stacks 0942, lemma-bounded, proof (1), DVR specialization
(blueprint: lem-sf-strict-dvr-reduction-triangles).

Proof:
1. Represent K by G and resolve G once by a flat-term K-flat P (lem-pc-kflat-resolution).
Compose the localization of that resolution with the isomorphism from Q(G) to K.
2. Over the DVR, multiplication by ϖ^(n+1) identifies R/(ϖ) with the kernel of
R/(ϖ^(n+2)) → R/(ϖ^(n+1)): well-definedness is multiplication of ideals, injectivity
is cancellation of the nonzero uniformizer in E, and exactness is the quotient formula.
3. Apply the exact constant-module functor (def-sfb-site-derived-constant-module-functor,
def-sf-site-constant-module-functor). Exactness can be read on underlying additive
sheaves by situation-conventions.
4. The residue injection is linear with the target action reduced to R/(ϖ).
The limit-projection identities therefore make it B-linear (def-pur-sheaf-inverse-limit,
def-pc-sheaf-restrict-scalars); its formula on constant sections is the one displayed.
5. Tensor the coefficient short exact sequence in each degree with the B-flat term P^i.
Symmetry (lem-pc-sheaf-modules-tensor-closed) identifies the scalar-first and scalar-last
conventions. The maps commute with d_P, giving the stated degreewise short exact rows.
6. The universal K-flat counit (lem-pur-derived-change-of-rings) computes all reductions
from this same P. The restriction localization comparison and symmetry give the
simultaneous comparisons (lem-pe-restricted-kflat-tensor-identification).
Coefficient naturality (lem-sf-ringed-kflat-single-tensor-comparison) identifies the
localized actual quotient chain maps with the canonical derived quotient transitions.
7. Apply lem-weil-pbc-complex-ses-triangle, then transport the triangle along those
same comparisons. Its first arrow is the localized kernel injection and its second
arrow is exactly the canonical quotient transition. No extra condition on K or X occurs.
-/
theorem strictDvrReductionTriangles
    (K : DerivedCategory (scalarReductionSource l E X)) :
    ∃ (P : CochainComplex (scalarReductionSource l E X) ℤ)
      (e : DerivedCategory.Q.obj P ≅ K)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted l E X) P),
      (∀ j : ℤ, SheafOfModules.IsFlatOnSite
        (J := AlgebraicGeometry.Scheme.ProEt.topology X)
        (R := completedIntegralCommRingSheafUnrestricted l E X) (P.X j)) ∧
      ∃ (u : ∀ n : ℕ, strictDvrCoefficientModule l E X 0 ⟶
          strictDvrCoefficientModule l E X (n + 1)),
        (∀ (n : ℕ) (U : X.ProEtᵒᵖ) (r : Padic.coefficientExtensionIntegers l E),
          (u n).val.app U (strictDvrConstantSection l E X 0 U r) =
            strictDvrConstantSection l E X (n + 1) U
              (Padic.coefficientExtensionUniformizer l E ^ (n + 1) * r)) ∧
        ∃ (i : ∀ n : ℕ, unrestrictedTowerComplex l E X 0 P ⟶
            unrestrictedTowerComplex l E X (n + 1) P),
          (∀ (n : ℕ) (j : ℤ) (U : X.ProEtᵒᵖ)
            (s : (strictDvrCoefficientModule l E X 0).val.obj U)
            (x : (P.X j).val.obj U),
            ((i n).f j).val.app U (unrestrictedTowerTensorSection l E X 0 (P.X j) U s x) =
              unrestrictedTowerTensorSection l E X (n + 1) (P.X j) U
                ((u n).val.app U s) x) ∧
          ∀ n : ℕ, ∃ hz : i n ≫ unrestrictedTowerTransition l E X P n = 0,
            (∀ j : ℤ, ((ShortComplex.mk (i n) (unrestrictedTowerTransition l E X P n) hz).map
              (HomologicalComplex.eval (scalarReductionSource l E X) (.up ℤ) j)).ShortExact) ∧
            ∃ δ : strictDvrDerivedReduction l E X K n ⟶
                (strictDvrDerivedReduction l E X K 0)⟦(1 : ℤ)⟧,
              Triangle.mk
                ((strictDvrReductionComparison l E X P hP e 0).inv ≫
                  DerivedCategory.Q.map (i n) ≫
                    (strictDvrReductionComparison l E X P hP e (n + 1)).hom)
                (strictDvrDerivedQuotientTransition l E X P hP e n) δ ∈
                  CategoryTheory.Pretriangulated.distinguishedTriangles := by
  classical
  let G := DerivedCategory.Q.objPreimage K
  let eG : DerivedCategory.Q.obj G ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X) G
  have : QuasiIso f := hf
  let e : DerivedCategory.Q.obj P ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eG
  have hflat' : ∀ j : ℤ, SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) (P.X j) := by
    intro j
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E X) (P.X j)).symm (hflat j)
  obtain ⟨a, ha, hseq⟩ := strictDvrCoefficientSequence l E X
  obtain ⟨i, hi, hrows⟩ := strictDvrFlatTensorSequence l E X P hflat' a hseq
  refine ⟨P, e, hP, hflat', a, ha, i, hi, ?_⟩
  intro n
  obtain ⟨hz, hrow⟩ := hrows n
  refine ⟨hz, hrow, ?_⟩
  let S := ShortComplex.mk (i n) (unrestrictedTowerTransition l E X P n) hz
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S hrow
  exact transport_shortExact_triangle S hS
    (strictDvrReductionComparison l E X P hP e 0)
    (strictDvrReductionComparison l E X P hP e (n + 1))
    (strictDvrReductionComparison l E X P hP e n)

end WeilConjectures
