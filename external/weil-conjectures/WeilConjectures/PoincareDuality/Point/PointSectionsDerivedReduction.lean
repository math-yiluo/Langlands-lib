/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionIso
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionCone
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionHomology

/-! # Point sections and derived integral reduction
(blueprint: lem-pod-point-sections-derived-reduction) -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Point sections commute naturally with derived reduction in the quotient-module
category. After forgetting quotient scalars the left side is the multiplication cone,
and its cohomology is sections of the reduced cohomology sheaf in every integer degree.
Source: blueprint `prop-cohomological-finiteness`, integral-to-finite comparison;
Stacks Tags 093M, 06YS, 06YY, 05RT, 064L and 06Y6
(blueprint: lem-pod-point-sections-derived-reduction).

Proof (the ten steps of the node):
1. O_E is a DVR, hence Noetherian. The two-term free resolution
   [O_E --uniformizer^(n+1)--> O_E] resolves the quotient. Completed constant-sheaf
   reduction identifies its completed sheaf version with the finite coefficient sheaf.
2. Resolve the integral sheaf object by a K-flat complex P with flat terms. Tensoring
   the coefficient short exact sequence identifies its derived reduction with P/tP,
   using the balanced map x tensor b-bar to bx modulo t, where t = uniformizer^(n+1).
3. Exact point sections give C = Gamma(P) and identify C/tC with Gamma(P/tP).
   Multiplication by t is injective termwise on C.
4. Resolve C over O_E by a flat-term K-flat complex Q. Multiplication by t is also
   injective termwise on Q, and Q/tQ maps to C/tC as a quotient-linear chain map.
5. The cone T of Q to C is acyclic; its terms have injective multiplication by t,
   and T/tT is the cone of Q/tQ to C/tC, with the identical signed differential.
6. A cycle z-bar of T/tT lifts to z with dz = tw. Injectivity of t implies dw = 0.
   Write w = dv by acyclicity; then z-tv is a cycle and hence a boundary. Reducing
   modulo t proves that z-bar is a boundary. Thus T/tT is acyclic, without bounds.
7. The quotient map Q/tQ to C/tC is a quasi-isomorphism over the quotient ring.
   Compose it with C/tC = Gamma(P/tP) to obtain the asserted derived isomorphism.
8. Simultaneous K-flat replacements of finite arrow and cospan diagrams identify
   all resolution choices and prove naturality. Localization arrows are composites
   of chain maps and inverses of quasi-isomorphisms, so the squares descend.
9. Tensor the two-term free quotient resolution with Q and compare with C.
   K-flat tensor invariance identifies the restricted left side with Cone(t on C),
   whose differential on C^j plus C^(j+1) is (x,y) to (dx+ty,-dy).
10. Take homology of the natural comparison. Exact finite point sections commute
    with homology, giving the final natural isomorphism in every integer degree.
-/
theorem point_sections_derived_reduction (_hl : l ≠ D.p) (n : ℕ) :
    Nonempty (pointReductionTensorSections D l E n ≅ pointReductionSectionsTensor D l E n) ∧
    (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (C : CochainComplex (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ),
      Nonempty (DerivedCategory.Q.obj C ≅
        (pointIntegralSections l E D.k).mapDerivedCategory.obj N.obj) →
      Nonempty (((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory).obj
          ((pointReductionTensorSections D l E n).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) • 𝟙 C)))) ∧
    ∀ r : ℤ, Nonempty
      (pointReductionTensorSections D l E n ⋙ DerivedCategory.homologyFunctor _ r ≅
        (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
          scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
            DerivedCategory.homologyFunctor _ r ⋙
              pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) := by
  refine ⟨point_sections_derived_reduction_iso D l E _hl n, ?_,
    point_sections_derived_reduction_homology D l E _hl n⟩
  intro N C hC
  obtain ⟨e⟩ := hC
  obtain ⟨m⟩ := point_sections_derived_reduction_module_cone D l E _hl n C
  let f := pointReductionModuleTensor l E n
  let q := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (pointReductionQuotient l E n)).mapDerivedCategory
  exact ⟨(q.mapIso (f.mapIso e)).symm ≪≫ m⟩

end WeilConjectures
