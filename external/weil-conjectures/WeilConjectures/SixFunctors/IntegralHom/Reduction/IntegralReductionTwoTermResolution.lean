/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # The completed-coefficient two-term quotient resolution

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 093M, 06YQ and 0657.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The finite coefficient sheaf, restricted to the completed ring, has a K-flat
resolution with two free rank-one terms. The target of the augmentation is the
actual restriction of the finite coefficient unit in degree zero.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 093M, 06YQ and 0657
(blueprint: lem-sf-integral-reduction-two-term-resolution).

Proof: use the DVR uniformizer of the ring of integers of E. Its (n+1)-st
power is a non-zero-divisor. The complex with that multiplication from the
free rank-one module in degree -1 to the same module in degree zero resolves
the quotient by its (n+1)-st power. Apply constant sheafification on the pro-etale
site and extend scalars to the completed coefficient ring. Flatness of the
completed constant sheaf and its finite-quotient identification preserve the
augmentation quasi-isomorphism. The quotient identification commutes with the
coordinate projection of the completed ring, so its target is exactly the
restricted coefficient unit below. Scalar extension carries the two free terms
to the completed unit and preserves the zero terms. A bounded complex of flat
terms is K-flat. These constructions work in the coefficient universe
max(u,t+1) without identifying the site and coefficient universes, also for the
empty scheme and n=0. -/
theorem integralReduction_twoTerm_resolution (n : ℕ) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    ∃ (Q : CochainComplex (Modules.{t, u} Y R) ℤ)
      (_ : flat.{t, u} Y R Q)
      (_ : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
      (_ : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (_ : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (epsilon : Q ⟶
        ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
            (SheafOfModules.unit (integralCoefficientSheaf l E Y n)))),
      QuasiIso epsilon := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let A := Modules.{t, u} Y R
  let U : A := SheafOfModules.unit
    (completedIntegralCoefficientSheafUnrestricted l E Y)
  let : EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
    essentiallySmallSelf _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.tensorPreadditive R
  let S : ShortComplex A := ShortComplex.mk
    (PrincipalKoszulStrictReplacement.multiplication l E Y n)
    (PrincipalKoszulStrictReplacement.projection l E Y n)
    (PrincipalKoszulStrictReplacement.multiplication_projection l E Y n)
  have hS : S.ShortExact := (PrincipalKoszulStrictReplacement.completed_exact l E Y n).1
  let F := CochainComplex.singleFunctor A 0
  let Q := CochainComplex.mappingCone (F.map S.f)
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero ((F.obj U).X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 U i hi
  have hsupport (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (Q.X i) := by
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
    exact ⟨hz (i + 1) (by omega), hz i h0⟩
  let em : Q.X (-1) ≅ U :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (F.map S.f) (-1) 0 (by decide) ≪≫
      (isoBiprodZero (hz (-1) (by decide))).symm ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 U
  let e0 : Q.X 0 ≅ U :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (F.map S.f) 0 1 (by decide) ≪≫
      (isoZeroBiprod (hz 1 (by decide))).symm ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 U
  have hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y) (R := R) (Q.X i) := by
    have hu : ObjectProperty.flat U := ObjectProperty.prop_unit ObjectProperty.flat
    intro i
    have hi : ObjectProperty.flat (Q.X i) := by
      by_cases hm : i = -1
      · subst i
        exact ObjectProperty.prop_of_iso ObjectProperty.flat em.symm hu
      · by_cases h0 : i = 0
        · subst i
          exact ObjectProperty.prop_of_iso ObjectProperty.flat e0.symm hu
        · exact ObjectProperty.flat_of_isZero (hsupport i hm h0)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (Q.X i)).symm hi.2
  have hbounded : Q.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hsupport i (by omega) (by omega)
  let := hbounded
  have hQ : flat.{t, u} Y R Q :=
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R Q 0 hflat
  have hFlim : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single A (.up ℤ) 0))
  have hFcolim : PreservesFiniteColimits F :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single A (.up ℤ) 0))
  let := hFlim
  let := hFcolim
  let ε : Q ⟶ F.obj S.X₃ := CochainComplex.mappingCone.descShortComplex (S.map F)
  have hε : QuasiIso ε :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (hS.map_of_exact F)
  let := hε
  let G := scalarReductionRestriction l E Y n
  let : PreservesFiniteLimits G := (scalarReductionRestriction_exact l E Y n).1
  let : PreservesFiniteColimits G := (scalarReductionRestriction_exact l E Y n).2
  let e := (G.mapCochainComplexSingleFunctor 0).app
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))
  refine ⟨Q, hQ, hsupport, em, e0, ε ≫ e.inv, ?_⟩
  infer_instance

end WeilConjectures.IntegralHom
