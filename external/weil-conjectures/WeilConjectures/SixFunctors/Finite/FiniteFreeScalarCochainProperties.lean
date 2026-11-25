/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.FiniteFreeQuotientRoosComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # A step of strict scalar pullback cone naturality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] integralTowerHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} W.ProEt :=
  essentiallySmallSelf.{u, t, t + 1} _

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} W

private local instance (W : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory in
/-- Finite-free completed scalar extension preserves products, good representatives,
and computes its derived functor on every complex.
Source: Stacks, sites-modules.tex, Tag 03EK and sites-cohomology.tex, Tag 06YY;
Steps 4, 6 and 7 of strict scalar pullback cone naturality.
(blueprint: lem-sf-finite-free-scalar-cochain-properties).

Proof: use the recorded finite free completed coefficient module S = R^d.
Restriction of ordinary scalar extension is naturally the finite direct sum
of d copies of the identity. The projection-defined product comparison has
inverse given by summing the d tuples of basis coordinates; thus it commutes
with countable products. Restriction of scalars creates limits and colimits,
is exact and conservative, so this also proves exactness of extension.
Change of rings preserves K-flatness. Its tensor-association comparison with
an arbitrary test module proves flatness of each extended flat term; together
these give preservation of good representatives. Finally resolve any complex
by a K-flat complex. Exact ordinary extension sends its quasi-isomorphism to
a quasi-isomorphism. The universal scalar counit is invertible on the resolution,
and its naturality square makes it invertible on the original complex by
three-for-two. This argument concerns completed finite-free coefficients,
and does not assume flatness of any ramified finite quotient map. -/
theorem finiteFreeScalarCochainProperties (W : AlgebraicGeometry.Scheme.{t}) :
    PreservesLimitsOfShape (Discrete ℕ) (completedOrdinaryScalarExtension l E L ι W) ∧
    (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      integralOperationsGoodComplex l L W
        ((completedOrdinaryScalarComplex l E L ι W).obj P.obj)) ∧
    (∀ P : CochainComplex (integralTowerModules l E W) ℤ,
      IsIso (completedScalarCounit l E L ι W P)) := by
  classical
  let F := completedScalarCochainModel l E L ι W
  have hfree := (finiteFreeCompletedScalarComparison l E L ι W).1
  have hf : ∃ d : ℕ, Nonempty
      (((SheafOfModules.restrictScalars
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
          (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E L ι W))).obj
            (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L W))) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))) := by
    let f : Fin (completedScalarRelativeDegree l E L ι) → integralTowerModules l E W :=
      fun _ ↦ SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
    let : HasBiproduct f :=
      (Abelian.hasFiniteBiproducts (C := integralTowerModules l E W)).out _ |>.has_biproduct f
    obtain ⟨b⟩ := hfree
    exact ⟨completedScalarRelativeDegree l E L ι, ⟨b ≪≫ biproductIso f⟩⟩
  obtain ⟨hl, hc, hp⟩ := PrincipalQuotientCompletion.scalarExactProducts F hf
  let := hl
  let := hc
  have he : IsIso F.ε := by
    let := F.universal
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      (W := HomologicalComplex.quasiIso _ (.up ℤ)) F.T F.ε
    intro P P' f hf
    have : QuasiIso f := hf
    change IsIso (DerivedCategory.Q.map ((F.E.mapHomologicalComplex (.up ℤ)).map f))
    infer_instance
  refine ⟨hp, ?_, ?_⟩
  · intro P
    let R := completedIntegralCommRingSheafUnrestricted l E W
    let S := completedIntegralCommRingSheafUnrestricted l L W
    let φ := completedCoefficientMap l E L ι W
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.isMonoidal_W_independentCoefficients S
    have hflat (i : ℤ) : exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.obj.X i)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (P.obj.X i)) (P.property.2 i)
    obtain ⟨hk, hterms⟩ :=
      SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients φ P.obj
        F.E F.obj_eq F.map_eq P.property.1 hflat
    refine ⟨hk, ?_⟩
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S
        (((F.E.mapHomologicalComplex (.up ℤ)).obj P.obj).X i)).symm (hterms i)
  · intro P
    rw [← completedScalarCochainModel_counit l E L ι W P]
    change IsIso (F.ε.app P)
    infer_instance

end WeilConjectures
