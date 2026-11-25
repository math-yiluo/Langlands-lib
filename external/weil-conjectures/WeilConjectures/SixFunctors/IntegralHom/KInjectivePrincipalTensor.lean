/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # K-injective targets and a two-term free tensor factor

Source: Stacks Project, Tags 08J7 and 070G; the first paragraph of
`lem-coef-integral-hom-reduction.proof.md`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

/-- Tensoring a K-injective complex by a principal two-term free complex preserves
K-injectivity.

Source: Stacks Project, Tags 08J7 and 070G; the finite-free construction in paragraph 1
of `lem-coef-integral-hom-reduction.proof.md`
(blueprint: lem-sf-kinjective-principal-tensor).

Proof: total tensor with the cone [R --a^(n+1)--> R] is canonically the cone of
multiplication by a^(n+1) on I. To check K-injectivity, apply the complex of abelian
groups of maps from an arbitrary acyclic complex. This takes the finite cone to the
cone of the induced endomorphism of the mapping complex. Both copies of that mapping
complex are acyclic by K-injectivity of I, so their cone is acyclic. The total-tensor
identification uses the unit constraints and the usual signed cone differential.
No regularity of a, boundedness of I, or flatness of its terms is needed. For a=0
this is the direct sum I[1] ⊕ I, and the same argument applies to zero inputs. -/
theorem isKInjective_tensor_principalKoszul
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : (SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)).sections)
    (I : CochainComplex (Modules.{t, u} Y R) ℤ) [I.IsKInjective] (n : ℕ) :
    (((totalTensor.{t, u} Y R).obj I).obj (principalKoszul R a n)).IsKInjective  := by
  let M := Modules.{t, u} Y R
  let : MonoidalCategory M := SheafOfModules.monoidalCategory R
  let : MonoidalPreadditive M := SheafOfModules.cochainModulesPreadditive R
  let := countableColimits.{t, u} Y R
  let F := ordinaryTensor.{t, u} Y R
  let U := (CochainComplex.singleFunctor M 0).obj
    (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
  let f := principalKoszulScalarComplex R a n
  let g := HomologicalComplex.mapBifunctorMap (𝟙 I) f F (.up ℤ)
  have hU : CochainComplex.IsKInjective (HomologicalComplex.mapBifunctor I U F (.up ℤ)) :=
    CochainComplex.isKInjective_of_iso (HomologicalComplex.rightUnitor I).symm
  have hcone : (CochainComplex.mappingCone g).IsKInjective := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact (HomotopyCategory.subcategoryAcyclic M).rightOrthogonal.ext_of_isTriangulatedClosed₃
      (CochainComplex.mappingCone.triangleh g)
      (HomotopyCategory.mappingCone_triangleh_distinguished g)
      ((CochainComplex.isKInjective_iff_rightOrthogonal _).1 hU)
      ((CochainComplex.isKInjective_iff_rightOrthogonal _).1 hU)
  let := hcone
  exact CochainComplex.isKInjective_of_iso
    (CochainComplex.mapBifunctorMappingCone₂Iso I f F).symm

end WeilConjectures.IntegralHom
