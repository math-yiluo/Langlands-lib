/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Basic.Finite.Sigma
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators
public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.ProEtaleCoefficients.SingleWContractibleCover

/-! Formal finite-family hypercovers by w-contractible spectra.
(blueprint: det-pe-hypercover-formal-wcontractible) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProEt
open scoped Simplicial

/-- A qcqs pro-etale object admits a finite formal-family hypercover by w-contractible spectra.
Source: Stacks Project, Tag 09A1, using Hypercoverings Tags 094K and 0DAV.
(blueprint: det-pe-hypercover-formal-wcontractible)

Proof: take the full qcqs subsite and the basis of literal spectra of w-contractible rings.
The singleton covering theorem supplies a finite basis cover of each object. Affines are
qcqs, so the sources lie in that subsite. Its finite precoverage permits adjoining each
prescribed degeneracy arrow. Apply the existing finite-basis hypercover theorem, retaining
its proper-face limiting cones, all projection identities, and the component covering
families. Empty index families and the empty base are allowed by that construction.
-/
theorem exists_formal_wContractible_hypercover (X : Scheme.{u}) (U : X.ProEt)
    (hUqc : CompactSpace U.left) (hUqs : QuasiSeparatedSpace U.left) :
    ∃ (T : Qcqs X)
      (K : SimplicialObject (FormalCoproduct.{u + 1} (Over T)))
      (M : ∀ n : ℕ, Cone (K.properFaceDiagram n))
      (μ : ∀ n : ℕ, K _⦋n⦌ ⟶ (M n).pt),
      T.obj = U ∧
      (∀ n : ℕ, Finite (K _⦋n⦌).I) ∧
      (∀ (n : ℕ) (i : (K _⦋n⦌).I),
        ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
          IsWContractibleRing D ∧
            ((K _⦋n⦌).obj i).left.obj = @Scheme.ProEt.mk X _ f hf) ∧
      (∀ n, Nonempty (IsLimit (M n))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (M n).π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ (n : ℕ) (j : (M n).pt.I),
        Presieve.ofArrows
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦ ((K _⦋n⦌).obj i.val).left)
          (fun i ↦ ((μ n).φ i.val).left ≫
            eqToHom (congrArg (fun k ↦ ((M n).pt.obj k).left) i.property)) ∈
          qcqsPrecoverage X ((M n).pt.obj j).left) := by
  classical
  obtain ⟨haffqc, ⟨hpb, J, hJ, hinc, hsch, hcov, hslice, hadjoin⟩, hsub, hcop⟩ :=
    qcqs_finite_family_geometry.{u, u + 1, 0} X
  let := hpb
  let T : Qcqs X := ⟨U, hUqc, hUqs⟩
  let B : Set (Qcqs X) := {V | ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X)
      (hf : WeaklyEtale f), IsWContractibleRing D ∧
        V.obj = @Scheme.ProEt.mk X _ f hf}
  have hBcover (Q : Qcqs X) :
      ∃ (I : Type (u + 1)) (V : I → Qcqs X) (f : ∀ i, V i ⟶ Q),
        Finite I ∧ (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ qcqsPrecoverage X Q := by
    obtain ⟨D, f, hf, g, hD, hg⟩ :=
      exists_single_wContractible_affine_cover X Q.obj Q.property.1
    let V := @Scheme.ProEt.mk X _ f hf
    have hV : IsAffine V.left := by
      change IsAffine (Spec D)
      infer_instance
    let V' : Qcqs X := ⟨V, (haffqc V hV).1, (haffqc V hV).2⟩
    let g' : V' ⟶ Q := ObjectProperty.homMk g
    refine ⟨PUnit, fun _ ↦ V', fun _ ↦ g', inferInstance,
      fun _ ↦ ⟨D, f, hf, hD, rfl⟩, ?_⟩
    constructor
    · simpa [Presieve.map_ofArrows, Presieve.ofArrows_pUnit, g', qcqsInclusion] using hg
    · exact Precoverage.ofArrows_mem_finite _ _
  have hBadjoin (Q : Qcqs X) (I : Type (u + 1)) [Finite I]
      (V : I → Qcqs X) (f : ∀ i, V i ⟶ Q) (_hV : ∀ i, V i ∈ B)
      (hf : Presieve.ofArrows V f ∈ qcqsPrecoverage X Q)
      (P : Qcqs X) (_hP : P ∈ B) (g : P ⟶ Q) :
      Presieve.ofArrows V f ⊔ Presieve.singleton g ∈ qcqsPrecoverage X Q := by
    apply hadjoin Q _ _ hf
    simp [Precoverage.mem_finite_iff]
  obtain ⟨K, M, μ, hfinite, hbasis, hzero, hlim, hproj, hcover⟩ :=
    exists_site_finite_basis_hypercover (qcqsPrecoverage X) B hBcover hBadjoin T
  exact ⟨T, K, M, μ, rfl, hfinite, hbasis, hlim, hproj, hcover⟩
