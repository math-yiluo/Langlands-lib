/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Natural Hom models on diagrams of K-injective tensor targets -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures.IntegralHom
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits ordinaryTensorZero ordinaryTensorObjZero
attribute [local implicit_reducible] homComplex totalTensor
attribute [local irreducible] homComplexFunctor HasDerivedCategory.standard
  derivedInternalHomOfUniverses

private theorem homDiagram_representatives
    {V : Type*} [Category* V]
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (K : Derived.{t, u} Y R) (A : CochainComplex (Modules.{t, u} Y R) ℤ)
    (eA : DerivedCategory.Q.obj A ≅ K)
    (S : V ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ n, (S.obj n).IsKInjective) :
    Nonempty (S ⋙ DerivedCategory.Q ⋙ (Functor.curry.obj (hom.{t, u} Y R)).obj (op K) ≅
      S ⋙ (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R)).obj (op A) ⋙ DerivedCategory.Q) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let M := Modules.{t, u} Y R
  let : HasDerivedCategory M := HasDerivedCategory.standard _
  let : IsGrothendieckAbelian.{max u (t + 1)} M :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u} J R).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} M
  let η := CochainComplex.toKInjectiveResolution.{max u (t + 1)} M
  let HA := (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
    (R := R)).obj (op A)
  obtain ⟨c⟩ := derivedInternalHomOfUniverses_comparison.{t + 1, t, u} J R I₀ η
    (fun N ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app
      M N).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M N⟩)
  let b : S ⋙ HA ⋙ DerivedCategory.Q ⟶ S ⋙ I₀ ⋙ HA ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (Functor.whiskerLeft S η) (HA ⋙ DerivedCategory.Q)
  have hb : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    let : (S.obj n).IsKInjective := hS n
    have : (I₀.obj (S.obj n)).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M (S.obj n)
    have : QuasiIso (η.app (S.obj n)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app M (S.obj n)).2
    change IsIso (DerivedCategory.Q.map (HA.map (η.app (S.obj n))))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    simpa [HA] using quasiIso_homComplex_mapOfUniverses.{t + 1, t, u}
      (J := J) (R := R) (I' := S.obj n) (I := I₀.obj (S.obj n))
      (L' := A) (L := A) (η.app (S.obj n)) (𝟙 A)
  let cS : S ⋙ DerivedCategory.Q ⋙
      (Functor.curry.obj (hom.{t, u} Y R)).obj (op (DerivedCategory.Q.obj A)) ≅
      S ⋙ I₀ ⋙ HA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun n ↦ c.app (op A, S.obj n)) (by
      intro n m f
      simpa [HA, hom] using c.hom.naturality
        (X := (op A, S.obj n)) (Y := (op A, S.obj m)) (𝟙 (op A), S.map f))
  exact ⟨Functor.isoWhiskerLeft (S ⋙ DerivedCategory.Q)
    ((Functor.curry.obj (hom.{t, u} Y R)).mapIso eA.op) ≪≫ cS ≪≫ (asIso b).symm⟩

/-- Tensor diagrams preserving K-injectivity admit natural derived Hom models.

Source: paragraph 1 of the current blueprint `lem-coef-integral-hom-reduction.proof.md`;
Stacks Tags 08J7 and 0A95 (blueprint: lem-sf-integral-hom-kinjective-tensor-diagram).

Proof: represent K by A and resolve G by the canonical K-injective complex I,
with the inverse of the localized resolution map as eI. The hypothesis makes
all I tensor S(v) K-injective. Compare derived Hom on these targets with the
canonical functorial K-injective resolution, using the natural derived-Hom
comparison. The resolution maps induce quasi-isomorphisms on Hom(A,-), since
both targets are K-injective, so their localizations form a natural isomorphism.
Compose its inverse with the derived-Hom comparison and transport along LA ≅ K.
Naturality holds on every diagram arrow; empty diagrams and zero inputs require
no separate choices. No flatness of A or boundedness of S is assumed. -/
theorem integralHom_kInjective_tensor_diagram
    {V : Type*} [Category* V]
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (K : Derived.{t, u} Y R) (G : CochainComplex (Modules.{t, u} Y R) ℤ)
    (S : V ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ (I : CochainComplex (Modules.{t, u} Y R) ℤ) [I.IsKInjective] (n : V),
      (((totalTensor.{t, u} Y R).obj I).obj (S.obj n)).IsKInjective) :
    ∃ (A I : CochainComplex (Modules.{t, u} Y R) ℤ)
      (_eI : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj G),
      Nonempty (S ⋙ (totalTensor.{t, u} Y R).obj I ⋙ DerivedCategory.Q ⋙
          (Functor.curry.obj (hom.{t, u} Y R)).obj (op K) ≅
        S ⋙ (totalTensor.{t, u} Y R).obj I ⋙
          (homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := R)).obj (op A) ⋙ DerivedCategory.Q) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let M := Modules.{t, u} Y R
  let : HasDerivedCategory M := HasDerivedCategory.standard _
  let A : CochainComplex M ℤ := DerivedCategory.Q.objPreimage K
  let eA : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let : IsGrothendieckAbelian.{max u (t + 1)} M :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u} J R).1
  let I := (CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} M).obj G
  let : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj M G
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} M).app G) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app M G).2
  let eI : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj G :=
    (asIso (DerivedCategory.Q.map
      ((CochainComplex.toKInjectiveResolution.{max u (t + 1)} M).app G))).symm
  refine ⟨A, I, eI, ?_⟩
  exact homDiagram_representatives Y R K A eA (S ⋙ (totalTensor.{t, u} Y R).obj I)
    (fun n ↦ hS I n)

end WeilConjectures.IntegralHom
