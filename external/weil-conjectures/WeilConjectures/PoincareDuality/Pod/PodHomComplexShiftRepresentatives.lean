/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
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

/-! # Signed Hom-complex shifts and K-injective representatives

Source: Stacks Project, Tags 08JA and 0A95.
(blueprint: stage3-pod-hom-complex-shift-representatives).
These existing constructions are separated from the automorphism companions
so that each file stays within the single-file compilation limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section SignedShifts
attribute [local irreducible] homComplexFunctor
universe r s t w
variable {C : Type s} [Category.{t} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max s t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r}]
  (A : Sheaf J CommRingCat.{max s t r})

/-- Modules in the existing independent-universe coefficient convention.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
abbrev PodModules := SheafOfModules.{max s t r}
  ((sheafCompose J (forget₂ CommRingCat.{max s t r} RingCat.{max s t r})).obj A)

/-- The canonical signed Hom-complex shift, fixed by every product projection.
Source: node proof step 6, Stacks 08JA.
Proof: reindex the product from p to p+m and multiply degree k by (-1)^(m*k).
The adjacent-degree signs compensate the shifted differential. The inverse
reindexes by -m with the inverse sign, so the map is an isomorphism. Product
projections are jointly monic, proving uniqueness, including negative shifts.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podHomComplexShift_existsUnique
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) (m n : ℤ) :
    ∃! e : (homComplex.{s, t, max s t r, max s t r} (R := A) K I)⟦n - m⟧ ≅
        homComplex.{s, t, max s t r, max s t r} (R := A) (K⟦m⟧) (I⟦n⟧),
      ∀ (k p q : ℤ) (h : p + k = q) (h' : p + m + (k + (n - m)) = q + n),
        e.hom.f k ≫ coefficientHomComponent.{r, s, t} J A (K⟦m⟧) (I⟦n⟧) k p q h =
          (m * k).negOnePow •
            ((homComplex.{s, t, max s t r, max s t r} (R := A) K I).shiftFunctorObjXIso
                (n - m) k (k + (n - m)) rfl).hom ≫
            coefficientHomComponent.{r, s, t} J A K I (k + (n - m)) (p + m) (q + n) h' ≫
            SheafOfModules.homObjMap.{max s t r, t, s, max s t r}
              (K.shiftFunctorObjXIso m p (p + m) rfl).hom
              (I.shiftFunctorObjXIso n q (q + n) rfl).inv := by
  classical
  obtain ⟨SR, _, hR, _⟩ := CategoryTheory.RingedHomUniverses.ordinaryRightShift.{s, t, r} J A
  obtain ⟨SL, hL⟩ := CategoryTheory.RingedHomUniverses.ordinaryLeftShift.{s, t, r} J A m
  let H := homComplex.{s, t, max s t r, max s t r} (R := A) K I
  let eR := ((SR K).commShiftIso n).symm.app I
  let eL := SL.app (op K, I⟦n⟧)
  let e : H⟦n - m⟧ ≅
      homComplex.{s, t, max s t r, max s t r} (R := A) (K⟦m⟧) (I⟦n⟧) :=
    (shiftFunctorAdd' _ n (-m) (n - m) (sub_eq_add_neg n m).symm).app H ≪≫
      (shiftFunctor _ (-m)).mapIso eR ≪≫ eL
  have hπeq (i j p q : ℤ) (hij : i = j) (h : p + i = q) (h' : p + j = q) :
      (H.XIsoOfEq hij).hom ≫ homComplexπ (R := A) K I j p q h' =
        homComplexπ (R := A) K I i p q h := by
    subst j
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  have he (k p q : ℤ) (h : p + k = q)
      (h' : p + m + (k + (n - m)) = q + n) :
      e.hom.f k ≫ coefficientHomComponent.{r, s, t} J A (K⟦m⟧) (I⟦n⟧) k p q h =
        (m * k).negOnePow •
          (H.shiftFunctorObjXIso (n - m) k (k + (n - m)) rfl).hom ≫
          coefficientHomComponent.{r, s, t} J A K I
            (k + (n - m)) (p + m) (q + n) h' ≫
          SheafOfModules.homObjMap.{max s t r, t, s, max s t r}
            (K.shiftFunctorObjXIso m p (p + m) rfl).hom
            (I.shiftFunctorObjXIso n q (q + n) rfl).inv := by
    have hl := hL K (I⟦n⟧) k p q h
    have hr := hR K I n (k + -m) (p + m) q (by omega)
    dsimp only [e, eL, eR, H, Iso.trans_hom, HomologicalComplex.comp_f,
      coefficientHomComponent]
    simp only [Category.assoc]
    rw [hl]
    simp only [Functor.mapIso_hom, CochainComplex.shiftFunctor_map_f',
      Linear.comp_units_smul, ← Category.assoc, hr]
    simp only [CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    simp only [smul_left_cancel_iff]
    change (H.XIsoOfEq (by omega : k + (n - m) = k + -m + n)).hom ≫
      homComplexπ (R := A) K I (k + -m + n) (p + m) (q + n) _ =
        𝟙 _ ≫ homComplexπ (R := A) K I (k + (n - m)) (p + m) (q + n) h'
    rw [Category.id_comp]
    exact hπeq _ _ _ _ _ _ _
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro k
  apply homComplex_hom_ext
  intro p q h
  exact (he' k p q h (by omega)).trans (he k p q h (by omega)).symm

/-- The unique signed product-reindexing map.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podHomComplexShift (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) (m n : ℤ) :=
  (podHomComplexShift_existsUnique.{r, s, t} J A K I m n).exists.choose

variable [HasDerivedCategory.{w} (PodModules.{r, s, t} J A)]

/-- The actual augmentation of the chosen Hom target resolution.
Source: Stacks 0A95 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podHomAugmentation (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) :
    homComplex.{s, t, max s t r, max s t r} (R := A) K I ⟶
      homComplex.{s, t, max s t r, max s t r} (R := A) K
        ((coefficientHomResolution.{r, s, t} J A).obj I) :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{s, t, r}
      J A).1
  (homComplexFunctor.{s, t, max s t r, max s t r}.obj (op K)).map
    ((CochainComplex.toKInjectiveResolution _).app I)

/-- The K-injective representative model is fixed by the actual augmentation.
Source: Stacks 0A95, node proof steps 3 and 6.
Proof: for K-injective I, its augmentation to the fixed resolution is a homotopy
 equivalence between K-injectives. Hom(K,-) preserves its homotopy inverse.
Localize and invert that map in the recorded resolution factorization. The
normalization determines the isomorphism uniquely by cancellation.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podKInjectiveHomModel_existsUnique
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] :
    ∃! e : (derivedInternalHomOfUniverses.{s, t, r, w} J A).obj
        (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
          DerivedCategory.Q.obj (homComplex.{s, t, max s t r, max s t r} (R := A) K I),
      e.hom ≫ DerivedCategory.Q.map (podHomAugmentation.{r, s, t} J A K I) =
        (coefficientHomResolutionIso.{r, s, t, w} J A K I).hom := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{s, t, r}
      J A).1
  let η := (CochainComplex.toKInjectiveResolution _).app I
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  have : ((coefficientHomResolution.{r, s, t} J A).obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ I
  have hq : QuasiIso (podHomAugmentation.{r, s, t} J A K I) := by
    simpa [podHomAugmentation, η] using
      (quasiIso_homComplex_mapOfUniverses.{s, t, r} (R := A)
        (I' := I) (I := (coefficientHomResolution.{r, s, t} J A).obj I) η (𝟙 K))
  let : IsIso (DerivedCategory.Q.map (podHomAugmentation.{r, s, t} J A K I)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  refine ⟨coefficientHomResolutionIso.{r, s, t, w} J A K I ≪≫
    (asIso (DerivedCategory.Q.map (podHomAugmentation.{r, s, t} J A K I))).symm, ?_, ?_⟩
  · simp
  · intro e he
    apply Iso.ext
    apply (cancel_mono (DerivedCategory.Q.map (podHomAugmentation.{r, s, t} J A K I))).mp
    simpa using he

/-- Canonical K-injective representative comparison.
Source: Stacks 0A95 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podKInjectiveHomModel
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] :=
  (podKInjectiveHomModel_existsUnique.{r, s, t, w} J A K I).exists.choose

end SignedShifts
end WeilConjectures
