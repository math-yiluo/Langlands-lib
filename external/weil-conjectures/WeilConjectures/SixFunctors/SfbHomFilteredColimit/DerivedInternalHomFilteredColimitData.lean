/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
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
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Strict coefficient tensor and internal-Hom roof

The definitions and unique-normalization assertion are shared by the finite-free stage
calculation and the filtered-colimit theorem. They are the unchanged representative
models of `lem-sfb-dc-hom-filtered-colimit`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures.SfbHomFilteredColimit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]

/-- Transparent type abbreviation for the recorded module category, not a new category.
Source: Stacks, Modules on Sites (blueprint: def-sfb-internal-hom-strict-models). -/
abbrev Modules (R : Sheaf J CommRingCat.{max u v r}) :=
  ringedSiteModules.{max u v r} ((sheafCompose J
    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)

/-- The degree-zero coefficient tensor bifunctor, using the recorded total tensor.
Source: Stacks 06YN (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensor (R : Sheaf J CommRingCat.{max u v r}) :
    Modules.{u, v, r} J R × CochainComplex (Modules.{u, v, r} J R) ℤ ⥤
      CochainComplex (Modules.{u, v, r} J R) ℤ :=
  ((HomologicalComplex.single (Modules.{u, v, r} J R) (ComplexShape.up ℤ) 0).prod (𝟭 _)) ⋙
    coefficientTotalTensor.{r, u, v} J R

/-- Tensor a variable coefficient module with a fixed complex.
Source: Stacks 06YN (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensorFixed (R : Sheaf J CommRingCat.{max u v r})
    (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    Modules.{u, v, r} J R ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  Prod.sectL _ B ⋙ tensor.{u, v, r} J R

/-- The actual Hom-complex representative with fixed first input and the recorded
functorial K-injective replacement in its second input.
Source: Stacks 0A95 (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def homFixed (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    CochainComplex (Modules.{u, v, r} J R) ℤ ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ :=
  coefficientHomResolution.{r, u, v} J R ⋙
    (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj (op P)

/-- The tensor generator in degree `(0,n)`, using the actual single-complex comparison.
Source: Stacks 06YN, 03EK (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def tensorGenerator (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    (((tensor.{u, v, r} J R).obj (T, B)).X n).val.obj U :=
  coefficientTensorGenerator.{r, u, v} J R
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T) B 0 n n (zero_add n) U
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).inv).val.app U t) b

/-- Evaluate a Hom-complex component, with no chosen evaluation map.
Source: Stacks 0A8X (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def homValue (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (h : p + n = q)
    (U : Cᵒᵖ) (f : ((homComplex (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((homComplexπ.{u, v, max u v r, max u v r} (J := J) (R := R) P Q n p q h).val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x

/-- The actual augmentation of the fixed K-injective replacement.
Source: Stacks 079P (blueprint: def-sfb-internal-hom-strict-models). -/
noncomputable def resolutionUnit (R : Sheaf J CommRingCat.{max u v r}) :
    𝟭 (CochainComplex (Modules.{u, v, r} J R) ℤ) ⟶ coefficientHomResolution.{r, u, v} J R :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  CochainComplex.toKInjectiveResolution.{max u v r} _

/-- The evaluation normalization of the strict comparison `a_T` in proof step 6.
Source: the node's ring-sheaf argument, step 6; Stacks 08J9
(blueprint: def-sfb-internal-hom-strict-models). -/
def Normalized (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P) : Prop :=
  ∀ (T : Modules.{u, v, r} J R) (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ)
    (t : T.val.obj U) (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    homValue.{u, v, r} J R P
        ((coefficientHomResolution.{r, u, v} J R).obj
          ((tensor.{u, v, r} J R).obj
            (T, (coefficientHomResolution.{r, u, v} J R).obj L))) n p q h U
        (((a.app T).f n).val.app U (tensorGenerator.{u, v, r} J R T _ n U t f)) x =
      (((resolutionUnit.{u, v, r} J R).app
          ((tensor.{u, v, r} J R).obj
            (T, (coefficientHomResolution.{r, u, v} J R).obj L))).f q).val.app U
        (tensorGenerator.{u, v, r} J R T _ q U t
          (homValue.{u, v, r} J R P
            ((coefficientHomResolution.{r, u, v} J R).obj L) n p q h U f x))

section ComparisonProof

open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency true

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

-- Pure tensors are the sheafification unit followed by the tensor comparison.
private noncomputable def tensorSectionMap (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) :
    letI := SheafOfModules.monoidalCategory R
    A.val ⊗ B.val ⟶ (A ⊗ B).val :=
  (PresheafOfModules.sheafificationAdjunction.{max u v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r}
      RingCat.{max u v r})).obj R).obj)).unit.app (A.val ⊗ B.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val

private noncomputable def pure (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :=
  (tensorSectionMap.{u, v, r} J R A B).app U (a ⊗ₜ[R.obj.obj U] b)

private theorem pure_restrict (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (a : A.val.obj U) (b : B.val.obj U) :
    let := SheafOfModules.monoidalCategory R
    (A ⊗ B).val.map i (pure.{u, v, r} J R A B U a b) =
      pure.{u, v, r} J R A B V (A.val.map i a) (B.val.map i b) := by
  let := SheafOfModules.monoidalCategory R
  exact (PresheafOfModules.naturality_apply (tensorSectionMap.{u, v, r} J R A B) i
    (a ⊗ₜ[R.obj.obj U] b)).symm

private theorem adjunction_tensor_natural
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G) [F.OplaxMonoidal]
    {A A' B B' : E} (f : A ⟶ A') (g : B ⟶ B') :
    adj.unit.app (G.obj A ⊗ G.obj B) ≫
        G.map (Functor.OplaxMonoidal.δ F _ _ ≫
          (adj.counit.app A ⊗ₘ adj.counit.app B)) ≫ G.map (f ⊗ₘ g) =
      (G.map f ⊗ₘ G.map g) ≫ adj.unit.app (G.obj A' ⊗ G.obj B') ≫
        G.map (Functor.OplaxMonoidal.δ F _ _ ≫
          (adj.counit.app A' ⊗ₘ adj.counit.app B')) := by
  let : G.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have hn := (Functor.LaxMonoidal.μ_natural G f g).symm
  change (adj.unit.app (G.obj A ⊗ G.obj B) ≫
      G.map (Functor.OplaxMonoidal.δ F _ _ ≫
        (adj.counit.app A ⊗ₘ adj.counit.app B))) ≫ G.map (f ⊗ₘ g) =
    (G.map f ⊗ₘ G.map g) ≫ adj.unit.app (G.obj A' ⊗ G.obj B') ≫
      G.map (Functor.OplaxMonoidal.δ F _ _ ≫
        (adj.counit.app A' ⊗ₘ adj.counit.app B')) at hn
  simpa only [Category.assoc] using hn

private theorem tensorSectionMap_natural (R : Sheaf J CommRingCat.{max u v r})
    {A A' B B' : Modules.{u, v, r} J R} (f : A ⟶ A') (g : B ⟶ B') :
    let := SheafOfModules.monoidalCategory R
    tensorSectionMap.{u, v, r} J R A B ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ tensorSectionMap.{u, v, r} J R A' B' := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{max u v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
  let H := SheafOfModules.forget.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)
  let adj : S ⊣ H := PresheafOfModules.sheafificationAdjunction.{max u v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
  have hn := adjunction_tensor_natural S H adj f g
  dsimp only [H, SheafOfModules.forget, Functor.id_obj] at hn
  simp only [S, adj, tensorSectionMap, SheafOfModules.tensorObjIsoSheafification,
    Iso.trans_inv, Iso.symm_inv, tensorIso_hom, Iso.app_hom, asIso_hom,
    Functor.Monoidal.μIso_inv, SheafOfModules.comp_val] at hn ⊢
  erw [Category.assoc, Category.assoc]
  exact hn

private theorem pure_map (R : Sheaf J CommRingCat.{max u v r})
    {A A' B B' : Modules.{u, v, r} J R} (f : A ⟶ A') (g : B ⟶ B')
    (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    let := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g).val.app U (pure.{u, v, r} J R A B U a b) =
      pure.{u, v, r} J R A' B' U (f.val.app U a) (g.val.app U b) := by
  let := SheafOfModules.monoidalCategory R
  exact congrArg (fun k ↦ k.app U (a ⊗ₜ[R.obj.obj U] b))
    (tensorSectionMap_natural.{u, v, r} J R f g)

private theorem pure_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (A B Z : Modules.{u, v, r} J R) :
    let := SheafOfModules.monoidalCategory R
    ∀ (f g : A ⊗ B ⟶ Z),
      (∀ (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
        f.val.app U (pure.{u, v, r} J R A B U a b) =
          g.val.app U (pure.{u, v, r} J R A B U a b)) → f = g := by
  let := SheafOfModules.monoidalCategory R
  intro _ f g h
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification A B).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  exact h U a b

private noncomputable def singleTensorIso (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    let := SheafOfModules.monoidalCategory R
    (tensor.{u, v, r} J R).obj (T, B) ≅
      ((MonoidalCategory.tensorLeft T).mapHomologicalComplex (.up ℤ)).obj B := by
  let := SheafOfModules.monoidalCategory R
  exact CochainComplex.mapBifunctorSingle₁Iso (MonoidalCategory.curriedTensor _) T B

set_option backward.isDefEq.respectTransparency false in
private theorem tensorGenerator_eq (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    let := SheafOfModules.monoidalCategory R
    tensorGenerator.{u, v, r} J R T B n U t b =
      (((singleTensorIso.{u, v, r} J R T B).inv).f n).val.app U
        (pure.{u, v, r} J R T (B.X n) U t b) := by
  let := SheafOfModules.monoidalCategory R
  rw [show (singleTensorIso.{u, v, r} J R T B).inv.f n =
    ((curriedTensor _).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv).app
      (B.X n) ≫ HomologicalComplex.ιMapBifunctor
        ((HomologicalComplex.single _ (.up ℤ) 0).obj T) B (curriedTensor _)
        (.up ℤ) 0 n n (zero_add n) from
    CochainComplex.mapBifunctorSingle₁Iso_inv_f _ _ _ _]
  have he := pure_map.{u, v, r} J R
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv (𝟙 (B.X n)) U t b
  change (HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj T) B (curriedTensor _)
      (.up ℤ) 0 n n (zero_add n)).val.app U
        (pure.{u, v, r} J R _ (B.X n) U
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) b) =
    (HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj T) B (curriedTensor _)
      (.up ℤ) 0 n n (zero_add n)).val.app U
        (((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv ▷ B.X n).val.app U
          (pure.{u, v, r} J R T (B.X n) U t b))
  exact congrArg
    ((HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single _ (.up ℤ) 0).obj T) B (curriedTensor _)
      (.up ℤ) 0 n n (zero_add n)).val.app U)
    (by simpa only [SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply, tensorHom_id] using he.symm)

attribute [local irreducible] singleTensorIso

private theorem pure_add_left (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (a a' : A.val.obj U) (b : B.val.obj U) :
    pure.{u, v, r} J R A B U (a + a') b =
      pure.{u, v, r} J R A B U a b + pure.{u, v, r} J R A B U a' b := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact ((tensorSectionMap.{u, v, r} J R A B).app U).hom.map_add _ _

private theorem pure_add_right (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (a : A.val.obj U) (b b' : B.val.obj U) :
    pure.{u, v, r} J R A B U a (b + b') =
      pure.{u, v, r} J R A B U a b + pure.{u, v, r} J R A B U a b' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact ((tensorSectionMap.{u, v, r} J R A B).app U).hom.map_add _ _

private theorem pure_smul_left (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (c : R.obj.obj U) :
    pure.{u, v, r} J R A B U (c • a) b = c • pure.{u, v, r} J R A B U a b := by
  exact (tensorSectionMap.{u, v, r} J R A B).app U |>.hom.map_smul c (a ⊗ₜ[R.obj.obj U] b)

private theorem pure_smul_right (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (c : R.obj.obj U) :
    pure.{u, v, r} J R A B U a (c • b) = c • pure.{u, v, r} J R A B U a b := by
  change (tensorSectionMap.{u, v, r} J R A B).app U (a ⊗ₜ[R.obj.obj U] (c • b)) = _
  rw [TensorProduct.tmul_smul]
  exact ((tensorSectionMap.{u, v, r} J R A B).app U).hom.map_smul c _

attribute [local irreducible] pure

-- Construct the sheaf-level map t ⊗ f ↦ (x ↦ t ⊗ f(x)) before assembling degrees.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def strengthSection (R : Sheaf J CommRingCat.{max u v r})
    (T M N : Modules.{u, v, r} J R) (U : Cᵒᵖ) (t : T.val.obj U)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U) :
    letI := SheafOfModules.monoidalCategory R
    (SheafOfModules.homObj (R := R) M (T ⊗ N)).val.obj U := by
  let := SheafOfModules.monoidalCategory R
  refine
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun x ↦ pure.{u, v, r} J R T N (op W.unop.left)
            (T.val.map W.unop.hom.op t) (f.app W x)
          map_add' := ?_
          map_smul' := ?_ }
      naturality := ?_ }
  · intro x y
    erw [(f.app W).hom.map_add, pure_add_right]
  · intro c x
    erw [(f.app W).hom.map_smul, pure_smul_right]
    rfl
  · intro W W' i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pure.{u, v, r} J R T N (op W'.unop.left) (T.val.map W'.unop.hom.op t)
        (f.app W' (M.val.map i.unop.left.op x)) =
      (T ⊗ N).val.map i.unop.left.op
        (pure.{u, v, r} J R T N (op W.unop.left) (T.val.map W.unop.hom.op t) (f.app W x))
    erw [pure_restrict, ← PresheafOfModules.naturality_apply f i x]
    congr 1
    rw [← T.val.map_comp_apply, ← op_comp, Over.w]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def strengthBilinear (R : Sheaf J CommRingCat.{max u v r})
    (T M N : Modules.{u, v, r} J R) (U : Cᵒᵖ) :
    letI := SheafOfModules.monoidalCategory R
    T.val.obj U →ₗ[R.obj.obj U]
      (SheafOfModules.homObj (R := R) M N).val.obj U →ₗ[R.obj.obj U]
        (SheafOfModules.homObj (R := R) M (T ⊗ N)).val.obj U := by
  let := SheafOfModules.monoidalCategory R
  refine
    { toFun := fun t ↦
        { toFun := strengthSection.{u, v, r} J R T M N U t
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pure.{u, v, r} J R T N (op W.unop.left) _ ((f + g).app W x) = _
    change pure.{u, v, r} J R T N (op W.unop.left) _ (f.app W x + g.app W x) = _
    exact pure_add_right.{u, v, r} J R T N _ _ _ _
  · intro c f
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pure.{u, v, r} J R T N (op W.unop.left) _ ((R.obj.map W.unop.hom.op c) • f.app W x) = _
    exact pure_smul_right.{u, v, r} J R T N _ _ _ _
  · intro t s
    apply LinearMap.ext
    intro f
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pure.{u, v, r} J R T N (op W.unop.left) (T.val.map W.unop.hom.op (t + s)) _ = _
    erw [(T.val.map W.unop.hom.op).hom.map_add]
    exact pure_add_left.{u, v, r} J R T N _ _ _ _
  · intro c t
    apply LinearMap.ext
    intro f
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pure.{u, v, r} J R T N (op W.unop.left) (T.val.map W.unop.hom.op (c • t)) _ = _
    erw [T.val.map_smul]
    exact pure_smul_left.{u, v, r} J R T N _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def strengthRaw (R : Sheaf J CommRingCat.{max u v r})
    (T M N : Modules.{u, v, r} J R) :
    letI := SheafOfModules.monoidalCategory R
    T.val ⊗ (SheafOfModules.homObj (R := R) M N).val ⟶
      (SheafOfModules.homObj (R := R) M (T ⊗ N)).val := by
  let := SheafOfModules.monoidalCategory R
  refine
    { app := fun U ↦ ModuleCat.ofHom
        (X := (T.val ⊗ (SheafOfModules.homObj (R := R) M N).val).obj U)
        (Y := (SheafOfModules.homObj (R := R) M (T ⊗ N)).val.obj U)
        (TensorProduct.lift (strengthBilinear.{u, v, r} J R T M N U))
      naturality := ?_ }
  intro U V i
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro t f
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change pure.{u, v, r} J R T N (op W.unop.left)
      (T.val.map W.unop.hom.op (T.val.map i t))
      (f.app (op ((Over.map i.unop).obj W.unop)) x) =
    pure.{u, v, r} J R T N (op W.unop.left)
      (T.val.map (((Over.map i.unop).obj W.unop).hom).op t)
      (f.app (op ((Over.map i.unop).obj W.unop)) x)
  exact congrArg (fun z ↦ pure.{u, v, r} J R T N (op W.unop.left) z
    (f.app (op ((Over.map i.unop).obj W.unop)) x))
      (T.val.map_comp_apply i W.unop.hom.op t).symm

private noncomputable def strength (R : Sheaf J CommRingCat.{max u v r})
    (T M N : Modules.{u, v, r} J R) :
    letI := SheafOfModules.monoidalCategory R
    T ⊗ SheafOfModules.homObj (R := R) M N ⟶
      SheafOfModules.homObj (R := R) M (T ⊗ N) := by
  let := SheafOfModules.monoidalCategory R
  exact (SheafOfModules.tensorObjIsoSheafification T
    (SheafOfModules.homObj (R := R) M N)).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).symm
      (strengthRaw.{u, v, r} J R T M N)

private theorem adjunction_lift_unit
    {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) (G : E ⥤ D) (adj : F ⊣ G)
    {X : D} {Y Z : E} (e : Y ≅ F.obj X) (q : X ⟶ G.obj Z) :
    adj.unit.app X ≫ G.map e.inv ≫ G.map (e.hom ≫ (adj.homEquiv X Z).symm q) = q := by
  have hi : G.map e.inv ≫ G.map e.hom = 𝟙 _ := by
    rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
  rw [G.map_comp, ← Category.assoc (G.map e.inv), hi, Category.id_comp]
  exact (adj.homEquiv X Z).apply_symm_apply q

set_option backward.isDefEq.respectTransparency false in
private theorem strength_apply (R : Sheaf J CommRingCat.{max u v r})
    (T M N : Modules.{u, v, r} J R) (U : Cᵒᵖ) (t : T.val.obj U)
    (f : (SheafOfModules.homObj (R := R) M N).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : M.val.obj (op W.unop.left)) :
    letI := SheafOfModules.monoidalCategory R
    (((strength.{u, v, r} J R T M N).val.app U
      (pure.{u, v, r} J R T (SheafOfModules.homObj (R := R) M N) U t f)).app W).hom x =
        pure.{u, v, r} J R T N (op W.unop.left) (T.val.map W.unop.hom.op t) (f.app W x) := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{max u v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
  let H := SheafOfModules.forget.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)
  let adj : S ⊣ H := PresheafOfModules.sheafificationAdjunction.{max u v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).obj)
  let e := SheafOfModules.tensorObjIsoSheafification T
    (SheafOfModules.homObj (R := R) M N)
  have hs := adjunction_lift_unit S H adj e
    (Z := SheafOfModules.homObj (R := R) M (T ⊗ N))
    (strengthRaw.{u, v, r} J R T M N)
  rw [← Category.assoc] at hs
  change tensorSectionMap.{u, v, r} J R T (SheafOfModules.homObj (R := R) M N) ≫
    (strength.{u, v, r} J R T M N).val = strengthRaw.{u, v, r} J R T M N at hs
  have he := congrArg (fun k ↦ ((k.app U (t ⊗ₜ[R.obj.obj U] f)).app W).hom x) hs
  change (((strength.{u, v, r} J R T M N).val.app U
    ((tensorSectionMap.{u, v, r} J R T (SheafOfModules.homObj (R := R) M N)).app U
      (t ⊗ₜ[R.obj.obj U] f))).app W).hom x =
    pure.{u, v, r} J R T N (op W.unop.left) (T.val.map W.unop.hom.op t) (f.app W x) at he
  simpa only [pure] using he

attribute [local irreducible] strengthSection strengthBilinear strengthRaw strength

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_to_homObj_ext (R : Sheaf J CommRingCat.{max u v r})
    (T A M N : Modules.{u, v, r} J R) :
    let := SheafOfModules.monoidalCategory R
    ∀ (a b : T ⊗ A ⟶ SheafOfModules.homObj (R := R) M N),
      (∀ (U : Cᵒᵖ) (t : T.val.obj U) (z : A.val.obj U) (x : M.val.obj U),
        ((a.val.app U (pure.{u, v, r} J R T A U t z)).app
            (op (Over.mk (𝟙 U.unop)))).hom x =
          ((b.val.app U (pure.{u, v, r} J R T A U t z)).app
            (op (Over.mk (𝟙 U.unop)))).hom x) → a = b := by
  let := SheafOfModules.monoidalCategory R
  intro _ a b hab
  apply pure_hom_ext.{u, v, r} J R T A _ a b
  intro U t z
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have ha := PresheafOfModules.naturality_apply a.val W.unop.hom.op
    (pure.{u, v, r} J R T A U t z)
  have hb := PresheafOfModules.naturality_apply b.val W.unop.hom.op
    (pure.{u, v, r} J R T A U t z)
  have hh := hab (op W.unop.left) (T.val.map W.unop.hom.op t)
    (A.val.map W.unop.hom.op z) x
  rw [← pure_restrict.{u, v, r} J R T A W.unop.hom.op t z] at hh
  rw [ha, hb] at hh
  change ((a.val.app U (pure.{u, v, r} J R T A U t z)).app
        (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))).hom x =
    ((b.val.app U (pure.{u, v, r} J R T A U t z)).app
        (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))).hom x at hh
  exact (PresheafOfModules.restrictOver_hom_app_congr
    (a.val.app U (pure.{u, v, r} J R T A U t z))
    (Category.id_comp W.unop.hom) x).symm.trans
      (hh.trans (PresheafOfModules.restrictOver_hom_app_congr
        (b.val.app U (pure.{u, v, r} J R T A U t z))
        (Category.id_comp W.unop.hom) x))

private theorem tensor_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (T A : Modules.{u, v, r} J R)
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n : ℤ) :
    let := SheafOfModules.monoidalCategory R
    ∀ (a b : T ⊗ A ⟶ (homComplex (R := R) P Q).X n),
      (∀ (p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
        (t : T.val.obj U) (z : A.val.obj U) (x : (P.X p).val.obj U),
        homValue.{u, v, r} J R P Q n p q hpq U
            (a.val.app U (pure.{u, v, r} J R T A U t z)) x =
          homValue.{u, v, r} J R P Q n p q hpq U
            (b.val.app U (pure.{u, v, r} J R T A U t z)) x) → a = b := by
  let := SheafOfModules.monoidalCategory R
  intro _ a b hab
  apply homComplex_hom_ext
  intro p q hpq
  apply tensor_to_homObj_ext.{u, v, r} J R T A (P.X p) (Q.X q)
  exact hab p q hpq

private theorem tensor_degree_exists (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (P Q V : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    let := SheafOfModules.monoidalCategory R
    ∀ (τ : ((tensorLeft T).mapHomologicalComplex (.up ℤ)).obj Q ⟶ V) (n : ℤ),
    ∃ a : T ⊗ (homComplex (R := R) P Q).X n ⟶ (homComplex (R := R) P V).X n,
      ∀ (p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
        (t : T.val.obj U) (z : ((homComplex (R := R) P Q).X n).val.obj U)
        (x : (P.X p).val.obj U),
        homValue.{u, v, r} J R P V n p q hpq U
            (a.val.app U (pure.{u, v, r} J R T _ U t z)) x =
          (τ.f q).val.app U (pure.{u, v, r} J R T (Q.X q) U t
            (homValue.{u, v, r} J R P Q n p q hpq U z x)) := by
  let := SheafOfModules.monoidalCategory R
  intro _ τ n
  let c (p : ℤ) : T ⊗ (homComplex (R := R) P Q).X n ⟶
      SheafOfModules.homObj (R := R) (P.X p) (V.X (p + n)) :=
    (𝟙 T ⊗ₘ homComplexπ P Q n p (p + n) rfl) ≫
      strength.{u, v, r} J R T (P.X p) (Q.X (p + n)) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (P.X p)) (τ.f (p + n))
  let a := Fan.IsLimit.lift (homComplexIsLimit (R := R) P V n) c
  refine ⟨a, ?_⟩
  intro p q hpq U t z x
  subst q
  have hπ : a ≫ homComplexπ P V n p (p + n) rfl = c p :=
    Fan.IsLimit.fac (homComplexIsLimit (R := R) P V n) c p
  have he := congrArg (fun k ↦ ((k.val.app U
    (pure.{u, v, r} J R T _ U t z)).app (op (Over.mk (𝟙 U.unop)))).hom x) hπ
  change homValue.{u, v, r} J R P V n p (p + n) rfl U
      (a.val.app U (pure.{u, v, r} J R T _ U t z)) x =
    (τ.f (p + n)).val.app U
      ((((strength.{u, v, r} J R T (P.X p) (Q.X (p + n))).val.app U
        ((𝟙 T ⊗ₘ homComplexπ P Q n p (p + n) rfl).val.app U
          (pure.{u, v, r} J R T _ U t z))).app (op (Over.mk (𝟙 U.unop)))).hom x) at he
  rw [pure_map.{u, v, r} J R] at he
  have hs := strength_apply.{u, v, r} J R T (P.X p) (Q.X (p + n)) U t
    ((homComplexπ P Q n p (p + n) rfl).val.app U z)
    (op (Over.mk (𝟙 U.unop))) x
  have hid : T.val.map (𝟙 U) t = t :=
    ConcreteCategory.congr_hom (T.val.presheaf.map_id U) t
  change _ = pure.{u, v, r} J R T (Q.X (p + n)) U (T.val.map (𝟙 U) t)
    (homValue.{u, v, r} J R P Q n p (p + n) rfl U z x) at hs
  rw [hid] at hs
  simpa only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
    using he.trans (congrArg ((τ.f (p + n)).val.app U) hs)

private theorem map_units {A B F : Type*} [AddCommGroup A] [AddCommGroup B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F) (e : ℤˣ) (x : A) :
    f (e • x) = e • f x := map_zsmul f (e : ℤ) x

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency true in
private theorem hom_section_sub_units (R : Sheaf J CommRingCat.{max u v r})
    (A B D : Modules.{u, v, r} J R)
    (f g : D ⟶ SheafOfModules.homObj (R := R) A B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : D.val.obj U) (x : A.val.obj U) :
    ((((f - e • g).val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x =
      (((f.val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x -
        e • (((g.val.app U).hom s).app (op (Over.mk (𝟙 U.unop)))).hom x := by
  let R₀ := (sheafCompose J
    (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj U
  have he : ((f - e • g).val.app U).hom s =
      (f.val.app U).hom s - e • (g.val.app U).hom s := by
    change (V.map (f - e • g)).hom s = _
    rw [Functor.map_sub]
    simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
      ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    rfl
  rw [he]
  change (((((f.val.app U).hom s - (e : ℤ) • (g.val.app U).hom s) :
    (PresheafOfModules.restrictOver R.obj U.unop).obj A.val ⟶
      (PresheafOfModules.restrictOver R.obj U.unop).obj B.val).app
        (op (Over.mk (𝟙 U.unop)))).hom x) = _
  erw [PresheafOfModules.sub_app, PresheafOfModules.zsmul_app,
    ModuleCat.hom_sub, ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homValue_d (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) (U : Cᵒᵖ)
    (z : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q m p q hpq U
        (((homComplex (R := R) P Q).d n m).val.app U z) x =
      (Q.d q' q).val.app U (homValue.{u, v, r} J R P Q n p q' hq' U z x) -
        n.negOnePow • homValue.{u, v, r} J R P Q n p' q hp' U z
          ((P.d p p').val.app U x) := by
  have he := congrArg
    (fun f : (homComplex (R := R) P Q).X n ⟶
        SheafOfModules.homObj (R := R) (P.X p) (Q.X q) ↦
      ((f.val.app U z).app (op (Over.mk (𝟙 U.unop)))).hom x)
    (homComplex_d_π P Q n m p q q' p' hnm hpq hq' hp')
  rw [hom_section_sub_units.{u, v, r} J R] at he
  unfold homValue
  exact he

private theorem pure_sub_units (R : Sheaf J CommRingCat.{max u v r})
    (A B : Modules.{u, v, r} J R) (U : Cᵒᵖ)
    (a : A.val.obj U) (b b' : B.val.obj U) (e : ℤˣ) :
    pure.{u, v, r} J R A B U a (b - e • b') =
      pure.{u, v, r} J R A B U a b - e • pure.{u, v, r} J R A B U a b' := by
  let := SheafOfModules.monoidalCategory R
  let k : B.val.obj U →ₗ[R.obj.obj U] (A ⊗ B).val.obj U :=
    ((tensorSectionMap.{u, v, r} J R A B).app U).hom.comp
      ((TensorProduct.mk (R.obj.obj U) (A.val.obj U) (B.val.obj U)) a)
  unfold pure
  change k (b - e • b') = k b - e • k b'
  rw [map_sub, map_units]

attribute [local irreducible] homValue

-- Hom-product projections reduce the chain condition to the Hom differential formula.
private theorem tensor_evaluation_exists (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (P Q V : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    let := SheafOfModules.monoidalCategory R
    ∀ (τ : ((tensorLeft T).mapHomologicalComplex (.up ℤ)).obj Q ⟶ V),
    ∃ a : ((tensorLeft T).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := R) P Q) ⟶ homComplex (R := R) P V,
      ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
        (t : T.val.obj U) (z : ((homComplex (R := R) P Q).X n).val.obj U)
        (x : (P.X p).val.obj U),
        homValue.{u, v, r} J R P V n p q hpq U
            ((a.f n).val.app U (pure.{u, v, r} J R T _ U t z)) x =
          (τ.f q).val.app U (pure.{u, v, r} J R T (Q.X q) U t
            (homValue.{u, v, r} J R P Q n p q hpq U z x)) := by
  classical
  let := SheafOfModules.monoidalCategory R
  intro _ τ
  choose a ha using tensor_degree_exists.{u, v, r} J R T P Q V τ
  let H := homComplex (R := R) P Q
  let G := homComplex (R := R) P V
  have hc (n m : ℤ) (hnm : n + 1 = m) :
      a n ≫ G.d n m = (tensorLeft T).map (H.d n m) ≫ a m := by
    apply tensor_hom_ext.{u, v, r} J R T (H.X n) P V m
    intro p q hpq U t z x
    change homValue.{u, v, r} J R P V m p q hpq U
        ((G.d n m).val.app U ((a n).val.app U
          (pure.{u, v, r} J R T (H.X n) U t z))) x =
      homValue.{u, v, r} J R P V m p q hpq U
        ((a m).val.app U (((tensorLeft T).map (H.d n m)).val.app U
          (pure.{u, v, r} J R T (H.X n) U t z))) x
    conv_lhs =>
      rw [homValue_d.{u, v, r} J R P V n m p q (p + n) (p + 1)
        hnm hpq rfl (by omega)]
    have hmap := pure_map.{u, v, r} J R (𝟙 T) (H.d n m) U t z
    simp only [id_tensorHom, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at hmap
    change ((tensorLeft T).map (H.d n m)).val.app U
        (pure.{u, v, r} J R T (H.X n) U t z) =
      pure.{u, v, r} J R T (H.X m) U t ((H.d n m).val.app U z) at hmap
    conv_rhs =>
      rw [hmap, ha m p q hpq U t ((H.d n m).val.app U z) x]
      rw [homValue_d.{u, v, r} J R P Q n m p q (p + n) (p + 1)
        hnm hpq rfl (by omega)]
    conv_lhs =>
      lhs
      rw [ha n p (p + n) rfl U t z x]
    conv_lhs =>
      rhs
      rw [ha n (p + 1) q (by omega) U t z ((P.d p (p + 1)).val.app U x)]
    have htau := congrArg
      (fun k : T ⊗ Q.X (p + n) ⟶ V.X q ↦ k.val.app U
        (pure.{u, v, r} J R T (Q.X (p + n)) U t
          (homValue.{u, v, r} J R P Q n p (p + n) rfl U z x)))
      (τ.comm (p + n) q)
    change (V.d (p + n) q).val.app U ((τ.f (p + n)).val.app U _) =
      (τ.f q).val.app U (((tensorLeft T).map (Q.d (p + n) q)).val.app U _) at htau
    have hmapQ := pure_map.{u, v, r} J R (𝟙 T) (Q.d (p + n) q) U t
      (homValue.{u, v, r} J R P Q n p (p + n) rfl U z x)
    simp only [id_tensorHom, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at hmapQ
    change ((tensorLeft T).map (Q.d (p + n) q)).val.app U
        (pure.{u, v, r} J R T (Q.X (p + n)) U t _) =
      pure.{u, v, r} J R T (Q.X q) U t
        ((Q.d (p + n) q).val.app U _) at hmapQ
    conv_lhs => lhs; rw [htau, hmapQ]
    have he := congrArg ((τ.f q).val.app U)
      (pure_sub_units.{u, v, r} J R T (Q.X q) U t
        ((Q.d (p + n) q).val.app U
          (homValue.{u, v, r} J R P Q n p (p + n) rfl U z x))
        (homValue.{u, v, r} J R P Q n (p + 1) q (by omega) U z
          ((P.d p (p + 1)).val.app U x)) n.negOnePow)
    erw [map_sub, map_units] at he
    exact he.symm
  refine ⟨{ f := a, comm' := fun n m hnm ↦ hc n m hnm }, ?_⟩
  exact fun n p q hpq U t z x ↦ ha n p q hpq U t z x

private theorem tensorGenerator_hom_ext (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R)
    (B P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n m : ℤ)
    (a b : ((tensor.{u, v, r} J R).obj (T, B)).X n ⟶
      (homComplex (R := R) P Q).X m)
    (h : ∀ (p q : ℤ) (hpq : p + m = q) (U : Cᵒᵖ)
      (t : T.val.obj U) (z : (B.X n).val.obj U) (x : (P.X p).val.obj U),
      homValue.{u, v, r} J R P Q m p q hpq U
          (a.val.app U (tensorGenerator.{u, v, r} J R T B n U t z)) x =
        homValue.{u, v, r} J R P Q m p q hpq U
          (b.val.app U (tensorGenerator.{u, v, r} J R T B n U t z)) x) : a = b := by
  let := SheafOfModules.monoidalCategory R
  apply (cancel_epi ((singleTensorIso.{u, v, r} J R T B).inv.f n)).mp
  apply tensor_hom_ext.{u, v, r} J R T (B.X n) P Q m
  intro p q hpq U t z x
  change homValue.{u, v, r} J R P Q m p q hpq U
    (a.val.app U (((singleTensorIso.{u, v, r} J R T B).inv.f n).val.app U
      (pure.{u, v, r} J R T (B.X n) U t z))) x =
    homValue.{u, v, r} J R P Q m p q hpq U
      (b.val.app U (((singleTensorIso.{u, v, r} J R T B).inv.f n).val.app U
        (pure.{u, v, r} J R T (B.X n) U t z))) x
  rw [← tensorGenerator_eq.{u, v, r} J R]
  exact h p q hpq U t z x

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_map_eq (R : Sheaf J CommRingCat.{max u v r})
    {T T' : Modules.{u, v, r} J R} (f : T ⟶ T')
    {B B' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : B ⟶ B') :
    let := SheafOfModules.monoidalCategory R
    (tensor.{u, v, r} J R).map (X := (T, B)) (Y := (T', B')) (f, g) =
      HomologicalComplex.mapBifunctorMap
      ((HomologicalComplex.single (Modules.{u, v, r} J R) (.up ℤ) 0).map f) g
      (curriedTensor _) (.up ℤ) := by
  let := SheafOfModules.monoidalCategory R
  let S := HomologicalComplex.single (Modules.{u, v, r} J R) (.up ℤ) 0
  change HomologicalComplex.mapBifunctorMap (S.map f) (𝟙 B) (curriedTensor _) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 (S.obj T')) g (curriedTensor _) (.up ℤ) = _
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f]
  simp only [curriedTensor_obj_map, curriedTensor_map_app, whiskerLeft_id,
    id_whiskerRight]
  erw [Category.id_comp, Category.id_comp]

private theorem tensorGenerator_ι (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    let := SheafOfModules.monoidalCategory R
    tensorGenerator.{u, v, r} J R T B n U t b =
      (HomologicalComplex.ιMapBifunctor
        ((HomologicalComplex.single _ (.up ℤ) 0).obj T) B (curriedTensor _)
        (.up ℤ) 0 n n (zero_add n)).val.app U
          (pure.{u, v, r} J R _ (B.X n) U
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) b) := by
  unfold tensorGenerator coefficientTensorGenerator pure tensorSectionMap
  rfl

attribute [local irreducible] tensorGenerator

private theorem tensorGenerator_map (R : Sheaf J CommRingCat.{max u v r})
    {T T' : Modules.{u, v, r} J R} (f : T ⟶ T')
    {B B' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : B ⟶ B')
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    (((tensor.{u, v, r} J R).map (X := (T, B)) (Y := (T', B')) (f, g)).f n).val.app U
        (tensorGenerator.{u, v, r} J R T B n U t b) =
      tensorGenerator.{u, v, r} J R T' B' n U (f.val.app U t) ((g.f n).val.app U b) := by
  let := SheafOfModules.monoidalCategory R
  rw [tensor_map_eq.{u, v, r} J R f g, tensorGenerator_ι.{u, v, r} J R,
    tensorGenerator_ι.{u, v, r} J R]
  let S := HomologicalComplex.single (Modules.{u, v, r} J R) (.up ℤ) 0
  have hi := HomologicalComplex.ι_mapBifunctorMap (S.map f) g (curriedTensor _)
    (.up ℤ) 0 n n (zero_add n)
  simp only [curriedTensor_map_app, curriedTensor_obj_map] at hi
  rw [← Category.assoc, ← tensorHom_def] at hi
  have he := congrArg (fun k ↦ k.val.app U
    (pure.{u, v, r} J R ((S.obj T).X 0) (B.X n) U
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) b)) hi
  change ((HomologicalComplex.mapBifunctorMap (S.map f) g (curriedTensor _) (.up ℤ)).f n).val.app U
      ((HomologicalComplex.ιMapBifunctor (S.obj T) B (curriedTensor _)
        (.up ℤ) 0 n n (zero_add n)).val.app U
          (pure.{u, v, r} J R ((S.obj T).X 0) (B.X n) U
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) b)) =
    (HomologicalComplex.ιMapBifunctor (S.obj T') B' (curriedTensor _)
      (.up ℤ) 0 n n (zero_add n)).val.app U
      (((S.map f).f 0 ⊗ₘ g.f n).val.app U
        (pure.{u, v, r} J R ((S.obj T).X 0) (B.X n) U
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) b)) at he
  rw [pure_map.{u, v, r} J R] at he
  have ht : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv ≫ (S.map f).f 0 =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T').inv := by
    dsimp only [S]
    rw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
  have hte := congrArg (fun k ↦ k.val.app U t) ht
  change ((S.map f).f 0).val.app U
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv.val.app U t) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T').inv.val.app U (f.val.app U t) at hte
  rw [hte] at he
  exact he

attribute [local irreducible] tensor

private theorem tensorGenerator_hom (R : Sheaf J CommRingCat.{max u v r})
    (T : Modules.{u, v, r} J R) (B : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U) (b : (B.X n).val.obj U) :
    let := SheafOfModules.monoidalCategory R
    ((singleTensorIso.{u, v, r} J R T B).hom.f n).val.app U
        (tensorGenerator.{u, v, r} J R T B n U t b) =
      pure.{u, v, r} J R T (B.X n) U t b := by
  let := SheafOfModules.monoidalCategory R
  rw [tensorGenerator_eq.{u, v, r} J R]
  exact congrArg (fun k ↦ (k.f n).val.app U (pure.{u, v, r} J R T (B.X n) U t b))
    (singleTensorIso.{u, v, r} J R T B).inv_hom_id

omit [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}] in
set_option backward.isDefEq.respectTransparency false in
private theorem homValue_map_right (R : Sheaf J CommRingCat.{max u v r})
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ)
    {Q Q' : CochainComplex (Modules.{u, v, r} J R) ℤ} (g : Q ⟶ Q')
    (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ)
    (z : ((homComplex (R := R) P Q).X n).val.obj U) (x : (P.X p).val.obj U) :
    homValue.{u, v, r} J R P Q' n p q hpq U
        (((((homComplexFunctor (R := R)).obj (op P)).map g).f n).val.app U z) x =
      (g.f q).val.app U (homValue.{u, v, r} J R P Q n p q hpq U z x) := by
  unfold homValue
  exact congrArg (fun k ↦ ((k.val.app U z).app (op (Over.mk (𝟙 U.unop)))).hom x)
    (homComplexFunctor_obj_map_f_π (R := R) g n p q hpq)

private theorem component_exists (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) (T : Modules.{u, v, r} J R) :
    ∃ a : (tensor.{u, v, r} J R).obj (T, (homFixed.{u, v, r} J R P).obj L) ⟶
      (homFixed.{u, v, r} J R P).obj ((tensor.{u, v, r} J R).obj
        (T, (coefficientHomResolution.{r, u, v} J R).obj L)),
      ∀ (n p q : ℤ) (hpq : p + n = q) (U : Cᵒᵖ) (t : T.val.obj U)
        (z : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
        (x : (P.X p).val.obj U),
        homValue.{u, v, r} J R P
          ((coefficientHomResolution.{r, u, v} J R).obj
            ((tensor.{u, v, r} J R).obj
              (T, (coefficientHomResolution.{r, u, v} J R).obj L))) n p q hpq U
          ((a.f n).val.app U (tensorGenerator.{u, v, r} J R T _ n U t z)) x =
        (((resolutionUnit.{u, v, r} J R).app ((tensor.{u, v, r} J R).obj
          (T, (coefficientHomResolution.{r, u, v} J R).obj L))).f q).val.app U
          (tensorGenerator.{u, v, r} J R T _ q U t
            (homValue.{u, v, r} J R P
              ((coefficientHomResolution.{r, u, v} J R).obj L) n p q hpq U z x)) := by
  let := SheafOfModules.monoidalCategory R
  let I := coefficientHomResolution.{r, u, v} J R
  let Q := I.obj L
  let B := (tensor.{u, v, r} J R).obj (T, Q)
  let V := I.obj B
  let τ := (singleTensorIso.{u, v, r} J R T Q).inv ≫ (resolutionUnit.{u, v, r} J R).app B
  obtain ⟨a, ha⟩ := tensor_evaluation_exists.{u, v, r} J R T P Q V τ
  refine ⟨(singleTensorIso.{u, v, r} J R T (homComplex (R := R) P Q)).hom ≫ a, ?_⟩
  intro n p q hpq U t z x
  change homValue.{u, v, r} J R P V n p q hpq U
    ((a.f n).val.app U
      (((singleTensorIso.{u, v, r} J R T (homComplex (R := R) P Q)).hom.f n).val.app U
        (tensorGenerator.{u, v, r} J R T _ n U t z))) x = _
  rw [tensorGenerator_hom.{u, v, r} J R, ha n p q hpq U t z x]
  change (((resolutionUnit.{u, v, r} J R).app B).f q).val.app U
    (((singleTensorIso.{u, v, r} J R T Q).inv.f q).val.app U
      (pure.{u, v, r} J R T (Q.X q) U t _)) = _
  rw [← tensorGenerator_eq.{u, v, r} J R]

/-- The strict evaluation comparisons exist uniquely, before any colimit or localization.
Source: the node's argument, step 6; Stacks 08J9
(blueprint: lem-sfb-internal-hom-comparison-exists).
Proof: send `t tensor f` to the cochain `x ↦ t tensor f(x)`, followed by the fixed
K-injective augmentation. Balancedness and restrictions give a sheaf map. The Hom
and total-tensor differentials give a chain map, with no sign since t has degree zero.
The same formula for a module map gives strict naturality. Sheafified pure tensors
and Hom-product projections determine every component, hence uniqueness. -/
theorem comparison_existsUnique (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    ∃! a : tensorFixed.{u, v, r} J R ((homFixed.{u, v, r} J R P).obj L) ⟶
      tensorFixed.{u, v, r} J R ((coefficientHomResolution.{r, u, v} J R).obj L) ⋙
        homFixed.{u, v, r} J R P,
      Normalized.{u, v, r} J R P L a := by
  classical
  let I := coefficientHomResolution.{r, u, v} J R
  let Q := I.obj L
  let H := (homFixed.{u, v, r} J R P).obj L
  let F := tensorFixed.{u, v, r} J R H
  let G := tensorFixed.{u, v, r} J R Q ⋙ homFixed.{u, v, r} J R P
  choose a ha using component_exists.{u, v, r} J R P L
  have nat {T T' : Modules.{u, v, r} J R} (f : T ⟶ T') :
      F.map f ≫ a T' = a T ≫ G.map f := by
    apply HomologicalComplex.hom_ext
    intro n
    apply tensorGenerator_hom_ext.{u, v, r} J R T H P
      (I.obj ((tensor.{u, v, r} J R).obj (T', Q))) n n
    intro p q hpq U t z x
    change homValue.{u, v, r} J R P
      (I.obj ((tensor.{u, v, r} J R).obj (T', Q))) n p q hpq U
      (((a T').f n).val.app U
        ((((tensor.{u, v, r} J R).map (X := (T, H)) (Y := (T', H)) (f, 𝟙 H)).f n).val.app U
          (tensorGenerator.{u, v, r} J R T H n U t z))) x =
      homValue.{u, v, r} J R P
        (I.obj ((tensor.{u, v, r} J R).obj (T', Q))) n p q hpq U
        (((((homComplexFunctor (R := R)).obj (op P)).map
          (I.map ((tensor.{u, v, r} J R).map (X := (T, Q)) (Y := (T', Q)) (f, 𝟙 Q)))).f n).val.app U
            (((a T).f n).val.app U
              (tensorGenerator.{u, v, r} J R T H n U t z))) x
    have hm := tensorGenerator_map.{u, v, r} J R f (𝟙 H) n U t z
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hm
    rw [hm, homValue_map_right.{u, v, r} J R P,
      ha T' n p q hpq U (f.val.app U t) z x, ha T n p q hpq U t z x]
    have he := congrArg (fun k ↦ (k.f q).val.app U
      (tensorGenerator.{u, v, r} J R T Q q U t
        (homValue.{u, v, r} J R P Q n p q hpq U z x)))
      ((resolutionUnit.{u, v, r} J R).naturality
        ((tensor.{u, v, r} J R).map (X := (T, Q)) (Y := (T', Q)) (f, 𝟙 Q)))
    change (((resolutionUnit.{u, v, r} J R).app
        ((tensor.{u, v, r} J R).obj (T', Q))).f q).val.app U
        ((((tensor.{u, v, r} J R).map (X := (T, Q)) (Y := (T', Q)) (f, 𝟙 Q)).f q).val.app U
          (tensorGenerator.{u, v, r} J R T Q q U t
            (homValue.{u, v, r} J R P Q n p q hpq U z x))) =
      ((I.map ((tensor.{u, v, r} J R).map (X := (T, Q)) (Y := (T', Q)) (f, 𝟙 Q))).f q).val.app U
        ((((resolutionUnit.{u, v, r} J R).app
          ((tensor.{u, v, r} J R).obj (T, Q))).f q).val.app U
            (tensorGenerator.{u, v, r} J R T Q q U t
              (homValue.{u, v, r} J R P Q n p q hpq U z x))) at he
    rw [tensorGenerator_map.{u, v, r} J R f (𝟙 Q)] at he
    simpa only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using he
  let α : F ⟶ G := { app := a, naturality := fun _ _ f ↦ nat f }
  refine ⟨α, ?_, ?_⟩
  · intro T n p q hpq U t z x
    exact ha T n p q hpq U t z x
  · intro b hb
    apply NatTrans.ext
    funext T
    apply HomologicalComplex.hom_ext
    intro n
    apply tensorGenerator_hom_ext.{u, v, r} J R T H P
      (I.obj ((tensor.{u, v, r} J R).obj (T, Q))) n n
    intro p q hpq U t z x
    exact (hb T n p q hpq U t z x).trans (ha T n p q hpq U t z x).symm

end ComparisonProof

/-- The uniquely evaluation-normalized comparison, not a choice of an arbitrary map.
Source: the node's argument, step 6 (blueprint: def-sfb-internal-hom-strict-roof). -/
noncomputable def comparison (R : Sheaf J CommRingCat.{max u v r})
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) :=
  (comparison_existsUnique.{u, v, r} J R P L).exists.choose

/-- Exact termwise-colimit continuity, expressed using the canonical cocone map.
Source: Bhatt--Scholze 6.8.12 and the node's continuity hypothesis
(blueprint: def-sfb-internal-hom-strict-roof). -/
def Continuous (R : Sheaf J CommRingCat.{max u v r})
    {I : Type (max u v r)} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I (Modules.{u, v, r} J R)]
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) : Prop :=
  ∀ (M : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (b : ℤ),
    (∀ (i : I) (n : ℤ), n < b → IsZero ((M.obj i).X n)) →
      QuasiIso (colimit.post M (homFixed.{u, v, r} J R P))

end WeilConjectures.SfbHomFilteredColimit
