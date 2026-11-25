/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.SixFunctors.Integral.IntegralHomReduction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
-- The successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Derived Hom and evaluation for extension from a pro-etale point

Source: Weil blueprint, main-20261015, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence; Stacks Tags 0A8X,
08J7, 0G7E and 08BJ (blueprint: def-pod-point-derived-hom-models).

All tensors here are ordinary tensors. The site retains object universe t+1 and
morphism universe t; the coefficient universe is max u (t+1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u r

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]

/-- Existing sheafification at the coefficient size, transported through a small model.
Source: Stacks 03DA (blueprint: def-pod-point-derived-hom-models). -/
instance abSheafify : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} (Spec (.of k))

/-- Existing local bijectivity criterion in the coefficient universe.
Source: Stacks 03DA (blueprint: def-pod-point-derived-hom-models). -/
instance abLocallyBijective : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} (Spec (.of k))

/-- The same small-model transport for commutative ring sheafification.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
instance ringLocallyBijective : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    CommRingCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The actual final object of the small pro-etale site.
Source: Stacks 098H (blueprint: def-pod-point-derived-hom-models). -/
abbrev finalObject := Scheme.ProEt.mk (𝟙 (Spec (.of k)))

variable (R : CommRingCat.{max u (t + 1)})

/-- The recorded constant ring sheaf, at the joint coefficient universe.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
abbrev constantRing := (constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
  CommRingCat.{max u (t + 1)}).obj R

/-- Forget commutativity of a coefficient sheaf without changing its sections.
Source: Stacks 03D1 (blueprint: def-pod-point-derived-hom-models). -/
abbrev ring (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{max u (t + 1)}) :=
  (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B

/-- The existing category of modules on the unchanged small site.
Source: Stacks 03D1 (blueprint: def-pod-point-derived-hom-models). -/
abbrev Modules (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{max u (t + 1)}) := SheafOfModules.{max u (t + 1)} (ring.{t, u} k B)

/-- Constant-ring sheafification's actual unit.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
def constantUnit : (Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
    ((forget₂ CommRingCat RingCat).obj R) ⟶ (ring.{t, u} k (constantRing.{t, u} k R)).obj :=
  Functor.whiskerRight (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
      (forget₂ CommRingCat RingCat)

/-- The existing local injectivity of ring sheafification, with commutativity forgotten.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
instance constantUnit_injective : Presheaf.IsLocallyInjective
    (Scheme.ProEt.topology (Spec (.of k))) (constantUnit.{t, u} k R) :=
  letI := ringLocallyBijective.{t, u} k
  (Presheaf.isLocallyInjective_forget_iff _ (constantUnit.{t, u} k R)).mp
    (inferInstanceAs (Presheaf.IsLocallyInjective _ (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
        (forget CommRingCat.{max u (t + 1)}))))

/-- The existing local surjectivity of ring sheafification.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
instance constantUnit_surjective : Presheaf.IsLocallySurjective
    (Scheme.ProEt.topology (Spec (.of k))) (constantUnit.{t, u} k R) :=
  letI := ringLocallyBijective.{t, u} k
  (Presheaf.isLocallySurjective_iff_whisker_forget _ (constantUnit.{t, u} k R)).mpr
    (inferInstanceAs (Presheaf.IsLocallySurjective _ (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R))
        (forget CommRingCat.{max u (t + 1)}))))

/-- Pull back the existing one-object constant-module presheaf to this site.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
def constantPresheaf : ModuleCat.{max u (t + 1)} R ⥤
    PresheafOfModules.{max u (t + 1)}
      ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj (RingCat.of R)) :=
  siteConstantModulePresheafGeneral (C := Discrete (ULift.{max u (t + 1)} Unit)) R ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const (Scheme.ProEt (Spec (.of k)))).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{max u (t + 1)} Unit))ᵒᵖ).obj (RingCat.of R))

/-- The genuine constant module sheaf, formed by associated-module sheafification.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
def constantModules : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k (constantRing.{t, u} k R) :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  constantPresheaf.{t, u} k R ⋙
    PresheafOfModules.sheafification.{max u (t + 1), t, max u (t + 1), t + 1}
      (constantUnit.{t, u} k R)

/-- Image of an actual module element under constant-module sheafification.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
def constantElement (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (x : M) :
    ((constantModules.{t, u} k R).obj M).val.obj U :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    (((constantPresheaf.{t, u} k R).obj M).presheaf)).app U x

variable {R} (B : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
  CommRingCat.{max u (t + 1)}) (α : constantRing.{t, u} k R ⟶ B)

/-- The canonical constant-value scalar map at each site object.
Source: Stacks 03CY (blueprint: def-pod-point-derived-hom-models). -/
def scalar (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) : R →+* B.obj.obj U :=
  (α.hom.app U).hom.comp ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj R)).app U).hom

/-- Sections with scalars restricted along the canonical constant-value map.
Source: Stacks 03CW (blueprint: def-pod-point-derived-hom-models). -/
def sections : Modules.{t, u} k B ⥤ ModuleCat.{max u (t + 1)} R :=
  SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj (op (finalObject k)) ⋙
    ModuleCat.restrictScalars (scalar.{t, u} k B α (op (finalObject k)))

/-- Evaluation and scalar restriction are the existing additive functors.
Source: Stacks 03CW (blueprint: def-pod-point-derived-hom-models). -/
instance sections_additive : (sections.{t, u} k B α).Additive :=
  inferInstanceAs ((SheafOfModules.forget (ring.{t, u} k B) ⋙
    PresheafOfModules.evaluation (ring.{t, u} k B).obj
    (op (finalObject k)) ⋙ ModuleCat.restrictScalars
      (scalar.{t, u} k B α (op (finalObject k)))).Additive)

/-- The actual local tensor generator of B tensor the constant module.
Source: Stacks 03EK (blueprint: def-pod-point-derived-hom-models). -/
def extensionElement (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (b : B.obj.obj U) (x : M) :
    (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} α
      ((constantModules.{t, u} k R).obj M)).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1), t, max u (t + 1), t + 1}
      (𝟙 (ring.{t, u} k B).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} α
      ((constantModules.{t, u} k R).obj M))).app U)
      (b ⊗ₜ[(constantRing.{t, u} k R).obj.obj U, (α.hom.app U).hom]
        constantElement.{t, u} k R M U x)

/-- Termwise application of the specified additive extension or sections functor.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
abbrev sectionComplex := (sections.{t, u} k B α).mapHomologicalComplex (.up ℤ)

/-- The recorded internal Hom complex, with all module and site universes explicit.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
abbrev sheafHom (P I : CochainComplex (Modules.{t, u} k B) ℤ) :=
  homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := B) P I

/-- The recorded product projection evaluated on the identity slice.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
abbrev homValue := IntegralHom.evaluate.{t, u} (Spec (.of k)) B

/-- The recorded ordinary direct-sum total tensor on the same small site.
Source: Stacks 06YL (blueprint: def-pod-point-derived-hom-models). -/
abbrev total (P Q : CochainComplex (Modules.{t, u} k B) ℤ) :=
  ((IntegralHom.totalTensor.{t, u} (Spec (.of k)) B).obj P).obj Q

section
variable {A : Type r} [CommRing A]

/-- The ordinary module total tensor, using the same totalization convention.
Source: Stacks 06YL (blueprint: def-pod-point-derived-hom-models). -/
abbrev moduleTotal (P Q : CochainComplex (ModuleCat.{r} A) ℤ) :=
  CochainComplex.mapBifunctor P Q (curriedTensor _)

end

/-- Restriction from the final object to an arbitrary object of the small site.
Source: Stacks 03CW (blueprint: def-pod-point-derived-hom-models). -/
def toFinal (U : Scheme.ProEt (Spec (.of k))) : U ⟶ finalObject k :=
  MorphismProperty.Over.homMk U.hom

/-- The actual extension object, with the coefficient-size sheafification fixed.
Source: Stacks 03EK (blueprint: def-pod-point-derived-hom-models). -/
def extensionObject (M : ModuleCat.{max u (t + 1)} R) : Modules.{t, u} k B :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} α
    ((constantModules.{t, u} k R).obj M)

/-- Tensor scalar extension of the actual constant-module morphism.
Source: Stacks 03EK (blueprint: def-pod-point-derived-hom-models). -/
def extensionMorphism {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N) :
    extensionObject.{t, u} k B α M ⟶ extensionObject.{t, u} k B α N :=
  letI := abSheafify.{t, u} k
  letI := abLocallyBijective.{t, u} k
  SheafOfModules.changeOfRingsHom.{t, t + 1, max u (t + 1)} α
    ((constantModules.{t, u} k R).obj M) ((constantModules.{t, u} k R).map f)

variable (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)

/-- The specified extension applied termwise; additivity follows from the assumed adjunction.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
def extensionComplex : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ ⥤
    CochainComplex (Modules.{t, u} k B) ℤ :=
  letI := adj.left_adjoint_additive
  L.mapHomologicalComplex (.up ℤ)

/-- The local tensor generator in the strictly specified extension functor.
The equality hobj identifies the actual tensor construction, not an arbitrary isomorphic object.
Source: Stacks 03EK (blueprint: def-pod-point-derived-hom-models). -/
def generator (M : ModuleCat.{max u (t + 1)} R)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ) (b : B.obj.obj U) (x : M) :
    (L.obj M).val.obj U :=
  (eqToHom (hobj M).symm).val.app U (extensionElement.{t, u} k B α M U b x)

/-- The stated explicit adjunction, in both directions and on every local tensor generator.
Source: Stacks 03CY and 03EK (blueprint: def-pod-point-derived-hom-models). -/
def ExplicitAdjunction : Prop :=
  (∀ (M : ModuleCat.{max u (t + 1)} R) (V : Modules.{t, u} k B) (h : L.obj M ⟶ V) (x : M),
    (adj.homEquiv M V h).hom x =
      h.val.app (op (finalObject k)) (generator.{t, u} k B α L hobj M (op (finalObject k)) 1 x)) ∧
  (∀ (M : ModuleCat.{max u (t + 1)} R) (V : Modules.{t, u} k B)
    (f : M ⟶ (sections.{t, u} k B α).obj V) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (b : B.obj.obj U) (x : M),
    ((adj.homEquiv M V).symm f).val.app U (generator.{t, u} k B α L hobj M U b x) =
      b • PresheafOfModulesOfCommRing.map (R := B.obj) V.val (toFinal k U.unop).op (f.hom x))

variable (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
  (I : CochainComplex (Modules.{t, u} k B) ℤ)

/-- The normalization that uniquely specifies q on every homogeneous component.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
def IsComparison
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
      CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) : Prop :=
  ∀ (j p : ℤ)
    (h : ((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j) (x : c.X p),
    (((q.hom.f j).hom h).v p (p + j) rfl).hom x =
      homValue.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I j p (op (finalObject k)) h
        (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x)

/-- Naturality of the normalized comparison under arbitrary maps of both complexes.
Source: Stacks 0A8X (blueprint: def-pod-point-derived-hom-models). -/
def ComparisonNatural
    (q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
      CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I)) : Prop :=
  ∀ (c' : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
    (I' : CochainComplex (Modules.{t, u} k B) ℤ) (f : c' ⟶ c) (g : I ⟶ I')
    (q' : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c') I') ≅
        CochainComplex.moduleHomComplex c' ((sectionComplex.{t, u} k B α).obj I')),
    IsComparison.{t, u} k B α L hobj adj c' I' q' → ∀ (j p : ℤ)
      (h : ((sectionComplex.{t, u} k B α).obj
        (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j) (x : c'.X p),
      (((q'.hom.f j).hom
        ((((sectionComplex.{t, u} k B α).map
          (((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
            (R := B)).map ((extensionComplex.{t, u} k B α L adj).map f).op).app I ≫
            ((homComplexFunctor.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := B)).obj
              (op ((extensionComplex.{t, u} k B α L adj).obj c'))).map g)).f j).hom h)).v
                p (p + j) rfl).hom x =
        ((((sectionComplex.{t, u} k B α).map g).f (p + j)).hom
          ((((q.hom.f j).hom h).v p (p + j) rfl).hom ((f.f p).hom x)))

variable [PreservesFiniteLimits (sections.{t, u} k B α)]
  [PreservesFiniteColimits (sections.{t, u} k B α)]

section Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- false denotes finite coefficients at exponent n, true denotes integral coefficients.
The ULift changes only size, and imposes no relation between field and coefficient universes.
Source: blueprint point comparison (blueprint: def-pod-point-derived-hom-models). -/
def coefficientRing (n : ℕ) : Bool → CommRingCat.{max u (t + 1)}
  | false => .of (ULift.{t + 1} (Padic.coefficientExtensionRing l E n))
  | true => .of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))

/-- The two actual coefficient sheaves of the node: discrete constant or completed integral.
Source: blueprint point comparison (blueprint: def-pod-point-derived-hom-models). -/
def coefficientSheaf (n : ℕ) : Bool →
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)}
  | false => constantRing.{t, u} k (coefficientRing.{t, u} l E n false)
  | true => completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))

/-- The constant-to-coefficient map: identity at finite level and the canonical limit lift
at integral level. Source: blueprint point comparison, Stacks 03CO
(blueprint: def-pod-point-derived-hom-models). -/
def coefficientMap (n : ℕ) (integral : Bool) :
    constantRing.{t, u} k (coefficientRing.{t, u} l E n integral) ⟶
      coefficientSheaf.{t, u} k l E n integral :=
  match integral with
  | false => 𝟙 _
  | true =>
    { hom :=
        { app := fun U ↦
            letI := completedIntegralCoefficientCommRingUnrestricted l E (Spec (.of k)) U
            CommRingCat.ofHom
            (show (constantRing.{t, u} k (coefficientRing.{t, u} l E n true)).obj.obj U →+*
              (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))).obj.obj U from
              ((integralConstantToCompletionOfUniverses.{t, u}
                l E (Spec (.of k))).hom.app U).hom)
          naturality := fun _U _V f ↦ (forget₂ CommRingCat RingCat).map_injective
            ((integralConstantToCompletionOfUniverses l E (Spec (.of k))).hom.naturality f) } }

end Coefficients

end WeilConjectures.PointDerivedHom
