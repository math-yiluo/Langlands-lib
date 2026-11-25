/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
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
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Maps between strict quotient presentations

Source: Stacks Project, Tags 03CZ and 0941. This is an ordinary chain-map
assembly statement, without a derived category or an open immersion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
universe t u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CanonicalOpenRestriction
namespace GeneralAssembly
universe c v
variable {T : Type c} [Category.{v} T] (J : GrothendieckTopology T)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})

local instance inclusionContinuous (n : ℕ) :
    (Prod.sectR n T).IsContinuous J (coefficientSequenceTopology J) :=
  SemilinearSections.evaluationContinuous.{c, v, max c v} J n

variable (φ : ∀ n : ℕ, S n ≅
  ((Prod.sectR n T).sheafPushforwardContinuous RingCat.{r} J
    (coefficientSequenceTopology J)).obj R)

variable (κ : ∀ {m n : ℕ}, n ≤ m → (S m ⟶ S n))
    (δ : ∀ {m n : ℕ} (h : n ≤ m), (SheafOfModules.pushforward.{r} (φ m).hom) ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom) ⋙ SheafOfModules.restrictScalars (κ h))
    (hδ : ∀ {m n : ℕ} (h : n ≤ m) (M : SheafOfModules.{r} R) (V : Tᵒᵖ),
      HEq (fun x ↦ ((δ h).app M).val.app V x)
        (fun x : M.val.obj (op (m, V.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    {M N : SheafOfModules.{r} R}
    (d : ∀ n : ℕ, (SheafOfModules.pushforward.{r} (φ n).hom).obj M ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom).obj N)
    (ht : ∀ {m n : ℕ} (h : n ≤ m),
      (δ h).app M ≫ (SheafOfModules.restrictScalars (κ h)).map (d n) =
        d m ≫ (δ h).app N)

private def undoRestriction {A B : RingCat.{r}} (φ : A ≅ B)
    {M N : ModuleCat.{r} B}
    (f : (ModuleCat.restrictScalars φ.hom.hom).obj M ⟶
      (ModuleCat.restrictScalars φ.hom.hom).obj N) : M ⟶ N :=
  ModuleCat.ofHom {
    toFun := f
    map_add' := f.hom.map_add
    map_smul' := by
      intro a x
      have h := f.hom.map_smul (φ.inv a) x
      change f (φ.hom (φ.inv a) • x) = φ.hom (φ.inv a) • f x at h
      have hi : φ.hom (φ.inv a) = a :=
        congrArg (fun k : B ⟶ B ↦ k a) φ.inv_hom_id
      simpa only [hi, RingHom.id_apply] using h }

@[irreducible] private def assemble_app (V : (ℕ × T)ᵒᵖ) :
    M.val.obj V ⟶ N.val.obj V :=
  undoRestriction
    (((CategoryTheory.evaluation Tᵒᵖ RingCat.{r}).obj (op V.unop.2)).mapIso
      ((sheafToPresheaf J RingCat.{r}).mapIso (φ V.unop.1)))
    ((d V.unop.1).val.app (op V.unop.2))

private theorem assemble_app_apply (V : (ℕ × T)ᵒᵖ) (x : M.val.obj V) :
    assemble_app J R S φ d V x = (d V.unop.1).val.app (op V.unop.2) x := by
  unfold assemble_app undoRestriction
  rfl

private theorem restriction_square_apply
    {A B : Sheaf J RingCat.{r}} (ψ : A ⟶ B)
    {V W : SheafOfModules.{r} A} {V' W' : SheafOfModules.{r} B}
    (a : V ⟶ (SheafOfModules.restrictScalars ψ).obj V')
    (b : W ⟶ (SheafOfModules.restrictScalars ψ).obj W')
    (f : V ⟶ W) (g : V' ⟶ W')
    (h : a ≫ (SheafOfModules.restrictScalars ψ).map g = f ≫ b)
    (U : Tᵒᵖ) (x : V.val.obj U) :
    g.val.app U (a.val.app U x) = b.val.app U (f.val.app U x) :=
  congrArg (fun k ↦ k.val.app U x) h

private theorem square_of_functions {A B P Q : Type r}
    (f : A → B) (g : P → Q) (a a' : A → P) (b b' : B → Q)
    (ha : a = a') (hb : b = b') (hs : ∀ x, g (a x) = b (f x)) (x : A) :
    b' (f x) = g (a' x) := by
  rw [← ha, ← hb]
  exact (hs x).symm

include ht hδ in
private theorem horizontal_natural {m n : ℕ} (h : n ≤ m) (V : Tᵒᵖ)
    (x : M.val.obj (op (m, V.unop))) :
    N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
        (assemble_app J R S φ d (op (m, V.unop)) x) =
      assemble_app J R S φ d (op (n, V.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  rw [assemble_app_apply, assemble_app_apply]
  exact square_of_functions
    (fun y ↦ (d m).val.app V y) (fun y ↦ (d n).val.app V y)
    (fun y ↦ ((δ h).app M).val.app V y)
    (fun y ↦ M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op y)
    (fun y ↦ ((δ h).app N).val.app V y)
    (fun y ↦ N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op y)
    (eq_of_heq (hδ h M V)) (eq_of_heq (hδ h N V))
    (fun y ↦ restriction_square_apply J (κ h)
      ((δ h).app M) ((δ h).app N) (d m) (d n) (ht h) V y) x

include ht hδ in
@[irreducible] private def assemble : M ⟶ N where
  val := {
    app := assemble_app J R S φ d
    naturality := by
      intro V Z f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change assemble_app J R S φ d Z (M.val.map f x) =
        N.val.map f (assemble_app J R S φ d V x)
      let a : V ⟶ op (V.unop.1, Z.unop.2) :=
        (Prod.mkHom (𝟙 V.unop.1) f.unop.2).op
      let b : op (V.unop.1, Z.unop.2) ⟶ Z :=
        (Prod.mkHom f.unop.1 (𝟙 Z.unop.2)).op
      have hab : f = a ≫ b := by
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext <;> simp [a, b]
      have hv : assemble_app J R S φ d (op (V.unop.1, Z.unop.2)) (M.val.map a x) =
          N.val.map a (assemble_app J R S φ d V x) := by
        simp only [assemble_app_apply]
        exact PresheafOfModules.naturality_apply (d V.unop.1).val f.unop.2.op x
      rw [hab, M.val.map_comp_apply, N.val.map_comp_apply, ← hv]
      exact (horizontal_natural J R S φ κ δ hδ d ht (leOfHom f.unop.1)
        (op Z.unop.2) (M.val.map a x)).symm }

private theorem assemble_evaluation (n : ℕ) :
    ((SheafOfModules.pushforward.{r} (φ n).hom)).map (assemble J R S φ κ δ hδ d ht) = d n := by
  unfold assemble
  ext V x
  exact assemble_app_apply J R S φ d (op (n, V.unop)) x

end GeneralAssembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem eval_hom_ext {M N : coefficientSequenceModules l E W} {f g : M ⟶ N}
    (h : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).map f =
      (coefficientSequenceEvaluation l E W n).map g) : f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

private theorem transported_ab_map_apply
    {A A' B B' : AddCommGrpCat.{r}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (x' : A') (hx : HEq x x') : HEq (f x) (g x') := by
  cases hA
  cases hB
  cases hx
  apply heq_of_eq
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    congrArg (fun k ↦ k x) h

private theorem transition_section {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (V : W.ProEtᵒᵖ)
    (x : M.val.obj (op (m, V.unop))) :
    ((coefficientSequenceTransition l E W h).app M).val.app V x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x := by
  have hh := (coefficientSequenceTransition_exists l E W h).exists.choose_spec M V
  have he := transported_ab_map_apply.{max u (t + 1)}
    (coefficientSequenceEvaluationAb_eq l E W M m V)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W M h V)
    _ _ hh x x (HEq.rfl)
  exact eq_of_heq he

private theorem transition_functions {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ ((coefficientSequenceTransition l E W h).app M).val.app V x)
      (fun x : M.val.obj (op (m, V.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) := by
  exact heq_of_eq (funext (transition_section l E W h M V))

private abbrev coefficientRing :=
  ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W))

section Assembly
variable {M N : coefficientSequenceModules l E W}
  (d : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj M ⟶
    (coefficientSequenceEvaluation l E W n).obj N)
  (ht : ∀ {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app M ≫
      (normalizedDVRModuleRes l E W h).map (d n) =
    d m ≫ (coefficientSequenceTransition l E W h).app N)

include d ht in
@[irreducible] private def assemble : M ⟶ N :=
  GeneralAssembly.assemble (Scheme.ProEt.topology W) (coefficientRing l E W)
    (integralCoefficientSheaf l E W)
    (fun n ↦ eqToIso (coefficientSequenceEvaluationRing_eq l E W n).symm)
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun {_ _} h M V ↦ transition_functions l E W h M V) d ht

private theorem assemble_evaluation (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).map (assemble l E W d ht) = d n := by
  unfold assemble
  exact GeneralAssembly.assemble_evaluation
    (Scheme.ProEt.topology W) (coefficientRing l E W)
    (integralCoefficientSheaf l E W)
    (fun k ↦ eqToIso (coefficientSequenceEvaluationRing_eq l E W k).symm)
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun {_ _} h M V ↦ transition_functions l E W h M V) d ht n

end Assembly

/-- An integral chain map gives a strict chain-system map between any two
quotient presentations with their actual horizontal transition equations.
Source: Stacks Project, Tags 03CZ and 0941; ordinary assembly in step 3 of
`lem-sf-open-restriction-counit-on-good-complexes`.
(blueprint: lem-sf-strict-reduction-presentation-map).

Proof: at each degree and coefficient level take kappaC, followed by scalar
extension of h, followed by kappaD inverse. Naturality of the quotient
transformation and the two assumed horizontal equations show that these maps
commute with horizontal restrictions. Their vertical naturality is that of the
finite module-sheaf maps. Since every arrow of the product site is a horizontal
arrow followed by a vertical arrow, they assemble to a module-sheaf map on the
sequence site. The chain-map equations follow from those of h and the kappa
isomorphisms, checked on ordinary coefficient evaluations, which are jointly
faithful. Thus these degreewise maps form the required strict chain map. -/
theorem strictReductionPresentationMap
    (Q R : CochainComplex (scalarReductionSource l E W) ℤ)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj R)
    (hC : ∀ (m n : ℕ) (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κC n).hom =
      (κC m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
          (.up ℤ)).app Q)
    (hD : ∀ (m n : ℕ) (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (.up ℤ)).app D ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κD n).hom =
      (κD m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h)
          (.up ℤ)).app R)
    (h : Q ⟶ R) :
    ∃ f : C ⟶ D, ∀ (n : ℕ) (i : ℤ),
      (coefficientSequenceEvaluation l E W n).map (f.f i) ≫ (κD n).hom.f i =
        (κC n).hom.f i ≫ (scalarReductionExtension l E W n).map (h.f i) := by
  let d (n : ℕ) :
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ⟶
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D :=
    (κC n).hom ≫ ((scalarReductionExtension l E W n).mapHomologicalComplex
      (.up ℤ)).map h ≫ (κD n).inv
  have hd (i : ℤ) {m n : ℕ} (hmn : n ≤ m) :
      (coefficientSequenceTransition l E W hmn).app (C.X i) ≫
          (normalizedDVRModuleRes l E W hmn).map ((d n).f i) =
        (d m).f i ≫ (coefficientSequenceTransition l E W hmn).app (D.X i) := by
    have hCi := congrArg (fun f ↦ f.f i) (hC m n hmn)
    have hDi := congrArg (fun f ↦ f.f i) (hD m n hmn)
    have hn := (coefficientOrdinaryQuotient l E W hmn).naturality (h.f i)
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f] at hCi hDi
    dsimp only [Functor.comp_map] at hn
    apply (cancel_mono ((normalizedDVRModuleRes l E W hmn).map ((κD n).hom.f i))).1
    simp only [d, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hDi]
    erw [reassoc_of% hCi, ← hn]
    have hDm : (κD m).inv.f i ≫ (κD m).hom.f i = 𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        congrArg (fun g ↦ g.f i) (κD m).inv_hom_id
    erw [reassoc_of% hDm]
  let f : C ⟶ D := {
    f := fun i ↦ assemble l E W (fun n ↦ (d n).f i) (hd i)
    comm' := by
      intro i j hij
      apply eval_hom_ext l E W
      intro n
      simp only [Functor.map_comp, assemble_evaluation]
      exact (d n).comm i j }
  refine ⟨f, ?_⟩
  intro n i
  change (coefficientSequenceEvaluation l E W n).map
    (assemble l E W (fun k ↦ (d k).f i) (hd i)) ≫ _ = _
  rw [assemble_evaluation]
  simp only [d, Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    Category.comp_id]
  rfl

end WeilConjectures.CanonicalOpenRestriction
