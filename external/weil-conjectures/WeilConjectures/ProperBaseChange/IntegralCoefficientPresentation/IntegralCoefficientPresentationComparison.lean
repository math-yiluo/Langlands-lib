/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Projection-normalized integral coefficient presentation comparison

Source: Bhatt--Scholze, Section 6.5, convention before Definition 6.5.1,
Lemma 4.2.12 and Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison).

The existing constants-to-functions comparison is reused. The quotient isomorphisms e_n
and the completed comparison e_T are the unique ones with the node's normalizations:
the statement asserts their existence and uniqueness and then quantifies over any family
so normalized. It does not import the parent stratified-perfect module (which cites this
node in its proof), so that module can import this one.
The extra compatibility predicate records finite derived reductions, their genuine
adjunction units, all quotient transitions, and the two arrows of the product Roos diagram.
No constructibility or completeness membership is asserted. Index n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralCoefficientPresentation

-- The published free-universe sheaf instance would leave a universe unassigned here;
-- the fixed coefficient-universe instance of the imported modules is used instead.
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

/-- The restricted derived finite reduction for a specified quotient projection.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
abbrev reduction {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (π : R ⟶ S) := pbcDerivedExtend π ⋙ pbcDerivedRestrict π

/-- The canonical restricted map from a larger quotient to a smaller quotient.
It is the adjoint of the smaller quotient unit, using the normalized scalar-restriction
composition. On K-flat models it sends b tensor x to q(b) tensor x.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def transition {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (π : R ⟶ S) (q : S ⟶ B) (π' : R ⟶ B) (h : π ≫ q = π')
    (K : DerivedCategory (pbcModules T R)) :
    (reduction π).obj K ⟶ (reduction π').obj K :=
  (pbcDerivedRestrict π).map (pbcReductionTransition π q π' h K) ≫
    (pbcDerivedRestrictComp π q π' h).hom.app ((pbcDerivedExtend π').obj K)

/-- Derive an identity-on-sections comparison of the two composite restrictions.
Source: Stacks 03DA and 015F
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def derivedSquare {T : Scheme.{u}}
    {R S Rn Sn : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ≅ S) (b : Rn ≅ Sn) (π : R ⟶ Rn) (ρ : S ⟶ Sn)
    (r : pbcRestrict b.hom ⋙ pbcRestrict π ≅ pbcRestrict ρ ⋙ pbcRestrict e.hom) :
    pbcDerivedRestrict b.hom ⋙ pbcDerivedRestrict π ≅
      pbcDerivedRestrict ρ ⋙ pbcDerivedRestrict e.hom :=
  Functor.mapDerivedCategoryCompIso (pbcRestrict b.hom) (pbcRestrict π) ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
      (Functor.mapDerivedCategoryCompIso (pbcRestrict ρ) (pbcRestrict e.hom)).symm

/-- The finite comparison after restriction to the completed coefficient ring.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def restrictedComparison {T : Scheme.{u}}
    {R S Rn Sn : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ≅ S) (b : Rn ≅ Sn) (π : R ⟶ Rn) (ρ : S ⟶ Sn)
    (r : pbcRestrict b.hom ⋙ pbcRestrict π ≅ pbcRestrict ρ ⋙ pbcRestrict e.hom)
    (α : pbcDerivedRestrict e.hom ⋙ pbcDerivedExtend π ≅
      pbcDerivedExtend ρ ⋙ pbcDerivedRestrict b.hom)
    (K : DerivedCategory (pbcModules T S)) :
    (reduction π).obj ((pbcDerivedRestrict e.hom).obj K) ≅
      (pbcDerivedRestrict e.hom).obj ((reduction ρ).obj K) :=
  (pbcDerivedRestrict π).mapIso (α.app K) ≪≫
    (derivedSquare e b π ρ r).app ((pbcDerivedExtend ρ).obj K)

/-- Compatibility of the two product Roos arrows, with the product comparison fixed
by every projection. Product existence is supplied separately, not assumed of a complex.
Source: Bhatt--Scholze, Propositions 3.1.10--3.1.11; Stacks 08TC
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def RoosCompatible {C : Type v} [Category.{w} C] [Preadditive C]
    {D : Type v} [Category.{w} D] [Preadditive D] (F : C ⥤ D)
    (K : C) (P : ℕ → D) (Q : ℕ → C)
    (cP : ∀ n, F.obj K ⟶ P n) (cQ : ∀ n, K ⟶ Q n)
    (tP : ∀ n, P (n + 1) ⟶ P n) (tQ : ∀ n, Q (n + 1) ⟶ Q n)
    (β : ∀ n, P n ≅ F.obj (Q n)) [HasProduct P] [HasProduct Q] : Prop :=
  ∃ z : F.obj (∏ᶜ Q) ≅ ∏ᶜ P,
    (∀ n, z.hom ≫ Pi.π P n = F.map (Pi.π Q n) ≫ (β n).inv) ∧
    F.map (Pi.lift cQ) ≫ z.hom = Pi.lift cP ∧
    F.map (towerTransitionEndomorphism tQ) ≫ z.hom =
      z.hom ≫ towerTransitionEndomorphism tP

/-- The published restriction compositor fixes every underlying section. -/
private theorem restrict_comp_hom {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

/-- The inverse compositor fixes sections by its inverse identity. -/
private theorem restrict_comp_inv {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).inv.app M).val.app U x = x := by
  have hx := congrArg (fun f ↦ f.val.app U x)
    ((pbcRestrictComp φ ψ χ h).inv_hom_id_app M)
  change ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U
    (((pbcRestrictComp φ ψ χ h).inv.app M).val.app U x) = x at hx
  rw [restrict_comp_hom] at hx
  exact hx

/-- The restriction square obtained from equality of the two coefficient composites. -/
private def restrictionSquare {T : Scheme.{u}}
    {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ R') (ψ : R' ⟶ S') (χ : R ⟶ S) (τ : S ⟶ S')
    (h : φ ≫ ψ = χ ≫ τ) :
    pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict τ ⋙ pbcRestrict χ :=
  pbcRestrictComp φ ψ (χ ≫ τ) h ≪≫ (pbcRestrictComp χ τ (χ ≫ τ) rfl).symm

/-- The coefficient square fixes every section. -/
private theorem restrictionSquare_hom {T : Scheme.{u}}
    {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ R') (ψ : R' ⟶ S') (χ : R ⟶ S) (τ : S ⟶ S')
    (h : φ ≫ ψ = χ ≫ τ) (M : pbcModules T S') (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) : ((restrictionSquare φ ψ χ τ h).hom.app M).val.app U x = x := by
  change ((pbcRestrictComp χ τ (χ ≫ τ) rfl).inv.app M).val.app U
    (((pbcRestrictComp φ ψ (χ ≫ τ) h).hom.app M).val.app U x) = x
  rw [restrict_comp_hom, restrict_comp_inv]

/-- Sectionwise identities prove the coherence of normalized restriction squares. -/
private theorem ordinary_coherence {T : Scheme.{u}}
    {R S Ra Rb Sa Sb : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (e : R ⟶ S) (πa : R ⟶ Ra) (πb : R ⟶ Rb)
    (ρa : S ⟶ Sa) (ρb : S ⟶ Sb) (ba : Ra ⟶ Sa) (bb : Rb ⟶ Sb)
    (qp : Rb ⟶ Ra) (qs : Sb ⟶ Sa)
    (ha : πa ≫ ba = e ≫ ρa) (hb : πb ≫ bb = e ≫ ρb)
    (hp : πb ≫ qp = πa) (hs : ρb ≫ qs = ρa) (ht : qp ≫ ba = bb ≫ qs)
    (M : pbcModules T Sa) :
    (pbcRestrict πb).map ((restrictionSquare qp ba bb qs ht).hom.app M) ≫
        (restrictionSquare πb bb e ρb hb).hom.app ((pbcRestrict qs).obj M) ≫
        (pbcRestrict e).map ((pbcRestrictComp ρb qs ρa hs).hom.app M) =
      (pbcRestrictComp πb qp πa hp).hom.app ((pbcRestrict ba).obj M) ≫
        (restrictionSquare πa ba e ρa ha).hom.app M := by
  ext U x
  change ((pbcRestrictComp ρb qs ρa hs).hom.app M).val.app U
      (((restrictionSquare πb bb e ρb hb).hom.app ((pbcRestrict qs).obj M)).val.app U
        (((restrictionSquare qp ba bb qs ht).hom.app M).val.app U x)) =
    ((restrictionSquare πa ba e ρa ha).hom.app M).val.app U
      (((pbcRestrictComp πb qp πa hp).hom.app ((pbcRestrict ba).obj M)).val.app U x)
  simp only [restrictionSquare_hom, restrict_comp_hom]

/-- Restriction along the identity, normalized on underlying sections. -/
private def restrictId {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl)))
      (fun f ↦ by ext U x; rfl)
/-- Construct inverse scalar equivalences from their normalized composition maps. -/
private theorem restrict_equivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (e : R ≅ S) :
    (pbcRestrict e.hom).IsEquivalence ∧ (pbcRestrict e.inv).IsEquivalence ∧
      Nonempty (pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _) ∧
      Nonempty (pbcRestrict e.inv ⋙ pbcRestrict e.hom ≅ 𝟭 _) := by
  let i := pbcRestrictComp e.inv e.hom (𝟙 S) e.inv_hom_id ≪≫ restrictId S
  let j := pbcRestrictComp e.hom e.inv (𝟙 R) e.hom_inv_id ≪≫ restrictId R
  let t : pbcModules T S ≌ pbcModules T R :=
    CategoryTheory.Equivalence.mk (pbcRestrict e.hom) (pbcRestrict e.inv) i.symm j
  exact ⟨t.isEquivalence_functor, t.isEquivalence_inverse, ⟨i⟩, ⟨j⟩⟩

/-- Exact countable products of module sheaves give countable derived products. -/
private theorem derived_products (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HasCountableProducts (DerivedCategory (pbcModules T R)) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : HasCountableProducts (pbcModules T R) :=
    (ProEt.countableProducts_exact.{u, u, 0} T R).1
  have : (lim (J := Discrete ℕ) (C := pbcModules T R)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} T R).2.2 ℕ
          (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have : HasFiniteBiproducts (pbcModules T R) := HasFiniteBiproducts.of_hasFiniteProducts
  have := hasExactLimitsOfShape_of_preservesEpi (pbcModules T R) (Discrete ℕ)
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat (pbcModules T R)
  exact (derivedCategory_countableProducts_core.{0} (pbcModules T R)).choose

open CategoryTheory.Functor

/-- Descend a coherent square of exact restrictions through unbounded localization. -/
private theorem restriction_coherence
    {A C B₀ B₁ D₀ D₁ : Type*}
    [Category A] [Category C] [Category B₀] [Category B₁] [Category D₀] [Category D₁]
    [Abelian A] [Abelian C] [Abelian B₀] [Abelian B₁] [Abelian D₀] [Abelian D₁]
    [HasDerivedCategory A] [HasDerivedCategory C]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁]
    (U₀ : B₀ ⥤ A) (U₁ : B₁ ⥤ A) (U₀' : D₀ ⥤ C) (U₁' : D₁ ⥤ C)
    (F : C ⥤ A) (G₀ : D₀ ⥤ B₀) (G₁ : D₁ ⥤ B₁)
    (V : B₀ ⥤ B₁) (V' : D₀ ⥤ D₁)
    [U₀.Additive] [U₁.Additive] [U₀'.Additive] [U₁'.Additive]
    [F.Additive] [G₀.Additive] [G₁.Additive] [V.Additive] [V'.Additive]
    [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₀'] [PreservesFiniteColimits U₀']
    [PreservesFiniteLimits U₁'] [PreservesFiniteColimits U₁']
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    (c : V ⋙ U₁ ≅ U₀) (c' : V' ⋙ U₁' ≅ U₀')
    (r₀ : G₀ ⋙ U₀ ≅ U₀' ⋙ F) (r₁ : G₁ ⋙ U₁ ≅ U₁' ⋙ F)
    (s : G₀ ⋙ V ≅ V' ⋙ G₁)
    (coh : ∀ X, U₁.map (s.hom.app X) ≫ r₁.hom.app (V'.obj X) ≫
      F.map (c'.hom.app X) = c.hom.app (G₀.obj X) ≫ r₀.hom.app X)
    (X : DerivedCategory D₀) :
    U₁.mapDerivedCategory.map ((mapDerivedCategorySquareIso s).hom.app X) ≫
      (mapDerivedCategorySquareIso r₁).hom.app (V'.mapDerivedCategory.obj X) ≫
      F.mapDerivedCategory.map
        ((exactDerivedRestrictionComposition V' U₁' U₀' c').hom.app X) =
    (exactDerivedRestrictionComposition V U₁ U₀ c).hom.app
        (G₀.mapDerivedCategory.obj X) ≫
      (mapDerivedCategorySquareIso r₀).hom.app X := by
  have hi (Y : D₀) : F.map (c'.inv.app Y) ≫ r₁.inv.app (V'.obj Y) ≫
      U₁.map (s.inv.app Y) = r₀.inv.app Y ≫ c.inv.app (G₀.obj Y) := by
    have hh : U₁.mapIso (s.app Y) ≪≫ r₁.app (V'.obj Y) ≪≫ F.mapIso (c'.app Y) =
        c.app (G₀.obj Y) ≪≫ r₀.app Y := by
      apply Iso.ext
      exact coh Y
    have hh' := congrArg Iso.inv hh
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hh'
  have hd := mapDerivedCategorySquareIso_comp V' U₁' U₀' V U₁ U₀ G₀ G₁ F
    s.symm r₁.symm r₀.symm c'.symm c.symm hi
  have h := congrArg (fun z ↦ z.inv.app X) hd
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, associator_hom_app, Category.id_comp, Category.comp_id,
    ← mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, exactDerivedRestrictionComposition,
    mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Category.assoc] using h

/-- Adjunction bijections transport the normalized quotient transition across a coherent square. -/
private theorem transition_transport
    {A C B₀ B₁ D₀ D₁ : Type*}
    [Category A] [Category C] [Category B₀] [Category B₁] [Category D₀] [Category D₁]
    {L₀ : A ⥤ B₀} {U₀ : B₀ ⥤ A} {L₁ : A ⥤ B₁} {U₁ : B₁ ⥤ A}
    {L₀' : C ⥤ D₀} {U₀' : D₀ ⥤ C} {L₁' : C ⥤ D₁} {U₁' : D₁ ⥤ C}
    (a₀ : L₀ ⊣ U₀) (a₁ : L₁ ⊣ U₁) (a₀' : L₀' ⊣ U₀') (a₁' : L₁' ⊣ U₁')
    (F : C ⥤ A) (G₀ : D₀ ⥤ B₀) (G₁ : D₁ ⥤ B₁)
    (V : B₀ ⥤ B₁) (V' : D₀ ⥤ D₁)
    (c : V ⋙ U₁ ≅ U₀) (c' : V' ⋙ U₁' ≅ U₀')
    (r₀ : G₀ ⋙ U₀ ≅ U₀' ⋙ F) (r₁ : G₁ ⋙ U₁ ≅ U₁' ⋙ F)
    (s : G₀ ⋙ V ≅ V' ⋙ G₁)
    (coh : ∀ X, U₁.map (s.hom.app X) ≫ r₁.hom.app (V'.obj X) ≫
      F.map (c'.hom.app X) = c.hom.app (G₀.obj X) ≫ r₀.hom.app X)
    (α₀ : F ⋙ L₀ ≅ L₀' ⋙ G₀) (α₁ : F ⋙ L₁ ≅ L₁' ⋙ G₁)
    (h₀ : ∀ X, a₀.unit.app (F.obj X) ≫ U₀.map (α₀.hom.app X) ≫
      r₀.hom.app (L₀'.obj X) = F.map (a₀'.unit.app X))
    (h₁ : ∀ X, a₁.unit.app (F.obj X) ≫ U₁.map (α₁.hom.app X) ≫
      r₁.hom.app (L₁'.obj X) = F.map (a₁'.unit.app X)) (X : C) :
    let m := (a₁.homEquiv _ _).symm
      (a₀.unit.app (F.obj X) ≫ c.inv.app (L₀.obj (F.obj X)))
    let m' := (a₁'.homEquiv _ _).symm
      (a₀'.unit.app X ≫ c'.inv.app (L₀'.obj X))
    (U₁.map m ≫ c.hom.app (L₀.obj (F.obj X))) ≫
        (U₀.map (α₀.hom.app X) ≫ r₀.hom.app (L₀'.obj X)) =
      (U₁.map (α₁.hom.app X) ≫ r₁.hom.app (L₁'.obj X)) ≫
        F.map (U₁'.map m' ≫ c'.hom.app (L₀'.obj X)) := by
  intro m m'
  have hm : a₁.unit.app (F.obj X) ≫ U₁.map m =
      a₀.unit.app (F.obj X) ≫ c.inv.app (L₀.obj (F.obj X)) :=
    (a₁.homEquiv _ _).apply_symm_apply _
  have hm' : a₁'.unit.app X ≫ U₁'.map m' =
      a₀'.unit.app X ≫ c'.inv.app (L₀'.obj X) :=
    (a₁'.homEquiv _ _).apply_symm_apply _
  have hi (Y : D₀) : F.map (c'.inv.app Y) ≫ r₁.inv.app (V'.obj Y) ≫
      U₁.map (s.inv.app Y) = r₀.inv.app Y ≫ c.inv.app (G₀.obj Y) := by
    have hh : U₁.mapIso (s.app Y) ≪≫ r₁.app (V'.obj Y) ≪≫ F.mapIso (c'.app Y) =
        c.app (G₀.obj Y) ≪≫ r₀.app Y := by
      apply Iso.ext
      exact coh Y
    have hh' := congrArg Iso.inv hh
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hh'
  dsimp only [Functor.id_obj] at hm hm'
  have hu : m ≫ V.map (α₀.hom.app X) =
      α₁.hom.app X ≫ G₁.map m' ≫ s.inv.app (L₀'.obj X) := by
    apply (a₁.homEquiv _ _).injective
    change a₁.unit.app (F.obj X) ≫ U₁.map (m ≫ _) =
      a₁.unit.app (F.obj X) ≫ U₁.map (_ ≫ _ ≫ _)
    simp only [Functor.map_comp, ← Category.assoc]
    erw [hm]
    have hcn := c.inv.naturality (α₀.hom.app X)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hcn
    rw [Category.assoc, ← hcn, ← Category.assoc]
    have h₀i : a₀.unit.app (F.obj X) ≫ U₀.map (α₀.hom.app X) =
        F.map (a₀'.unit.app X) ≫ r₀.inv.app (L₀'.obj X) := by
      rw [← h₀]
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
    have h₁i : a₁.unit.app (F.obj X) ≫ U₁.map (α₁.hom.app X) =
        F.map (a₁'.unit.app X) ≫ r₁.inv.app (L₁'.obj X) := by
      rw [← h₁]
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
    rw [h₀i, h₁i]
    have hrn := r₁.inv.naturality m'
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hrn
    simp only [Category.assoc]
    rw [← reassoc_of% hrn, ← F.map_comp_assoc, hm', F.map_comp, Category.assoc, hi]
  have hc := c.hom.naturality (α₀.hom.app X)
  have hr := r₁.hom.naturality m'
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hc hr
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hc, ← U₁.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← coh (L₀'.obj X)]
  have hs : U₁.map (s.inv.app (L₀'.obj X)) ≫ U₁.map (s.hom.app (L₀'.obj X)) =
      𝟙 _ := by rw [← U₁.map_comp, Iso.inv_hom_id_app, U₁.map_id]
  rw [reassoc_of% hs]
  rw [reassoc_of% hr]

/-- Product projections transport both Roos arrows across an additive equivalence. -/
private theorem roos_transport
    {C : Type v} [Category.{w} C] [Preadditive C]
    {D : Type v} [Category.{w} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (K : C) (P : ℕ → D) (Q : ℕ → C)
    (cP : ∀ n, F.obj K ⟶ P n) (cQ : ∀ n, K ⟶ Q n)
    (tP : ∀ n, P (n + 1) ⟶ P n) (tQ : ∀ n, Q (n + 1) ⟶ Q n)
    (β : ∀ n, P n ≅ F.obj (Q n)) [HasProduct P] [HasProduct Q]
    (hc : ∀ n, cP n ≫ (β n).hom = F.map (cQ n))
    (ht : ∀ n, tP n ≫ (β n).hom = (β (n + 1)).hom ≫ F.map (tQ n)) :
    RoosCompatible F K P Q cP cQ tP tQ β := by
  have : HasProduct (fun n ↦ F.obj (Q n)) :=
    hasLimit_of_iso (F := Discrete.functor P) (Discrete.natIso (fun n ↦ β n.as))
  let z : F.obj (∏ᶜ Q) ≅ ∏ᶜ P :=
    PreservesProduct.iso F Q ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso (fun n ↦ (β n.as).symm))
  have hz (n : ℕ) : z.hom ≫ Pi.π P n = F.map (Pi.π Q n) ≫ (β n).inv := by
    simp [z, HasLimit.isoOfNatIso_hom_π, PreservesProduct.iso_hom]
  have hci (n : ℕ) : F.map (cQ n) ≫ (β n).inv = cP n := by
    rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hti (n : ℕ) : F.map (tQ n) ≫ (β n).inv = (β (n + 1)).inv ≫ tP n := by
    apply (cancel_epi (β (n + 1)).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨z, hz, ?_, ?_⟩
  · apply Pi.hom_ext
    intro n
    rw [Category.assoc, hz, ← Category.assoc, ← F.map_comp, Pi.lift_comp_π, hci,
      Pi.lift_comp_π]
  · have hs : F.map (towerProductShift tQ) ≫ z.hom = z.hom ≫ towerProductShift tP := by
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, hz, towerProductShift, Pi.lift_comp_π]
      rw [← Category.assoc, ← F.map_comp, Pi.lift_comp_π, F.map_comp, Category.assoc,
        hti, ← Category.assoc, ← hz]
      exact Category.assoc _ _ _
    simp only [towerTransitionEndomorphism, F.map_sub, F.map_id,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, hs]

/-- An invertible square of right adjoints has an invertible left mate across equivalences. -/
private theorem square_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (a : L ⊣ U) (a' : L' ⊣ U') (F : C ⥤ A) (G : D ⥤ B)
    [F.IsEquivalence] [G.IsEquivalence] (r : G ⋙ U ≅ U' ⋙ F) :
    ∃ α : F ⋙ L ≅ L' ⋙ G, ∀ X : C,
      a.unit.app (F.obj X) ≫ U.map (α.hom.app X) ≫ r.hom.app (L'.obj X) =
        F.map (a'.unit.app X) := by
  let t : F ⋙ L ⟶ L' ⋙ G :=
    { app X := (a.homEquiv _ _).symm
        (F.map (a'.unit.app X) ≫ r.inv.app (L'.obj X))
      naturality X Y f := by
        apply (a.homEquiv _ _).injective
        simp only [Functor.comp_map, a.homEquiv_naturality_left,
          a.homEquiv_naturality_right, Equiv.apply_symm_apply]
        rw [← Category.assoc, ← F.map_comp, ← a'.unit_naturality]
        simp only [F.map_comp, Category.assoc]
        exact congrArg (fun k ↦ F.map (a'.unit.app X) ≫ k)
          (r.inv.naturality (L'.map f)) }
  have ht (X : C) : a.unit.app (F.obj X) ≫ U.map (t.app X) =
      F.map (a'.unit.app X) ≫ r.inv.app (L'.obj X) := by
    exact (a.homEquiv _ _).apply_symm_apply _
  have hi (X : C) : IsIso (t.app X) := by
    apply isIso_of_coyoneda_map_bijective
    intro Y
    let Z := G.objPreimage Y
    let i : G.obj Z ≅ Y := G.objObjPreimageIso Y
    let e :=
      (Iso.homCongr (Iso.refl (G.obj (L'.obj X))) i.symm).trans
        ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
          ((a'.homEquiv X Z).trans
            ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
              ((Iso.homCongr (Iso.refl (F.obj X)) (r.app Z).symm).trans
                ((a.homEquiv (F.obj X) (G.obj Z)).symm.trans
                  (Iso.homCongr (Iso.refl (L.obj (F.obj X))) i))))))
    change Function.Bijective (fun f : G.obj (L'.obj X) ⟶ Y ↦ t.app X ≫ f)
    have he : (fun f : G.obj (L'.obj X) ⟶ Y ↦ t.app X ≫ f) = e := by
      funext f
      apply (a.homEquiv _ _).injective
      change a.unit.app _ ≫ U.map (t.app X ≫ f) = _
      simp only [Functor.map_comp, ← Category.assoc, ht]
      dsimp [e, Iso.homCongr]
      simp only [Category.id_comp, a.homEquiv_naturality_right,
        Equiv.apply_symm_apply]
      let g := (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm (f ≫ i.inv)
      have hg : G.map g = f ≫ i.inv :=
        (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.apply_symm_apply _
      have hgf : f = G.map g ≫ i.hom := by rw [hg]; simp
      change (F.map (a'.unit.app X) ≫ r.inv.app (L'.obj X)) ≫ U.map f =
        (F.map (a'.unit.app X ≫ U'.map g) ≫ r.inv.app Z) ≫ U.map i.hom
      rw [hgf, F.map_comp, U.map_comp]
      simp only [Category.assoc]
      have hr := r.inv.naturality g
      dsimp only [Functor.comp_map] at hr
      rw [reassoc_of% hr]
    rw [he]
    exact e.bijective
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨asIso t, fun X ↦ ?_⟩
  change a.unit.app _ ≫ U.map (t.app X) ≫ _ = _
  rw [← Category.assoc, ht]
  simp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The commutative finite coefficient comparison ē_n = e_n ∘ κ_n⁻¹ for a family q of
quotient isomorphisms; the theorem applies it to the uniquely normalized family.
Source: Bhatt--Scholze, Section 6.5, Lemma 4.2.12
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def level (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (n : ℕ) : (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      integralCoefficientCommRingSheaf l E T n :=
  (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso (q n).toCommRingCatIso

/-- The actual detailed finite coefficient diagram, retaining commutativity.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def detailedSystem : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ integralCoefficientCommRingSheaf l E T n) (fun n ↦
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))

/-- The derived compatibility clauses, expressed using the published scalar adjunctions.
The section formula on r prevents substitution of an arbitrary restriction comparison.
The unit equation then fixes the derived tensor comparison. The transition equation is
for every quotient arrow, including the identity. RoosCompatible uses the actual 1-s.
Source: Bhatt--Scholze, Section 6.5; Stacks 06YY and 08TC
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison). -/
def DerivedCompatible
    (q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E T)
    (hρ : ∀ (b a : ℕ) (hab : a ≤ b),
      completedIntegralCommRingProjectionUnrestricted l E T b ≫
          (detailedSystem l E T).map (homOfLE hab).op =
        completedIntegralCommRingProjectionUnrestricted l E T a) : Prop :=
  ∃ r : ∀ n, pbcRestrict (level l E T q n).hom ⋙
        pbcRestrict (pbcAdicProjection T (pbcIntegralDatum l E) n) ≅
      pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E T n) ⋙
        pbcRestrict e.hom,
    (∀ (n : ℕ) (M : pbcModules T (integralCoefficientCommRingSheaf l E T n))
      (U : T.ProEtᵒᵖ) (x : M.val.obj U), ((r n).hom.app M).val.app U x = x) ∧
    ∃ α : ∀ n, pbcDerivedRestrict e.hom ⋙
          pbcDerivedExtend (pbcAdicProjection T (pbcIntegralDatum l E) n) ≅
        pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T n) ⋙
          pbcDerivedRestrict (level l E T q n).hom,
      (∀ (K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T))) (n : ℕ),
        (pbcDerivedScalarAdjunction
            (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
              ((pbcDerivedRestrict e.hom).obj K) ≫
          (restrictedComparison e (level l E T q n)
            (pbcAdicProjection T (pbcIntegralDatum l E) n)
            (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) (α n) K).hom =
          (pbcDerivedRestrict e.hom).map
            ((pbcDerivedScalarAdjunction
              (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K)) ∧
      (∀ (K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T)))
          (b a : ℕ) (hab : a ≤ b),
        transition (pbcAdicProjection T (pbcIntegralDatum l E) b)
            (pbcAdicQuotient T (pbcIntegralDatum l E) b a hab)
            (pbcAdicProjection T (pbcIntegralDatum l E) a)
            (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab)
            ((pbcDerivedRestrict e.hom).obj K) ≫
          (restrictedComparison e (level l E T q a)
            (pbcAdicProjection T (pbcIntegralDatum l E) a)
            (completedIntegralCommRingProjectionUnrestricted l E T a) (r a) (α a) K).hom =
        (restrictedComparison e (level l E T q b)
            (pbcAdicProjection T (pbcIntegralDatum l E) b)
            (completedIntegralCommRingProjectionUnrestricted l E T b) (r b) (α b) K).hom ≫
          (pbcDerivedRestrict e.hom).map
            (transition (completedIntegralCommRingProjectionUnrestricted l E T b)
              ((detailedSystem l E T).map (homOfLE hab).op)
              (completedIntegralCommRingProjectionUnrestricted l E T a) (hρ b a hab) K)) ∧
      (∀ K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T)),
        ∃ (hP : HasProduct (fun n ↦
              (reduction (pbcAdicProjection T (pbcIntegralDatum l E) n)).obj
                ((pbcDerivedRestrict e.hom).obj K)))
          (hQ : HasProduct (fun n ↦
              (reduction (completedIntegralCommRingProjectionUnrestricted l E T n)).obj K)),
          @RoosCompatible _ _ _ _ _ _ (pbcDerivedRestrict e.hom) K
            (fun n ↦ (reduction (pbcAdicProjection T (pbcIntegralDatum l E) n)).obj
              ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦
              (reduction (completedIntegralCommRingProjectionUnrestricted l E T n)).obj K)
            (fun n ↦ (pbcDerivedScalarAdjunction
              (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
                ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦ (pbcDerivedScalarAdjunction
              (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K)
            (fun n ↦ transition (pbcAdicProjection T (pbcIntegralDatum l E) (n + 1))
              (pbcAdicQuotient T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))
              (pbcAdicProjection T (pbcIntegralDatum l E) n)
              (pbcAdicProjection_comp T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))
              ((pbcDerivedRestrict e.hom).obj K))
            (fun n ↦ transition (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
              ((detailedSystem l E T).map (homOfLE (Nat.le_succ n)).op)
              (completedIntegralCommRingProjectionUnrestricted l E T n)
              (hρ (n + 1) n (Nat.le_succ n)) K)
            (fun n ↦ restrictedComparison e (level l E T q n)
              (pbcAdicProjection T (pbcIntegralDatum l E) n)
              (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) (α n) K) hP hQ)

/-- Projection-normalized comparison of the two completed integral coefficient presentations.
Source: Bhatt--Scholze, Section 6.5, convention before Definition 6.5.1,
Lemma 4.2.12 and Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-integral-coefficient-presentation-comparison).
The family q and the completed comparison e are quantified under their normalizations,
whose existence and uniqueness are the first and the ∃! conjuncts; so the remaining
clauses are about e_n and e_T themselves.

Proof: Descend the lift ring equivalence through the power ideals. Quotient
representatives give uniqueness and every transition identity. Reuse the normalized
constants-to-functions isomorphism and its naturality. The induced natural isomorphism
of inverse systems gives the completed comparison, uniquely fixed by its projections.
Restriction along a ring isomorphism has inverse restriction along its inverse, using
the canonical sectionwise composition and identity comparisons. Exact-functor descent
therefore gives inverse derived equivalences, preserving and reflecting homology bounds.
For each finite projection, take the left mate of the identity-on-sections restriction
square. The adjunction bijections and full faithfulness of both equivalences show this
mate is invertible; its defining equation is the required adjunction-unit equation.
The ordinary restriction squares commute with quotient composition on every section.
Exact-derived-square coherence descends that identity. Applying the adjunction bijection
to the two candidate transition maps proves their equality, for every quotient arrow.
Exact countable products on the pro-etale module categories give CountableAB4Star and
hence countable products in the derived categories. The product comparison induced by
the equivalence and the finite-level mates has the stated projection formula. Checking
projections proves compatibility with the augmentation and the shift; additivity gives
compatibility with the difference 1-s. -/
theorem comparison :
    (∀ n : ℕ, ∃! q : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ x : PbcIntegralRing l E,
        q (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down)) ∧
    (∀ (n : ℕ),
      (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom =
        AdicCoefficients.constantComparison T
          (PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))) ∧
    (∀ (i j : ℕᵒᵖ) (f : i ⟶ j),
      (adicLisseRingSystem T (pbcIntegralDatum l E).ideal).map f ≫
          (pbcLevelConstantComparison T (pbcIntegralDatum l E) j.unop).hom =
        (pbcLevelConstantComparison T (pbcIntegralDatum l E) i.unop).hom ≫
          (pbcAdicRings T (pbcIntegralDatum l E)).map f) ∧
    ∃ hρ : ∀ (b a : ℕ) (hab : a ≤ b),
        completedIntegralCommRingProjectionUnrestricted l E T b ≫
            (detailedSystem l E T).map (homOfLE hab).op =
          completedIntegralCommRingProjectionUnrestricted l E T a,
    ∀ q : ∀ n : ℕ, PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      (∀ (n : ℕ) (x : PbcIntegralRing l E),
        q n (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down)) →
    (∀ (b a : ℕ) (hab : a ≤ b),
      (q a).toRingHom.comp
          (reductionQuotientMap (pbcIntegralDatum l E).ideal b a hab) =
        ((ULift.ringEquiv : ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (a + 1)) ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))).comp
              (ULift.ringEquiv : ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (b + 1)) ≃+* _).toRingHom)).comp
          (q b).toRingHom) ∧
    (∀ (i j : ℕᵒᵖ) (f : i ⟶ j),
      (pbcAdicRings T (pbcIntegralDatum l E)).map f ≫ (level l E T q j.unop).hom =
        (level l E T q i.unop).hom ≫ (detailedSystem l E T).map f) ∧
    (∃! e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom) ∧
    ∀ e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      (∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom) →
    (pbcRestrict e.hom).IsEquivalence ∧
    (pbcRestrict e.inv).IsEquivalence ∧
    PreservesFiniteLimits (pbcRestrict e.hom) ∧
    PreservesFiniteColimits (pbcRestrict e.hom) ∧
    PreservesFiniteLimits (pbcRestrict e.inv) ∧
    PreservesFiniteColimits (pbcRestrict e.inv) ∧
    Nonempty (pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _) ∧
    Nonempty (pbcRestrict e.inv ⋙ pbcRestrict e.hom ≅ 𝟭 _) ∧
    (pbcDerivedRestrict e.hom).IsEquivalence ∧
    (pbcDerivedRestrict e.inv).IsEquivalence ∧
    Nonempty (pbcDerivedRestrict e.hom ⋙ pbcDerivedRestrict e.inv ≅ 𝟭 _) ∧
    Nonempty (pbcDerivedRestrict e.inv ⋙ pbcDerivedRestrict e.hom ≅ 𝟭 _) ∧
    (∀ (K : DerivedCategory
        (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T))) (m : ℤ),
      (DerivedCategory.IsLE ((pbcDerivedRestrict e.hom).obj K) m ↔
        DerivedCategory.IsLE K m) ∧
      (DerivedCategory.IsGE ((pbcDerivedRestrict e.hom).obj K) m ↔
        DerivedCategory.IsGE K m)) ∧
    (∀ (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m : ℤ),
      (DerivedCategory.IsLE ((pbcDerivedRestrict e.inv).obj K) m ↔
        DerivedCategory.IsLE K m) ∧
      (DerivedCategory.IsGE ((pbcDerivedRestrict e.inv).obj K) m ↔
        DerivedCategory.IsGE K m)) ∧
    DerivedCompatible l E T q e hρ := by
  classical
  constructor
  · intro n
    let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
      ULift.ringEquiv
    have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
        Ideal.map e.toRingHom ((pbcIntegralDatum l E).ideal ^ (n + 1)) := by
      simp [pbcIntegralDatum, Padic.coefficientExtensionIdeal, Ideal.map_pow,
        Ideal.map_span, Set.image_singleton, e, pbcUniformizer]
      rfl
    let q := Ideal.quotientEquiv _ _ e hI
    refine ⟨q.trans ULift.ringEquiv.symm, ?_, ?_⟩
    · intro x
      change ULift.up (q (Ideal.Quotient.mk _ x)) = _
      rw [Ideal.quotientEquiv_mk]
      rfl
    · intro e' he'
      apply RingEquiv.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (he' x).trans (by
        change ULift.up (Ideal.Quotient.mk _ x.down) =
          ULift.up (q (Ideal.Quotient.mk _ x))
        rw [Ideal.quotientEquiv_mk]
        rfl)
  constructor
  · intro n
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)).property
    change toSheafify _ _ ≫ (pbcLevelConstantComparison T _ n).hom.hom =
      toSheafify _ _ ≫ sheafifyMap _ _
    rw [← toSheafify_naturality]
    ext U b
    exact (pbcLevelConstantComparison_exists T (pbcIntegralDatum l E) n).exists.choose_spec U b
  refine ⟨fun _ _ f ↦ pbcConstantSystemComparison_naturality T _ f, ?_⟩
  have hρ (b a : ℕ) (hab : a ≤ b) :
      completedIntegralCommRingProjectionUnrestricted l E T b ≫
          (detailedSystem l E T).map (homOfLE hab).op =
        completedIntegralCommRingProjectionUnrestricted l E T a := by
    let ρ : (Functor.const ℕᵒᵖ).obj
        (completedIntegralCommRingSheafUnrestricted l E T) ⟶ detailedSystem l E T :=
      NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E T) (by
        intro n
        simp only [Functor.const_obj_map, detailedSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        apply RingCat.hom_ext
        apply RingHom.ext
        intro x
        have hw := congrArg (fun v ↦ (v.hom.app U).hom x)
          (limit.w (integralCoefficientSheafSystem l E T)
            (homOfLE (Nat.le_succ n)).op)
        simp only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] at hw
        convert hw.symm using 1 <;> rfl)
    exact (ρ.naturality (homOfLE hab).op).symm.trans (Category.id_comp _)
  refine ⟨hρ, ?_⟩
  intro q hq
  have ht (b a : ℕ) (hab : a ≤ b) :
      (q a).toRingHom.comp
          (reductionQuotientMap (pbcIntegralDatum l E).ideal b a hab) =
        ((ULift.ringEquiv : ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (a + 1)) ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))).comp
              (ULift.ringEquiv : ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (b + 1)) ≃+* _).toRingHom)).comp
          (q b).toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change q a (Ideal.Quotient.mk _ x) = _
    rw [hq]
    change ULift.up (Ideal.Quotient.mk _ x.down) =
      ULift.up (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1))
        ((q b (Ideal.Quotient.mk _ x)).down))
    rw [hq]
    rfl
  refine ⟨ht, ?_⟩
  have hn (i j : ℕᵒᵖ) (f : i ⟶ j) :
      (pbcAdicRings T (pbcIntegralDatum l E)).map f ≫ (level l E T q j.unop).hom =
        (level l E T q i.unop).hom ≫ (detailedSystem l E T).map f := by
    let C := constantSheaf (ProEt.topology T) CommRingCat.{u + 1}
    let c : adicLisseRingSystem T (pbcIntegralDatum l E).ideal ⟶ detailedSystem l E T :=
      NatTrans.ofOpSequence (fun n ↦ C.map (q n).toCommRingCatIso.hom) (by
        intro n
        simp only [adicLisseRingSystem, detailedSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change C.map _ ≫ C.map _ = C.map _ ≫ C.map _
        rw [← C.map_comp, ← C.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact ht (n + 1) n (Nat.le_succ n))
    let t := (pbcConstantSystemComparison T (pbcIntegralDatum l E)).inv ≫ c
    exact t.naturality f
  refine ⟨hn, ?_, ?_⟩
  · let F := adicLisseForget T
    let c : pbcAdicRings T (pbcIntegralDatum l E) ⟶ detailedSystem l E T :=
      { app n := (level l E T q n.unop).hom
        naturality _ _ f := hn _ _ f }
    have : IsIso c := NatIso.isIso_of_isIso_app c
    let w := Functor.isoWhiskerRight (asIso c) F
    have : PreservesLimit (pbcAdicRings T (pbcIntegralDatum l E)) F := by
      have : PreservesLimit (pbcAdicRings T (pbcIntegralDatum l E))
          (F ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}) :=
        inferInstanceAs (PreservesLimit (pbcAdicRings T (pbcIntegralDatum l E))
          (sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
            (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{u + 1} RingCat.{u + 1}).obj
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
      exact preservesLimit_of_reflects_of_preserves F
        (sheafToPresheaf (ProEt.topology T) RingCat.{u + 1})
    let v : detailedSystem l E T ⋙ F ⟶ integralCoefficientSheafSystem l E T :=
      NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
        intro n
        simp only [Functor.comp_map, detailedSystem, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp]
        rfl)
    have (n : ℕᵒᵖ) : IsIso (v.app n) := by
      change IsIso (𝟙 _)
      infer_instance
    have : IsIso v := NatIso.isIso_of_isIso_app v
    let eR := preservesLimitIso F (pbcAdicRings T (pbcIntegralDatum l E)) ≪≫
      HasLimit.isoOfNatIso (w ≪≫ asIso v)
    let e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T := F.preimageIso eR
    have he (n : ℕ) :
        e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
          pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (level l E T q n).hom := by
      apply F.map_injective
      rw [Functor.map_comp, Functor.map_comp]
      have hef : F.map e.hom = eR.hom := F.map_preimage _
      rw [hef]
      change eR.hom ≫ limit.π _ (op n) = _
      dsimp only [eR, Iso.trans_hom]
      rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
        preservesLimitIso_hom_π]
      simp [w, c, F, v, pbcAdicProjection]
    refine ⟨e, he, ?_⟩
    intro e' he'
    apply Iso.ext
    apply F.map_injective
    apply limit.hom_ext
    intro n
    change F.map e'.hom ≫ F.map (completedIntegralCommRingProjectionUnrestricted l E T
        n.unop) = F.map e.hom ≫ F.map (completedIntegralCommRingProjectionUnrestricted
          l E T n.unop)
    rw [← F.map_comp, ← F.map_comp, he', he]
  · intro e he
    let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
      integralCoefficientAbSheafify.{u, 0} T
    let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      integralCoefficientAbLocallyBijective.{u, 0} T
    obtain ⟨hf, hg, ⟨i⟩, ⟨j⟩⟩ := restrict_equivalence e
    have := hf
    have := hg
    have dhf : (pbcDerivedRestrict e.hom).IsEquivalence := by
      change (pbcRestrict e.hom).mapDerivedCategory.IsEquivalence
      infer_instance
    have dhg : (pbcDerivedRestrict e.inv).IsEquivalence := by
      change (pbcRestrict e.inv).mapDerivedCategory.IsEquivalence
      infer_instance
    have dhadd : (pbcDerivedRestrict e.hom).Additive := by
      change (pbcRestrict e.hom).mapDerivedCategory.Additive
      infer_instance
    have di : pbcDerivedRestrict e.hom ⋙ pbcDerivedRestrict e.inv ≅ 𝟭 _ :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso _
    have dj : pbcDerivedRestrict e.inv ⋙ pbcDerivedRestrict e.hom ≅ 𝟭 _ :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso _
    refine ⟨hf, hg, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨i⟩, ⟨j⟩, inferInstance, inferInstance, ⟨di⟩, ⟨dj⟩, ?_, ?_, ?_⟩
    · intro K m
      constructor
      · constructor
        · intro h
          exact (DerivedCategory.isLE_iff K m).2 fun n hn ↦
            Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
              (pbcRestrict e.hom)
              ((DerivedCategory.isLE_iff _ m).1 h n hn)
        · intro h
          exact (pbcRestrict e.hom).isLE_mapDerivedCategory_obj K m
      · constructor
        · intro h
          exact (DerivedCategory.isGE_iff K m).2 fun n hn ↦
            Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
              (pbcRestrict e.hom)
              ((DerivedCategory.isGE_iff _ m).1 h n hn)
        · intro h
          exact (pbcRestrict e.hom).isGE_mapDerivedCategory_obj K m
    · intro K m
      constructor
      · constructor
        · intro h
          exact (DerivedCategory.isLE_iff K m).2 fun n hn ↦
            Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
              (pbcRestrict e.inv)
              ((DerivedCategory.isLE_iff _ m).1 h n hn)
        · intro h
          exact (pbcRestrict e.inv).isLE_mapDerivedCategory_obj K m
      · constructor
        · intro h
          exact (DerivedCategory.isGE_iff K m).2 fun n hn ↦
            Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
              (pbcRestrict e.inv)
              ((DerivedCategory.isGE_iff _ m).1 h n hn)
        · intro h
          exact (pbcRestrict e.inv).isGE_mapDerivedCategory_obj K m
    · let r (n : ℕ) := restrictionSquare
        (pbcAdicProjection T (pbcIntegralDatum l E) n) (level l E T q n).hom
        e.hom (completedIntegralCommRingProjectionUnrestricted l E T n) (he n).symm
      have hr (n : ℕ) (M : pbcModules T (integralCoefficientCommRingSheaf l E T n))
          (U : T.ProEtᵒᵖ) (x : M.val.obj U) : ((r n).hom.app M).val.app U x = x :=
        restrictionSquare_hom _ _ _ _ _ M U x
      have ha (n : ℕ) : ∃ α : pbcDerivedRestrict e.hom ⋙
            pbcDerivedExtend (pbcAdicProjection T (pbcIntegralDatum l E) n) ≅
          pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l E T n) ⋙
            pbcDerivedRestrict (level l E T q n).hom,
          ∀ K, (pbcDerivedScalarAdjunction
              (pbcAdicProjection T (pbcIntegralDatum l E) n)).unit.app
                ((pbcDerivedRestrict e.hom).obj K) ≫
            (restrictedComparison e (level l E T q n)
              (pbcAdicProjection T (pbcIntegralDatum l E) n)
              (completedIntegralCommRingProjectionUnrestricted l E T n) (r n) α K).hom =
            (pbcDerivedRestrict e.hom).map
              ((pbcDerivedScalarAdjunction
                (completedIntegralCommRingProjectionUnrestricted l E T n)).unit.app K) := by
        have : (pbcRestrict (level l E T q n).hom).IsEquivalence :=
          (restrict_equivalence (level l E T q n)).1
        have : (pbcDerivedRestrict (level l E T q n).hom).IsEquivalence := by
          change (pbcRestrict (level l E T q n).hom).mapDerivedCategory.IsEquivalence
          infer_instance
        obtain ⟨α, hα⟩ := square_iso
          (pbcDerivedScalarAdjunction (pbcAdicProjection T (pbcIntegralDatum l E) n))
          (pbcDerivedScalarAdjunction (completedIntegralCommRingProjectionUnrestricted l E T n))
          (pbcDerivedRestrict e.hom) (pbcDerivedRestrict (level l E T q n).hom)
          (derivedSquare e (level l E T q n)
            (pbcAdicProjection T (pbcIntegralDatum l E) n)
            (completedIntegralCommRingProjectionUnrestricted l E T n) (r n))
        refine ⟨α, fun K ↦ ?_⟩
        simpa only [restrictedComparison, Iso.trans_hom, Functor.mapIso_hom,
          Iso.app_hom, Category.assoc] using hα K
      choose α hα using ha
      have htower (K : DerivedCategory
          (pbcModules T (completedIntegralCommRingSheafUnrestricted l E T)))
          (b a : ℕ) (hab : a ≤ b) :
          transition (pbcAdicProjection T (pbcIntegralDatum l E) b)
              (pbcAdicQuotient T (pbcIntegralDatum l E) b a hab)
              (pbcAdicProjection T (pbcIntegralDatum l E) a)
              (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab)
              ((pbcDerivedRestrict e.hom).obj K) ≫
            (restrictedComparison e (level l E T q a)
              (pbcAdicProjection T (pbcIntegralDatum l E) a)
              (completedIntegralCommRingProjectionUnrestricted l E T a)
              (r a) (α a) K).hom =
          (restrictedComparison e (level l E T q b)
              (pbcAdicProjection T (pbcIntegralDatum l E) b)
              (completedIntegralCommRingProjectionUnrestricted l E T b)
              (r b) (α b) K).hom ≫
            (pbcDerivedRestrict e.hom).map
              (transition (completedIntegralCommRingProjectionUnrestricted l E T b)
                ((detailedSystem l E T).map (homOfLE hab).op)
                (completedIntegralCommRingProjectionUnrestricted l E T a) (hρ b a hab) K) := by
        let πa := pbcAdicProjection T (pbcIntegralDatum l E) a
        let πb := pbcAdicProjection T (pbcIntegralDatum l E) b
        let ρa := completedIntegralCommRingProjectionUnrestricted l E T a
        let ρb := completedIntegralCommRingProjectionUnrestricted l E T b
        let qp := pbcAdicQuotient T (pbcIntegralDatum l E) b a hab
        let qs := (detailedSystem l E T).map (homOfLE hab).op
        let c := pbcRestrictComp πb qp πa
          (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab)
        let c' := pbcRestrictComp ρb qs ρa (hρ b a hab)
        let s := restrictionSquare qp (level l E T q a).hom
          (level l E T q b).hom qs (hn (op b) (op a) (homOfLE hab).op)
        have ho := ordinary_coherence e.hom πa πb ρa ρb
          (level l E T q a).hom (level l E T q b).hom qp qs (he a).symm (he b).symm
          (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab) (hρ b a hab)
          (hn (op b) (op a) (homOfLE hab).op)
        have hd := restriction_coherence
          (pbcRestrict πa) (pbcRestrict πb) (pbcRestrict ρa) (pbcRestrict ρb)
          (pbcRestrict e.hom) (pbcRestrict (level l E T q a).hom)
          (pbcRestrict (level l E T q b).hom) (pbcRestrict qp) (pbcRestrict qs)
          c c' (r a) (r b) s ho
        have ht := transition_transport
          (pbcDerivedScalarAdjunction πa) (pbcDerivedScalarAdjunction πb)
          (pbcDerivedScalarAdjunction ρa) (pbcDerivedScalarAdjunction ρb)
          (pbcDerivedRestrict e.hom) (pbcDerivedRestrict (level l E T q a).hom)
          (pbcDerivedRestrict (level l E T q b).hom)
          (pbcDerivedRestrict qp) (pbcDerivedRestrict qs)
          (pbcDerivedRestrictComp πb qp πa
            (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a hab))
          (pbcDerivedRestrictComp ρb qs ρa (hρ b a hab))
          (derivedSquare e (level l E T q a) πa ρa (r a))
          (derivedSquare e (level l E T q b) πb ρb (r b))
          (CategoryTheory.Functor.mapDerivedCategorySquareIso s) hd
          (α a) (α b) (fun K ↦ hα a K) (fun K ↦ hα b K) K
        simpa only [transition, pbcReductionTransition, restrictedComparison,
          Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.id_obj,
          Functor.comp_obj, πa, πb, ρa, ρb, qp, qs] using ht
      refine ⟨r, hr, α, (fun K n ↦ hα n K), htower, ?_⟩
      intro K
      have := derived_products T (pbcAdicCompletion T (pbcIntegralDatum l E))
      have := derived_products T (completedIntegralCommRingSheafUnrestricted l E T)
      refine ⟨inferInstance, inferInstance, ?_⟩
      exact roos_transport (pbcDerivedRestrict e.hom) K _ _ _ _ _ _ _
        (fun n ↦ hα n K) (fun n ↦ htower K (n + 1) n (Nat.le_succ n))

end WeilConjectures.IntegralCoefficientPresentation
