/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
import WeilConjectures.PoincareDuality.CompletedInverseImageScalarCounit
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismScalarComparisonAgreement

/-! # Scalar extension and the normalized pullback identities

Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
lem-fix-weil-operations.proof.md, first paragraph, pullback and inverse automorphism squares
(blueprint: lem-pod-pullback-identities-scalar-extension).

The compositor and scalar comparison are the whole-system realization maps. The inverse
identity uses the inverse of the specified quotient-cone kappa, followed by the
section-normalized inverse-image counit. No natural isomorphism is supplied arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The site identification of successive postcomposition by the inverse and by g.
Its arrows are identity on the underlying schemes. Source: Stacks 09A5 and 03D6;
blueprint inverse automorphism squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentitySiteUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    𝟭 Y.ProEt ≅ proEtaleIsoPostcompose (inv g) ⋙ proEtaleIsoPostcompose g :=
  (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y (inv g ≫ g)
    (IsIso.inv_hom_id g)).symm ≪≫
      MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale (inv g)) (inferInstance : WeaklyEtale g)

/-- The inverse-image counit is uniquely fixed by its value on every section.
Source: Stacks 09A5, 03D6; blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof: postcompose structure maps first with inv g and then g. The displayed site
unit identifies the result with the original object by the identity on its scheme.
Constant-section maps respect this identification at every finite quotient; their
limit projection equations give the same fact for completed coefficients. Thus the
restriction in the formula is linear for the transported actions. Its inverse is
restriction along the inverse site arrow. Restrictions commute with module maps,
so these maps form a natural isomorphism. Sectionwise equality proves uniqueness. -/
theorem pullbackIdentityModuleCounit_existsUnique
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! e : inverseImageIntegralModules l E g ⋙ inverseImageIntegralModules l E (inv g) ≅
        𝟭 (integralTowerModules l E Y),
      ∀ (M : integralTowerModules l E Y) (U : Y.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj
          ((proEtaleIsoPostcompose (inv g)).obj U)))),
        (e.hom.app M).val.app (op U) x =
          M.val.map ((pullbackIdentitySiteUnit g).hom.app U).op x := by
  simpa only [pullbackIdentitySiteUnit, integralInverseImageCounitSite,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom] using
    integralInverseImageCounit_existsUnique l E g

/-- The uniquely section-normalized module counit. Source: Stacks 09A5, 03D6;
blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityModuleCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (pullbackIdentityModuleCounit_existsUnique l E g).exists.choose

/-- Apply the section-normalized counit termwise and localize, including the exact
functor composition and identity comparisons. Source: Stacks 03D6, 05RU;
blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityInverseImageCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ inverseImageIntegralDerived l E (inv g) ≅
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (inverseImageIntegralModules l E (inv g))) ≪≫
      Functor.mapDerivedCategoryNatIso (pullbackIdentityModuleCounit l E g) ≪≫
        Functor.mapDerivedCategoryIdIso _

/-- Kappa is invertible on exactly the constructible complete inputs in the node.
Source: blueprint inverse squares; normalization of the specified cone map
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof: apply lem-weil-isomorphism-derived-pullback-comparison-normalization to the
canonical reduction/limit calculus of lem-coef-derived-system-evaluation-calculus.
The intrinsic constructible predicate includes derived completeness. The normalization
identifies kappa followed by theta with inverse image of the completion unit. That unit
is invertible on complete objects, so the displayed kappa has a two-sided inverse. -/
theorem pullbackIdentityKappa_isIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso (inverseImagePullbackComparisonDerived l E g hX hY K.obj) := by
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    ((hY y).map (IsLocalRing.residue (Y.presheaf.stalk y))).invertible
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨κ, hk, _, hn, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨θ, hθ⟩ := hn S hS
  have : IsIso (S.adjunction.unit.app K.obj) :=
    by
      obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
      let T := (D.coefficient E).system Y
      let := (D.coefficient E).complete Y K
      rw [← T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K.obj]
      infer_instance
  rw [← hk K.obj, hθ K.obj]
  infer_instance

/-- Lambda is the inverse of the specified quotient-cone kappa, rather than an
unspecified isomorphism with the same endpoints. Source: blueprint inverse squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityLambda
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l E g).obj K.obj ≅
      (inverseImageIntegralDerived l E g).obj K.obj :=
  letI := pullbackIdentityKappa_isIso l E g hX hY K
  (asIso (inverseImagePullbackComparisonDerived l E g hX hY K.obj)).symm

/-- The inverse identity epsilon is lambda for inv g, inverse image of lambda for g,
then the canonical inverse-image counit, in that order. Source: blueprint inverse squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityEpsilon
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l E (inv g)).obj
        ((integralDerivedPullback l E g).obj K.obj) ≅ K.obj :=
  let hX := fun x : X ↦ isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
    ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
      isUnit_of_invertible (l : X.residueField x))
  let hY := fun y : Y ↦ isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
    ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
      isUnit_of_invertible (l : Y.residueField y))
  pullbackIdentityLambda l E (inv g) hY hX
      ((constructibleIntegralPullback l E g).obj K) ≪≫
    (inverseImageIntegralDerived l E (inv g)).mapIso
      (pullbackIdentityLambda l E g hX hY K) ≪≫
    (pullbackIdentityInverseImageCounit l E g).app K.obj

private theorem mate_postcompose
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {F : C} {O N : B} (b : F ⟶ L.obj O) (z : O ⟶ N) :
    R.map (b ≫ L.map z) ≫ adj.counit.app N =
      R.map b ≫ adj.counit.app O ≫ z := by
  simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg (fun q ↦ R.map b ≫ q) (adj.counit.naturality z)

private theorem mate_comparison
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {F G : C} {O N : B} (b : F ≅ L.obj O) (c : G ≅ L.obj N) (t : O ⟶ N) :
    R.map (b.hom ≫ L.map t ≫ c.inv) ≫
        (R.map c.hom ≫ adj.counit.app N) =
      (R.map b.hom ≫ adj.counit.app O) ≫ t := by
  calc
    _ = R.map (b.hom ≫ L.map t) ≫ adj.counit.app N := by
      rw [← Category.assoc, ← R.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      simpa only [Category.assoc] using mate_postcompose R L adj b.hom t

private theorem reduction_reflects
    {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (L : B ⥤ C) (adj : R ⊣ L)
    {K J : C} [Mono (adj.unit.app J)] (f g : K ⟶ J)
    (h : R.map f = R.map g) : f = g := by
  apply (cancel_mono (adj.unit.app J)).1
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  dsimp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg]
  exact congrArg (fun t ↦ adj.unit.app K ≫ L.map t) h

private theorem composition_reduction
    (D : IntegralComparisonSystem.{u} l) {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    ((D.coefficient E).system Z).reduction.map
        (integralComparisonComposition l E D h k K).hom ≫
      (integralComparisonPullbackCounit l E h ((D.coefficient E).system W)
        ((D.coefficient E).system Z) ((D.coefficient E).roos Z)
        ((D.coefficient E).pullback h)).app
          ((integralDerivedPullback l E k).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l E h).map
        ((integralComparisonPullbackCounit l E k ((D.coefficient E).system V)
          ((D.coefficient E).system W) ((D.coefficient E).roos W)
          ((D.coefficient E).pullback k)).app K.obj) =
    (integralComparisonPullbackCounit l E (h ≫ k) ((D.coefficient E).system V)
      ((D.coefficient E).system Z) ((D.coefficient E).roos Z)
      ((D.coefficient E).pullback (h ≫ k))).app K.obj ≫
        (integralComparisonSystemComposition l E h k).hom.app
          (((D.coefficient E).system V).reduction.obj K.obj) := by
  have hh := mate_comparison _ _ ((D.coefficient E).system Z).adjunction
    (((D.coefficient E).pullback (h ≫ k)).realization.app K.obj)
    (integralComparisonEta l E D h k K)
    ((integralComparisonSystemComposition l E h k).hom.app
      (((D.coefficient E).system V).reduction.obj K.obj))
  have he := mate_postcompose _ _ ((D.coefficient E).system Z).adjunction
    (((D.coefficient E).pullback h).realization.hom.app
      ((integralDerivedPullback l E k).obj K.obj))
    ((integralComparisonDerivedSequencePullback l E h).map
      ((integralComparisonPullbackCounit l E k ((D.coefficient E).system V)
        ((D.coefficient E).system W) ((D.coefficient E).roos W)
        ((D.coefficient E).pullback k)).app K.obj))
  have hEta := he
  change
      ((D.coefficient E).system Z).reduction.map
          (integralComparisonEta l E D h k K).hom ≫
        ((D.coefficient E).system Z).adjunction.counit.app _ = _ at hEta
  rw [hEta] at hh
  simpa only [integralComparisonComposition, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, integralComparisonPullbackCounit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using hh

private theorem scalar_reduction
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (K : sfIntegralConstructibleCategory l E Y) :
    ((D.coefficient L).system X).reduction.map
        (integralComparisonScalar l E L ι D f K).hom ≫
      (integralComparisonPullbackCounit l L f ((D.coefficient L).system Y)
        ((D.coefficient L).system X) ((D.coefficient L).roos X)
        ((D.coefficient L).pullback f)).app
          ((integralScalarExtension l E L ι Y).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l L f).map
        ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
          ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
          ((D.scalar E L ι).model Y)).app K.obj) =
    (integralComparisonScalarCounit l E L ι X ((D.coefficient E).system X)
      ((D.coefficient L).system X) ((D.coefficient L).roos X)
      ((D.scalar E L ι).model X)).app ((integralDerivedPullback l E f).obj K.obj) ≫
        (integralComparisonDerivedSequenceScalar l E L ι X).map
          ((integralComparisonPullbackCounit l E f ((D.coefficient E).system Y)
            ((D.coefficient E).system X) ((D.coefficient E).roos X)
            ((D.coefficient E).pullback f)).app K.obj) ≫
        (integralComparisonSystemScalarPullback l E L ι f).hom.app
          (((D.coefficient E).system Y).reduction.obj K.obj) := by
  let R := ((D.coefficient L).system X).reduction
  let T := coefficientSequenceLimit l L X
  let adj := ((D.coefficient L).system X).adjunction
  have hh := mate_comparison R T adj
    (integralComparisonLambda l E L ι D f K)
    (integralComparisonMu l E L ι D f K) (𝟙 _)
  have hLam := mate_postcompose R T adj (((D.scalar E L ι).model X).realization.hom.app
      ((integralDerivedPullback l E f).obj K.obj))
    ((integralComparisonDerivedSequenceScalar l E L ι X).map
      ((integralComparisonPullbackCounit l E f ((D.coefficient E).system Y)
        ((D.coefficient E).system X) ((D.coefficient E).roos X)
        ((D.coefficient E).pullback f)).app K.obj))
  have hMu := mate_postcompose R T adj (((D.coefficient L).pullback f).realization.hom.app
      ((integralScalarExtension l E L ι Y).obj K.obj))
    ((integralComparisonDerivedSequencePullback l L f).map
      ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
        ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
        ((D.scalar E L ι).model Y)).app K.obj) ≫
      (integralComparisonSystemScalarPullback l E L ι f).inv.app
        (((D.coefficient E).system Y).reduction.obj K.obj))
  have hLam' := hLam
  change R.map (integralComparisonLambda l E L ι D f K).hom ≫
      adj.counit.app _ = _ at hLam'
  have hMu' : R.map (integralComparisonMu l E L ι D f K).hom ≫
      adj.counit.app _ =
        R.map (((D.coefficient L).pullback f).realization.hom.app
          ((integralScalarExtension l E L ι Y).obj K.obj)) ≫
        adj.counit.app _ ≫
        (integralComparisonDerivedSequencePullback l L f).map
          ((integralComparisonScalarCounit l E L ι Y ((D.coefficient E).system Y)
            ((D.coefficient L).system Y) ((D.coefficient L).roos Y)
            ((D.scalar E L ι).model Y)).app K.obj) ≫
        (integralComparisonSystemScalarPullback l E L ι f).inv.app
          (((D.coefficient E).system Y).reduction.obj K.obj) := by
    simpa only [integralComparisonMu, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Functor.comp_obj, Functor.id_obj, Category.assoc] using hMu
  rw (transparency := .all) [T.map_id, Category.id_comp, Category.comp_id] at hh
  rw (transparency := .all) [hLam', hMu'] at hh
  have h := congrArg (fun a ↦ a ≫
    (integralComparisonSystemScalarPullback l E L ι f).hom.app
      (((D.coefficient E).system Y).reduction.obj K.obj)) hh
  simpa only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    integralComparisonScalarCounit, integralComparisonPullbackCounit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using h

private theorem counit_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    pullbackIdentityInverseImageCounit l E g = integralInverseImageDerivedCounit l E g := by
  have hm : pullbackIdentityModuleCounit l E g = integralInverseImageCounit l E g := by
    apply (pullbackIdentityModuleCounit_existsUnique l E g).unique
    · exact (pullbackIdentityModuleCounit_existsUnique l E g).exists.choose_spec
    · simpa only [integralInverseImageCounit, pullbackIdentitySiteUnit,
        integralInverseImageCounitSite, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
        Iso.symm_hom] using
        (integralInverseImageCounit_existsUnique l E g).exists.choose_spec
  unfold pullbackIdentityInverseImageCounit integralInverseImageDerivedCounit
  rw [hm]

private theorem inverse_naturality
    {C B : Type*} [Category C] [Category B] {F G : C ⥤ B} (κ : F ⟶ G)
    {K J : C} (f : K ⟶ J) [IsIso (κ.app K)] [IsIso (κ.app J)] :
    G.map f ≫ inv (κ.app J) = inv (κ.app K) ≫ F.map f := by
  have h := congrArg (fun a ↦ inv (κ.app K) ≫ a ≫ inv (κ.app J)) (κ.naturality f)
  simpa only [Category.assoc, IsIso.hom_inv_id, IsIso.inv_hom_id_assoc,
    Category.comp_id] using h.symm

private theorem lambda_naturality {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K J : sfIntegralConstructibleCategory l E Y) (f : K.obj ⟶ J.obj) :
    (integralDerivedPullback l E g).map f ≫ (pullbackIdentityLambda l E g hX hY J).hom =
      (pullbackIdentityLambda l E g hX hY K).hom ≫
        (inverseImageIntegralDerived l E g).map f := by
  obtain ⟨κ, hk, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  have : IsIso (κ.app K.obj) := hk K.obj ▸ pullbackIdentityKappa_isIso l E g hX hY K
  have : IsIso (κ.app J.obj) := hk J.obj ▸ pullbackIdentityKappa_isIso l E g hX hY J
  simpa only [pullbackIdentityLambda, Iso.symm_hom, asIso_inv, hk] using
    inverse_naturality κ f

private theorem beta_naturality
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K J : sfIntegralConstructibleCategory l E Y) (f : K.obj ⟶ J.obj) :
    (integralScalarExtension l E L ι X).map ((inverseImageIntegralDerived l E g).map f) ≫
        isomorphismComparisonScalarBeta l E L ι g hX hY J.obj J.property =
      isomorphismComparisonScalarBeta l E L ι g hX hY K.obj K.property ≫
        (inverseImageIntegralDerived l L g).map
          ((integralScalarExtension l E L ι Y).map f) := by
  let CK : sfIntegralConstructibleCategory l E X :=
    ⟨_, (isomorphismComparisonInputs_constructible l E g hX hY K.obj K.property).1⟩
  let CJ : sfIntegralConstructibleCategory l E X :=
    ⟨_, (isomorphismComparisonInputs_constructible l E g hX hY J.obj J.property).1⟩
  have : IsIso ((scalarCompletion l E L ι X).app CK.obj) :=
    (scalarCompletionIso l E L ι X CK.obj CK.property.1).isIso_hom
  have : IsIso ((scalarCompletion l E L ι X).app CJ.obj) :=
    (scalarCompletionIso l E L ι X CJ.obj CJ.property.1).isIso_hom
  unfold isomorphismComparisonScalarBeta scalarCompletionIso
  simp only [asIso_inv, Category.assoc]
  rw [reassoc_of% (inverse_naturality (scalarCompletion l E L ι X)
    ((inverseImageIntegralDerived l E g).map f))]
  have hb := (isomorphismScalarTensorDerived l E L ι g).hom.naturality f
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb, ← Functor.map_comp]
  rw [(scalarCompletion l E L ι Y).naturality f, Functor.map_comp]

private theorem lambda_scalar
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E L ι D g K).hom ≫
        (pullbackIdentityLambda l L g hX hY
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom =
      (integralScalarExtension l E L ι X).map (pullbackIdentityLambda l E g hX hY K).hom ≫
        isomorphismComparisonScalarBeta l E L ι g hX hY K.obj K.property := by
  have h := isomorphismComparison_scalarExtension l E L ι g hX hY K.obj K.property
  have ha := isomorphismScalarComparisonAgreement l E L ι D g K
  change (integralComparisonScalar l E L ι D g K).hom =
    isomorphismComparisonScalarAlpha l E L ι g hX hY K.obj K.property at ha
  rw [← ha] at h
  let := pullbackIdentityKappa_isIso l E g hX hY K
  let := pullbackIdentityKappa_isIso l L g hX hY
    ((integralComparisonConstructibleScalar l E L ι Y).obj K)
  have hkL : IsIso (inverseImagePullbackComparisonDerived l L g hX hY
      ((integralScalarExtension l E L ι Y).obj K.obj)) := by
    with_unfolding_all
      exact pullbackIdentityKappa_isIso l L g hX hY
        ((integralComparisonConstructibleScalar l E L ι Y).obj K)
  have hh := congrArg (fun a ↦
    (integralScalarExtension l E L ι X).map
      (inv (inverseImagePullbackComparisonDerived l E g hX hY K.obj)) ≫ a ≫
    inv (inverseImagePullbackComparisonDerived l L g hX hY
      ((integralScalarExtension l E L ι Y).obj K.obj))) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id] at hh
  rw (transparency := .all) [(integralScalarExtension l E L ι X).map_id,
    Category.id_comp, IsIso.hom_inv_id, Category.comp_id] at hh
  dsimp only [integralComparisonConstructibleScalar,
    sfConstructibleIntegralScalarExtension, ObjectProperty.lift, ObjectProperty.ι,
    inducedFunctor, Functor.comp_obj]
  simpa only [pullbackIdentityLambda, Iso.symm_hom, asIso_inv] using hh

/-- Composition and inverse identities commute with integral scalar extension, for the
specified whole-system comparison families. Source: blueprint main-20261015,
sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof, following the node:
1. Apply lem-trf-integral-pullback-comparison-realization to E into L, h, k and K.
Its entire quotient-diagram scalar/composition equation is the first conjunct.
The composition and scalar maps here are exactly its counit-built families.
2. For an isomorphism g write P=Lg*, Q=L(inv g)*, G=g-inverse and H=(inv g)-inverse.
The inverse images are exact site equivalences and preserve the required domains
(lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback).
The normalization lemma inverts the specified kappa. Thus lambda=kappa inverse
and epsilon=u H(lambda) lambda, with u the section-normalized inverse-image counit.
3. Lem-weil-isomorphism-comparison-scalar-extension gives the kappa/scalar square.
Lem-pod-isomorphism-scalar-comparison-agreement identifies its tensor/completion alpha
with the whole-system alpha used here, for both g and inv g. Cancel the invertible
kappas to obtain lambda_L alpha = beta T(lambda_E), for both isomorphisms.
4. Write C for ordinary derived coefficient change and chi:C iso T for the specified
finite-free completed comparison. Beta=G(chi) b chi inverse. The sectionwise tensor
map b only reindexes x tensor a. Reindexing by g and inv g returns x and a unchanged.
Consequently u_L H(b_g) b_inv = C(u_E), already on complexes, and hence after
sheafification and localization. Substitution cancels the adjacent chi inverses;
naturality of u and chi gives u_L H(beta_g) beta_inv = T(u_E).
5. Expand epsilon_L. Naturality of lambda for inv g and step 3 replace the two lambdas
by beta T(lambda_E). Naturality of beta_inv moves T(lambda_g) past beta_inv.
Step 4 replaces the initial three factors by T(u_E). Functoriality of T combines
the remaining factors to T(epsilon_E). This is the second conjunct, as an equality
of whole derived arrows; no finite-reduction detection or Tor-amplitude bound is used. -/
theorem pullbackIdentities_scalarExtension
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l) :
    (∀ {V W Z : Scheme.{u}}
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)]
      (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
      (integralScalarExtensionOfUniverses l E L ι Z).map
          (integralComparisonComposition l E D h k K).hom ≫
        (integralComparisonScalar l E L ι D h
          ((constructibleIntegralPullback l E k).obj K)).hom ≫
        (integralDerivedPullback l L h).map
          (integralComparisonScalar l E L ι D k K).hom =
      (integralComparisonScalar l E L ι D (h ≫ k) K).hom ≫
        (integralComparisonComposition l L D h k
          ((integralComparisonConstructibleScalar l E L ι V).obj K)).hom) ∧
    (∀ {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      (K : sfIntegralConstructibleCategory l E Y),
      (integralComparisonScalar l E L ι D (inv g)
          ((constructibleIntegralPullback l E g).obj K)).hom ≫
        (integralDerivedPullback l L (inv g)).map
          (integralComparisonScalar l E L ι D g K).hom ≫
        (pullbackIdentityEpsilon l L g
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom =
      (integralScalarExtensionOfUniverses l E L ι Y).map
        (pullbackIdentityEpsilon l E g K).hom) := by
  constructor
  · intro V W Z _ _ _ h k K
    let RE (A : Scheme.{u}) := ((D.coefficient E).system A).reduction
    let RL (A : Scheme.{u}) := ((D.coefficient L).system A).reduction
    let UE {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonDerivedSequencePullback l E f
    let UL {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonDerivedSequencePullback l L f
    let S (A : Scheme.{u}) := integralComparisonDerivedSequenceScalar l E L ι A
    let rE {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonPullbackCounit l E f ((D.coefficient E).system B)
        ((D.coefficient E).system A) ((D.coefficient E).roos A)
        ((D.coefficient E).pullback f)
    let rL {A B : Scheme.{u}} (f : A ⟶ B) :=
      integralComparisonPullbackCounit l L f ((D.coefficient L).system B)
        ((D.coefficient L).system A) ((D.coefficient L).roos A)
        ((D.coefficient L).pullback f)
    let rS (A : Scheme.{u}) := integralComparisonScalarCounit l E L ι A
      ((D.coefficient E).system A) ((D.coefficient L).system A)
      ((D.coefficient L).roos A) ((D.scalar E L ι).model A)
    let PK := (constructibleIntegralPullback l E k).obj K
    let TK := (integralComparisonConstructibleScalar l E L ι V).obj K
    let PTK := (constructibleIntegralPullback l L k).obj TK
    let ah := (integralComparisonScalar l E L ι D h PK).hom
    let ak := (integralComparisonScalar l E L ι D k K).hom
    let a := (integralComparisonScalar l E L ι D (h ≫ k) K).hom
    let cE := (integralComparisonComposition l E D h k K).hom
    let cL := (integralComparisonComposition l L D h k TK).hom
    have nh := (rL h).naturality ak
    have ns := (rS Z).naturality cE
    have na := (integralComparisonSystemScalarPullback l E L ι h).hom.naturality
      ((rE k).app K.obj)
    have nc := (integralComparisonSystemComposition l L h k).hom.naturality
      ((rS V).app K.obj)
    dsimp only [Functor.comp_map] at nh ns na nc
    have ce := composition_reduction l E D h k K
    have cl := composition_reduction l L D h k TK
    have sh := scalar_reduction l E L ι D h PK
    have sk := scalar_reduction l E L ι D k K
    have shk := scalar_reduction l E L ι D (h ≫ k) K
    have sk' := congrArg (UL h).map sk
    have ce' := congrArg (S Z).map ce
    simp only [Functor.map_comp] at sk' ce'
    have mix := NatTrans.congr_app
      ((integralQuotientMixedCoherence.{u, u} l).derived_mixed E L ι h k)
        ((RE V).obj K.obj)
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at mix
    let := (D.scalar E L ι).effective V K
    let := (D.coefficient L).effective k TK
    let := (D.coefficient L).effective h PTK
    let target := (constructibleIntegralPullback l L h).obj PTK
    let hcomplete : IsIso (((D.coefficient L).system Z).adjunction.unit.app
        ((integralDerivedPullback l L h).obj
          ((integralDerivedPullback l L k).obj
            ((integralScalarExtension l E L ι V).obj K.obj)))) := by
      with_unfolding_all exact (D.coefficient L).complete Z target
    apply reduction_reflects (RL Z) (coefficientSequenceLimit l L Z)
      ((D.coefficient L).system Z).adjunction
    apply (cancel_mono ((rL h).app PTK.obj ≫
      (UL h).map ((rL k).app TK.obj) ≫
      (UL h).map ((UL k).map ((rS V).app K.obj)))).1
    simp only [Functor.map_comp, Category.assoc]
    change (RL Z).map ((integralScalarExtensionOfUniverses l E L ι Z).map cE) ≫
      (RL Z).map ah ≫ (RL Z).map ((integralDerivedPullback l L h).map ak) ≫
      (rL h).app PTK.obj ≫ (UL h).map ((rL k).app TK.obj) ≫
      (UL h).map ((UL k).map ((rS V).app K.obj)) = _
    dsimp only [ah, ak, a, cE, cL, PK, TK, PTK]
    rewrite (transparency := .default) [reassoc_of% nh]
    rewrite (transparency := .default) [sk']
    rewrite (transparency := .default) [reassoc_of% sh]
    rewrite (transparency := .default) [← reassoc_of% na]
    rewrite (transparency := .default) [reassoc_of% ns]
    rewrite (transparency := .default) [reassoc_of% ce']
    rewrite (transparency := .default) [mix]
    rewrite (transparency := .default) [← reassoc_of% shk]
    rewrite (transparency := .default) [nc]
    rewrite (transparency := .default) [reassoc_of% cl]
    rfl
  · intro X Y g _ _ _ K
    let hX := fun x : X ↦ isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
      ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
        isUnit_of_invertible (l : X.residueField x))
    let hY := fun y : Y ↦ isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
      ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
        isUnit_of_invertible (l : Y.residueField y))
    let PK := (constructibleIntegralPullback l E g).obj K
    let TK := (integralComparisonConstructibleScalar l E L ι Y).obj K
    let TPK := (integralComparisonConstructibleScalar l E L ι X).obj PK
    let PTK := (constructibleIntegralPullback l L g).obj TK
    let GK : sfIntegralConstructibleCategory l E X :=
      ⟨_, (isomorphismComparisonInputs_constructible l E g hX hY K.obj K.property).1⟩
    have hn := lambda_naturality l L (inv g) hY hX TPK PTK
      (integralComparisonScalar l E L ι D g K).hom
    have hg := lambda_scalar l E L ι D g hX hY K
    have hi := lambda_scalar l E L ι D (inv g) hY hX PK
    have hb := beta_naturality l E L ι (inv g) hY hX PK GK
      (pullbackIdentityLambda l E g hX hY K).hom
    have hu := (completedInverseImage_scalarCounit l E L ι g hX hY K).2
    simp only [pullbackIdentityEpsilon, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    with_unfolding_all rw [reassoc_of% hn, reassoc_of% hi]
    with_unfolding_all rw [← Functor.map_comp_assoc, hg, Functor.map_comp, Category.assoc]
    with_unfolding_all rw [← reassoc_of% hb, counit_eq, counit_eq]
    dsimp only [GK, TK, integralComparisonConstructibleScalar,
      sfConstructibleIntegralScalarExtension, ObjectProperty.lift, ObjectProperty.ι,
      Functor.comp_obj] at *
    with_unfolding_all erw [hu]
    simp only [Functor.map_comp]
    with_unfolding_all rfl

end WeilConjectures
