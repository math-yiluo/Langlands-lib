/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
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
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Completed scalar comparison and the inverse-image counit

Source: main-20261015, sec-six-functors/sk-rem-sf-pf-done,
lem-fix-weil-operations.proof.md, first paragraph; Stacks Tags 03D6, 03EK, 015F and 04VG
(blueprint: lem-pod-completed-inverse-image-scalar-counit).

The counit is fixed on sections by the identity on the underlying schemes. The ordinary
scalar functor is the recorded exact tensor model, and its completion comparison is the
specified comparison under the normalized ordinary-derived-model identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The canonical reindexing identification for inverse isomorphisms, with identity
underlying scheme maps. Source: Stacks Tag 03D6 and the first paragraph of
lem-fix-weil-operations.proof.md
(blueprint: lem-pod-completed-inverse-image-scalar-counit). -/
def integralInverseImageCounitSite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    proEtaleIsoPostcompose (inv g) ⋙ proEtaleIsoPostcompose g ≅ 𝟭 Y.ProEt :=
  (MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale (inv g)) (inferInstance : WeaklyEtale g)).symm ≪≫
    MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y (inv g ≫ g)
      (IsIso.inv_hom_id g)

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem constantCounit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{u + 1}) :
    ((isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).map
        (isoSectionwiseConstantMap.{u, u} g A) ≫ isoSectionwiseConstantMap.{u, u} (inv g) A).hom =
      Functor.whiskerRight (NatTrans.op (integralInverseImageCounitSite g).inv)
        (((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A).obj ⋙
          forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let F := proEtaleIsoPostcompose (inv g)
  let G := proEtaleIsoPostcompose g
  let : (F ⋙ G).IsContinuous (ProEt.topology Y) (ProEt.topology Y) :=
    Functor.isContinuous_comp F G _ (ProEt.topology X) _
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A
  let W := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e := (Functor.sheafPushforwardContinuousId' (integralInverseImageCounitSite g)
    RingCat.{u + 1} (ProEt.topology Y)).app (W.obj R)
  let c := (isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).map
    (isoSectionwiseConstantMap.{u, u} g A) ≫ isoSectionwiseConstantMap.{u, u} (inv g) A
  suffices c = e.hom by exact congrArg (fun f ↦ f.hom) this
  apply (cancel_epi e.inv).1
  rw [e.inv_hom_id]
  let d := e.inv ≫ c
  change d = 𝟙 _
  rw [← W.map_preimage d]
  change W.map (W.preimage d) = W.map (𝟙 R)
  apply congrArg W.map
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology Y) _ _ R.property
  ext U a
  change (W.map (W.preimage d)).hom.app U _ = _
  rw [W.map_preimage]
  have hg := (isoSectionwiseConstantMap_existsUnique.{u, u} g A).exists.choose_spec
  have hi := (isoSectionwiseConstantMap_existsUnique.{u, u} (inv g) A).exists.choose_spec
  have hn := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).naturality
      ((integralInverseImageCounitSite g).hom.app U.unop).op) a
  change c.hom.app U ((W.obj R).obj.map
    ((integralInverseImageCounitSite g).hom.app U.unop).op
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U a)) = _
  change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      (op (G.obj (F.obj U.unop))) a =
    (W.obj R).obj.map ((integralInverseImageCounitSite g).hom.app U.unop).op
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U a) at hn
  rw [← hn]
  exact (congrArg ((isoSectionwiseConstantMap.{u, u} (inv g) A).hom.app U)
    (hg (F.obj U.unop) a)).trans (hi U.unop a)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem completedCoefficientCounit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ((isoSectionwiseInverseImage (inv g) RingCat.{u + 1}).map
        (inverseImageCompletedCoefficientMap l E g) ≫
        inverseImageCompletedCoefficientMap l E (inv g)).hom =
      Functor.whiskerRight (NatTrans.op (integralInverseImageCounitSite g).inv)
        (completedIntegralCoefficientSheafUnrestricted l E Y).obj := by
  let F := proEtaleIsoPostcompose (inv g)
  let G := proEtaleIsoPostcompose g
  let : (F ⋙ G).IsContinuous (ProEt.topology Y) (ProEt.topology Y) :=
    Functor.isContinuous_comp F G _ (ProEt.topology X) _
  let H := isoSectionwiseInverseImage (inv g) RingCat.{u + 1}
  let I := isoSectionwiseInverseImage g RingCat.{u + 1}
  let t := Functor.sheafPushforwardContinuousNatTrans (integralInverseImageCounitSite g).inv
    RingCat.{u + 1} (ProEt.topology Y) (ProEt.topology Y)
  suffices H.map (inverseImageCompletedCoefficientMap l E g) ≫
      inverseImageCompletedCoefficientMap l E (inv g) =
        t.app (completedIntegralCoefficientSheafUnrestricted l E Y) by
    exact congrArg (fun f ↦ f.hom) this
  have hc {S T : Scheme.{u}} (f : S ⟶ T) [IsIso f] (n : ℕ) :
      inverseImageCompletedCoefficientMap l E f ≫
          limit.π (integralCoefficientSheafSystem l E S) (op n) =
        (isoSectionwiseInverseImage f RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E T) (op n)) ≫
            inverseImageFiniteCoefficientMap l E f n := limit.lift_π _ _
  apply limit.hom_ext
  intro n
  rw [Category.assoc, hc (inv g) n.unop, ← Category.assoc, ← H.map_comp,
    hc g n.unop, H.map_comp, Category.assoc]
  have hconst := constantCounit g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))
  have hfin : H.map (inverseImageFiniteCoefficientMap l E g n.unop) ≫
      inverseImageFiniteCoefficientMap l E (inv g) n.unop =
        t.app ((integralCoefficientSheafSystem l E Y).obj n) := by
    apply Sheaf.hom_ext
    exact hconst
  rw [hfin]
  exact t.naturality (limit.π (integralCoefficientSheafSystem l E Y) n)

attribute [local irreducible] inverseImageCompletedCoefficientMap

/-- The inverse-image counit is uniquely specified by reindexing sections. This supplies
only the linearity and naturality needed by the named counit construction below.
Source: Stacks Tag 03D6; lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-completed-inverse-image-scalar-counit).
Proof: the finite constant-coefficient structure maps send each constant to itself.
Their double transport agrees with the displayed identity reindexing. Composing with
each finite projection therefore makes double completed coefficient transport the
identity, by uniqueness of maps to the coefficient limit. The displayed restriction
maps are consequently linear for the transported actions. Restriction along the
inverse site isomorphism supplies their inverses. Sheaf restrictions and module maps
commute with these maps, giving a natural isomorphism. Its values on all sections
uniquely determine each component, and hence the natural isomorphism. -/
theorem integralInverseImageCounit_existsUnique
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! e : inverseImageIntegralModules l E g ⋙ inverseImageIntegralModules l E (inv g) ≅
        𝟭 (integralTowerModules l E Y),
      ∀ (M : integralTowerModules l E Y) (U : Y.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj
          ((proEtaleIsoPostcompose (inv g)).obj U)))),
        (e.hom.app M).val.app (op U) x =
          M.val.map ((integralInverseImageCounitSite g).inv.app U).op x := by
  let F := proEtaleIsoPostcompose (inv g)
  let G := proEtaleIsoPostcompose g
  let : (F ⋙ G).IsContinuous (ProEt.topology Y) (ProEt.topology Y) :=
    Functor.isContinuous_comp F G _ (ProEt.topology X) _
  let H := isoSectionwiseInverseImage (inv g) RingCat.{u + 1}
  let c := inverseImageCompletedCoefficientMap l E g
  let d := inverseImageCompletedCoefficientMap l E (inv g)
  let R := completedIntegralCoefficientSheafUnrestricted l E Y
  let e := (Functor.sheafPushforwardContinuousId' (integralInverseImageCounitSite g)
    RingCat.{u + 1} (ProEt.topology Y)).app R
  have hc : H.map c ≫ d = e.hom := by
    apply Sheaf.hom_ext
    exact completedCoefficientCounit l E g
  have hi : inv d ≫ H.map (inv c) = e.inv := by
    apply (cancel_epi e.hom).1
    have h : (H.map c ≫ d) ≫ (inv d ≫ H.map (inv c)) = 𝟙 _ := by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← H.map_comp,
        IsIso.hom_inv_id, H.map_id]
    rw [hc] at h
    exact h.trans e.hom_inv_id.symm
  let eM : inverseImageIntegralModules l E g ⋙ inverseImageIntegralModules l E (inv g) ≅
      𝟭 (integralTowerModules l E Y) :=
    SheafOfModules.pushforwardComp (F := F) (G := G) (inv d) (inv c) ≪≫
      (SheafOfModules.pushforwardCongr₂
        (J := ProEt.topology Y) (K := ProEt.topology Y) (S := R) (T := R)
        (F := F ⋙ G) (G := 𝟭 Y.ProEt)
        (φ := 𝟙 R) (integralInverseImageCounitSite g)
        (by change 𝟙 R ≫ e.inv = inv d ≫ H.map (inv c)
            simpa only [Category.id_comp] using hi.symm)).symm ≪≫
      SheafOfModules.pushforwardId R
  refine ⟨eM, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext U x
    exact (he' M U.unop x).trans (by rfl)

/-- The actual section-normalized counit, with no choice of an unnormalized equivalence.
Source: Stacks Tag 03D6; lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-completed-inverse-image-scalar-counit). -/
def integralInverseImageCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralModules l E g ⋙ inverseImageIntegralModules l E (inv g) ≅
      𝟭 (integralTowerModules l E Y) :=
  (integralInverseImageCounit_existsUnique l E g).exists.choose

/-- Apply the section-normalized counit termwise and localize it. This is u_F.
Source: Stacks Tags 015F and 04VG; lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-completed-inverse-image-scalar-counit). -/
def integralInverseImageDerivedCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ inverseImageIntegralDerived l E (inv g) ≅
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (inverseImageIntegralModules l E (inv g)) ≪≫
    Functor.mapDerivedCategoryNatIso (integralInverseImageCounit l E g) ≪≫
    Functor.mapDerivedCategoryIdIso (integralTowerModules l E Y)

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralCompletedScalarMap

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryScalarAdjunction (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι W ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W)),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι W M U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι W)
  obtain ⟨a, ha⟩ := h (integralOrdinaryScalar l E L ι W)
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M ((integralOrdinaryScalar l E L ι W).obj M)
    (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl] at h
  rw [Adjunction.homEquiv_id] at h
  exact h
private theorem ordinaryTensorSection_map (W : Scheme.{u})
    {M N : integralTowerModules l E W} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W N U 1 (f.val.app U x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := congrArg (fun k ↦ k.val.app U x) (a.unit.naturality f)
  change ((a.unit.app N).val.app U) (f.val.app U x) =
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_restrict (W : Scheme.{u})
    (M : integralTowerModules l E W) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W M V 1 (M.val.map f x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := PresheafOfModules.naturality_apply (a.unit.app M).val f x
  change (a.unit.app M).val.app V (M.val.map f x) =
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensor_hom_ext_one (W : Scheme.{u})
    (M : integralTowerModules l E W) (N : integralTowerModules l L W)
    (f h : (integralOrdinaryScalar l E L ι W).obj M ⟶ N)
    (he : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (integralOrdinaryTensorSection l E L ι W M U 1 x) =
        h.val.app U (integralOrdinaryTensorSection l E L ι W M U 1 x)) : f = h := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  apply (a.homEquiv M N).injective
  ext U x
  change f.val.app U ((a.unit.app M).val.app U x) =
    h.val.app U ((a.unit.app M).val.app U x)
  rw [ha]
  exact he U x

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarModuleCounit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (M : integralTowerModules l E Y) :
    (isomorphismScalarTensor l E L ι (inv g)).hom.app
        ((inverseImageIntegralModules l E g).obj M) ≫
      (inverseImageIntegralModules l L (inv g)).map
        ((isomorphismScalarTensor l E L ι g).hom.app M) ≫
      (integralInverseImageCounit l L g).hom.app
        ((integralOrdinaryScalar l E L ι Y).obj M) =
      (integralOrdinaryScalar l E L ι Y).map
        ((integralInverseImageCounit l E g).hom.app M) := by
  apply tensor_hom_ext_one l E L ι Y
  intro U x
  have hb (f : X ⟶ Y) [IsIso f] (N : integralTowerModules l E Y)
      (V : X.ProEt) (y : N.val.obj (op ((proEtaleIsoPostcompose f).obj V))) :=
    (isomorphismScalarTensor_existsUnique l E L ι f).exists.choose_spec N V y 1
  have hb' := (isomorphismScalarTensor_existsUnique l E L ι (inv g)).exists.choose_spec
    ((inverseImageIntegralModules l E g).obj M) U.unop x 1
  simp only [map_one] at hb'
  have hb'' := hb g M ((proEtaleIsoPostcompose (inv g)).obj U.unop) x
  simp only [map_one] at hb''
  change ((integralInverseImageCounit l L g).hom.app
      ((integralOrdinaryScalar l E L ι Y).obj M)).val.app U
        (((isomorphismScalarTensor l E L ι g).hom.app M).val.app
          (op ((proEtaleIsoPostcompose (inv g)).obj U.unop))
          (((isomorphismScalarTensor l E L ι (inv g)).hom.app
            ((inverseImageIntegralModules l E g).obj M)).val.app U
            (integralOrdinaryTensorSection l E L ι Y _ U 1 x))) = _
  erw [hb', hb'']
  erw [(integralInverseImageCounit_existsUnique l L g).exists.choose_spec]
  erw [ordinaryTensorSection_restrict, ordinaryTensorSection_map,
    (integralInverseImageCounit_existsUnique l E g).exists.choose_spec]
  rfl

section ExactCounit

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]

private abbrev derivedCounit (G : A ⥤ B) (H : B ⥤ A)
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : G ⋙ H ≅ 𝟭 A) :=
  Functor.mapDerivedCategoryCompIso G H ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A

private theorem derivedCounit_factors (G : A ⥤ B) (H : B ⥤ A)
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : G ⋙ H ≅ 𝟭 A) (X : HomotopyCategory A (.up ℤ)) :
    (derivedCounit G H e).hom.app (DerivedCategory.Qh.obj X) =
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app X) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso G H).inv.app
    (DerivedCategory.Qh.obj X))).1
  simp only [derivedCounit, Iso.trans_hom, NatTrans.comp_app,
    Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryNatIso_fach,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]

private theorem derivedSquare_factors
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ C) (G₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (X : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app
    (DerivedCategory.Qh.obj X))).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedScalarCounit
    (G : A ⥤ B) (H : B ⥤ A) (G' : C ⥤ D) (H' : D ⥤ C)
    (CX : B ⥤ D) (CY : A ⥤ C)
    [G.Additive] [H.Additive] [G'.Additive] [H'.Additive] [CX.Additive] [CY.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits CX] [PreservesFiniteColimits CX]
    [PreservesFiniteLimits CY] [PreservesFiniteColimits CY]
    (u : G ⋙ H ≅ 𝟭 A) (v : G' ⋙ H' ≅ 𝟭 C)
    (b : G ⋙ CX ≅ CY ⋙ G') (c : H ⋙ CY ≅ CX ⋙ H')
    (h : ∀ M : A, c.hom.app (G.obj M) ≫ H'.map (b.hom.app M) ≫
      v.hom.app (CY.obj M) = CY.map (u.hom.app M))
    (K : DerivedCategory A) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (G.mapDerivedCategory.obj K) ≫
      H'.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso b).hom.app K) ≫
      (derivedCounit G' H' v).hom.app (CY.mapDerivedCategory.obj K) =
      CY.mapDerivedCategory.map ((derivedCounit G H u).hom.app K) := by
  let bD := (Functor.mapDerivedCategorySquareIso b).hom
  let cD := (Functor.mapDerivedCategorySquareIso c).hom
  let uD := (derivedCounit G H u).hom
  let vD := (derivedCounit G' H' v).hom
  let α := Functor.whiskerLeft G.mapDerivedCategory cD ≫
    Functor.whiskerRight bD H'.mapDerivedCategory ≫
      Functor.whiskerLeft CY.mapDerivedCategory vD
  let β := Functor.whiskerRight uD CY.mapDerivedCategory
  have he : α = β := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ))
    intro X
    change cD.app (G.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        H'.mapDerivedCategory.map (bD.app (DerivedCategory.Qh.obj X)) ≫
        vD.app (CY.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      CY.mapDerivedCategory.map (uD.app (DerivedCategory.Qh.obj X))
    let GX := (G.mapHomotopyCategory (.up ℤ)).obj X
    let CX' := (CY.mapHomotopyCategory (.up ℤ)).obj X
    let bX := (NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app X
    let cX := (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app GX
    let uX := (NatTrans.mapHomotopyCategory u.hom (.up ℤ)).app X
    let vX := (NatTrans.mapHomotopyCategory v.hom (.up ℤ)).app CX'
    have hh : cX ≫ (H'.mapHomotopyCategory (.up ℤ)).map bX ≫ vX =
        (CY.mapHomotopyCategory (.up ℤ)).map uX := by
      obtain ⟨X⟩ := X
      change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
          (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
          (HomotopyCategory.quotient C (.up ℤ)).map _ =
        (HomotopyCategory.quotient C (.up ℤ)).map _
      simp only [← Functor.map_comp]
      congr 1
      ext n
      exact h (X.X n)
    apply (cancel_mono (CY.mapDerivedCategoryFactorsh.hom.app X)).1
    simp only [Category.assoc]
    have nv := vD.naturality (CY.mapDerivedCategoryFactorsh.hom.app X)
    dsimp only [Functor.comp_map, Functor.id_map] at nv
    erw [← nv]
    dsimp only [vD]
    erw [derivedCounit_factors G' H' v CX']
    rw [← H'.mapDerivedCategory.map_comp_assoc,
      ← H'.mapDerivedCategory.map_comp_assoc]
    have hb := derivedSquare_factors G CX CY G' b X
    change bD.app (DerivedCategory.Qh.obj X) ≫ _ = _ at hb
    have hb' : (bD.app (DerivedCategory.Qh.obj X) ≫
        G'.mapDerivedCategory.map (CY.mapDerivedCategoryFactorsh.hom.app X)) ≫
        G'.mapDerivedCategoryFactorsh.hom.app CX' =
      CX.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app X) ≫
        CX.mapDerivedCategoryFactorsh.hom.app GX ≫ DerivedCategory.Qh.map bX :=
      (Category.assoc _ _ _).trans hb
    erw [hb', H'.mapDerivedCategory.map_comp, H'.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    have nf := H'.mapDerivedCategoryFactorsh.hom.naturality bX
    dsimp only [Functor.comp_map] at nf
    erw [reassoc_of% nf]
    have nc := cD.naturality (G.mapDerivedCategoryFactorsh.hom.app X)
    dsimp only [Functor.comp_map] at nc
    erw [← reassoc_of% nc]
    have hc := derivedSquare_factors H CY CX H' c GX
    change cD.app (DerivedCategory.Qh.obj GX) ≫ _ = _ at hc
    erw [reassoc_of% hc]
    dsimp only [uD]
    erw [derivedCounit_factors G H u X]
    simp only [Functor.map_comp, Category.assoc]
    have nu := CY.mapDerivedCategoryFactorsh.hom.naturality uX
    dsimp only [Functor.comp_map] at nu
    erw [nu]
    simp only [← Functor.map_comp]
    erw [hh]
    rfl
  exact congr_app he K

end ExactCounit

private theorem completionCounit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (G : A ⥤ B) (H : B ⥤ A) (G' : C ⥤ D) (H' : D ⥤ C)
    (CX TX : B ⥤ D) (CY TY : A ⥤ C)
    (χX : CX ⟶ TX) (χY : CY ⟶ TY)
    (u : G ⋙ H ⟶ 𝟭 A) (u' : G' ⋙ H' ⟶ 𝟭 C)
    (b : G ⋙ CX ⟶ CY ⋙ G') (c : H ⋙ CY ⟶ CX ⋙ H')
    (K : A) [IsIso (χX.app (G.obj K))] [IsIso (χY.app (H.obj (G.obj K)))]
    (hc : c.app (G.obj K) ≫ H'.map (b.app K) ≫ u'.app (CY.obj K) =
      CY.map (u.app K)) :
    (inv (χY.app (H.obj (G.obj K))) ≫ c.app (G.obj K) ≫
        H'.map (χX.app (G.obj K))) ≫
      H'.map (inv (χX.app (G.obj K)) ≫ b.app K ≫ G'.map (χY.app K)) ≫
      u'.app (TY.obj K) = TY.map (u.app K) := by
  apply (cancel_epi (χY.app (H.obj (G.obj K)))).1
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← H'.map_comp_assoc, IsIso.hom_inv_id, H'.map_id, Category.id_comp]
  have hn := u'.naturality (χY.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  calc
    _ = (c.app (G.obj K) ≫ H'.map (b.app K) ≫ u'.app (CY.obj K)) ≫ χY.app K := by
      simp only [Category.assoc]
    _ = CY.map (u.app K) ≫ χY.app K := congrArg (fun z ↦ z ≫ χY.app K) hc
    _ = _ := χY.naturality (u.app K)

/-- Ordinary tensor reindexing and its specified completion conjugate preserve the
canonical inverse-image counit, as actual derived arrows, naturally in K.
Source: lem-fix-weil-operations.proof.md, first paragraph, inverse automorphism
squares whose paste is the identity; Stacks Tags 03D6, 03EK, 015F and 04VG
(blueprint: lem-pod-completed-inverse-image-scalar-counit).
Proof:
1. Finite freeness of completed coefficients (lem-weil-finite-free-completed-scalar-
   comparison) and lem-sfb-finite-free-scalar-coordinates express underlying scalar
   extension as a finite sum. Kernels and sheafified cokernels are preserved
   (situation-conventions). Thus scalar extension is exact, as is
   inverse image (lem-weil-proetale-isomorphism-inverse-image). The exact-functor
   derived-factorization and derived-functor nodes compute them termwise on every
   complex, without flatness assumptions on K.
2. Reindex twice. Constants and all finite coefficient projections are fixed, so
   double completed coefficient transport is the identity by its limit property
   (def-weil-proetale-inverse-image, lem-weil-isomorphism-derived-pullback and
   def-weil-completed-integral-coefficients). This is the normalized counit above.
3. On local pure tensors, first apply b for the inverse map, then inverse image of
   b for g, and finally u_L. The result is u_E(x) tensor a. Tensor induction and
   sheafification give equality of sheaf maps (def-pur-sheaf-tensor-product and
   lem-weil-isomorphism-comparison-scalar-extension); sections of the tensor sheaf
   are never assumed to equal the sectionwise tensor product.
4. Apply this equality degreewise. Naturality gives equality of chain maps, and
   lem-weil-pbc-localization-universal-property gives equality of the derived
   transformations. Restrict to the full constructible complete category, using
   lem-weil-isomorphism-derived-pullback. The first equation results.
5. Expand both specified beta maps. Functoriality cancels the adjacent chi_X
   inverse and chi_X. Naturality of u_L at chi_Y moves chi_Y to the left of u_L.
   Substitute the first equation, then naturality of chi_Y at u_E gives the
   second equation. The normalized ordinary-model identification in
   isomorphismScalarModel_existsUnique identifies scalarCompletion with the
   specified completedScalarComparison. Every map is natural on the full
   constructible category, so both equalities are natural in K. -/
theorem completedInverseImage_scalarCounit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    ((isomorphismScalarTensorDerived l E L ι (inv g)).hom.app
        ((inverseImageIntegralDerived l E g).obj K.obj) ≫
      (inverseImageIntegralDerived l L (inv g)).map
        ((isomorphismScalarTensorDerived l E L ι g).hom.app K.obj) ≫
      (integralInverseImageDerivedCounit l L g).hom.app
        ((integralOrdinaryDerivedScalar l E L ι Y).obj K.obj) =
      (integralOrdinaryDerivedScalar l E L ι Y).map
        ((integralInverseImageDerivedCounit l E g).hom.app K.obj)) ∧
    (isomorphismComparisonScalarBeta l E L ι (inv g) hY hX
        ((inverseImageIntegralDerived l E g).obj K.obj)
        (isomorphismComparisonInputs_constructible l E g hX hY K.obj K.property).1 ≫
      (inverseImageIntegralDerived l L (inv g)).map
        (isomorphismComparisonScalarBeta l E L ι g hX hY K.obj K.property) ≫
      (integralInverseImageDerivedCounit l L g).hom.app
        ((integralScalarExtension l E L ι Y).obj K.obj) =
      (integralScalarExtension l E L ι Y).map
        ((integralInverseImageDerivedCounit l E g).hom.app K.obj)) := by
  have hOrd := derivedScalarCounit
    (inverseImageIntegralModules l E g) (inverseImageIntegralModules l E (inv g))
    (inverseImageIntegralModules l L g) (inverseImageIntegralModules l L (inv g))
    (integralOrdinaryScalar l E L ι X) (integralOrdinaryScalar l E L ι Y)
    (integralInverseImageCounit l E g) (integralInverseImageCounit l L g)
    (isomorphismScalarTensor l E L ι g) (isomorphismScalarTensor l E L ι (inv g))
    (scalarModuleCounit l E L ι g) K.obj
  refine ⟨hOrd, ?_⟩
  have hK := (isomorphismComparisonInputs_constructible l E g hX hY K.obj K.property).1
  have hGK := (isomorphismComparisonInputs_constructible l E (inv g) hY hX
    ((inverseImageIntegralDerived l E g).obj K.obj) hK).1
  let : IsIso ((scalarCompletion l E L ι X).app
      ((inverseImageIntegralDerived l E g).obj K.obj)) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _ hK.1
  let : IsIso ((scalarCompletion l E L ι Y).app
      ((inverseImageIntegralDerived l E (inv g)).obj
        ((inverseImageIntegralDerived l E g).obj K.obj))) :=
    (scalarCompletion_existsUnique l E L ι Y).exists.choose_spec.2 _ hGK.1
  have h := completionCounit
    (inverseImageIntegralDerived l E g) (inverseImageIntegralDerived l E (inv g))
    (inverseImageIntegralDerived l L g) (inverseImageIntegralDerived l L (inv g))
    (integralOrdinaryDerivedScalar l E L ι X) (integralScalarExtension l E L ι X)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralScalarExtension l E L ι Y)
    (scalarCompletion l E L ι X) (scalarCompletion l E L ι Y)
    (integralInverseImageDerivedCounit l E g).hom
    (integralInverseImageDerivedCounit l L g).hom
    (isomorphismScalarTensorDerived l E L ι g).hom
    (isomorphismScalarTensorDerived l E L ι (inv g)).hom K.obj hOrd
  simpa only [isomorphismComparisonScalarBeta, scalarCompletionIso, asIso_inv,
    Category.assoc] using h

end WeilConjectures
