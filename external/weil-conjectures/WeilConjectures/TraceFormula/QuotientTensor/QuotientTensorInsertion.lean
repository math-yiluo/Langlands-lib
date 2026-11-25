/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Tensor insertion across quotient coefficient systems

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3);
Stacks Tags 03EK and 03CY (blueprint: lem-trf-quotient-tensor-insertion).

The index n denotes positive exponent n+1. Source, target and transition maps are
unbounded complexes of sheaves, before localization. Site and coefficient sizes
are independent. Tensor sections below use the published sheafified tensor unit,
not an identification of sections of a sheaf tensor with tensors of sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe t u d v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.QuotientTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- G after restriction by the completed projection, with action through c_R inverse.
Source: blueprint clause (3) (blueprint: lem-trf-quotient-tensor-insertion). -/
def source (n : ℕ) :
    CochainComplex (integralOperationsFiniteModules l E Y n) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  integralOperationsRestrict l E Y n ⋙
    (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- The specified finite sheafified pullback, restricted by pi_X,n.
Source: Stacks 03EK, blueprint clause (3)
(blueprint: lem-trf-quotient-tensor-insertion). -/
def target (n : ℕ) :
    CochainComplex (integralOperationsFiniteModules l E Y n) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  (integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ) ⋙
    integralOperationsRestrict l E X n

/-- The actual section x tensor b: scalar multiplication of the published tensor-unit
generator, restricted along the canonical inverse-image comma arrow.
Source: Stacks 03EK; def-weil-inverse-image-pullback-comparison (a)
(blueprint: lem-trf-quotient-tensor-insertion). -/
def tensorSection (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt)
    (b : (integralCoefficientSheaf l E X n).obj.obj (op U))
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.obj (op U)) :=
  b • (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.map
    (proEtaleIsoCommaArrow g U).op
      (integralOperationsPullbackGenerator l E g n (K.X i)
        ((proEtaleIsoPostcompose g).obj U) x))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem coefficientTransport_cocontinuous :
    (proEtaleIsoPostcompose g).IsCocontinuous (ProEt.topology X) (ProEt.topology Y) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let e' : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
    (proEtaleIsoPostcompose g) (proEtaleIsoPostcompose (inv g))
    e.2.1.some.symm e.2.2.1.some
  exact (e'.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some

private def coefficientTransportIso (A : CommRingCat.{max u (t + 1)}) :
    (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ≅
      (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A := by
  have := coefficientTransport_cocontinuous g
  exact ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Y)).symm.app
      ((Functor.const Y.ProEtᵒᵖ).obj A)

private theorem coefficientTransport_eq (A : CommRingCat.{max u (t + 1)}) :
    isoSectionwiseConstantMap g A =
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (coefficientTransportIso g A).hom := by
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  · intro U a
    have := coefficientTransport_cocontinuous g
    have hn : (proEtaleIsoPostcompose g).op.whiskerLeft
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) ≫
        (coefficientTransportIso g A).hom.hom =
      toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) := by
      let i := (sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).mapIso
        (coefficientTransportIso g A).symm
      change _ ≫ i.inv = _
      apply (i.comp_inv_eq).2
      exact ((proEtaleIsoPostcompose g).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj A)).symm
    exact congrArg (fun f ↦ (f.app (op U)) a) hn

private theorem coefficientTransport_naturality {A B : CommRingCat.{max u (t + 1)}}
    (f : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f)) ≫
        isoSectionwiseConstantMap g B =
      isoSectionwiseConstantMap g A ≫
        (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f) := by
  rw [coefficientTransport_eq g A, coefficientTransport_eq g B]
  have := coefficientTransport_cocontinuous g
  exact congrArg
    ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
    ((((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Y)).symm.hom.naturality
        ((Functor.const Y.ProEtᵒᵖ).map f)))

private def quotientSheafAdjunction (D : Type d) [Category.{v} D] :
    isoSectionwiseInverseImage g D ⊣
      (proEtaleBaseChange g).sheafPushforwardContinuous D (ProEt.topology Y)
        (ProEt.topology X) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial).sheafPushforwardContinuous _ _

private theorem coefficientTransport_mate (A : CommRingCat.{max u (t + 1)}) :
    isoSectionwiseConstantMap g A =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
              (coefficientProEtaleDirectRingMap g A)) ≫
        (quotientSheafAdjunction g RingCat.{max u (t + 1)}).counit.app
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
              ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)) := by
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  · intro U a
    let ηX := toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)
    let ηY := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)
    have hρ : ηY ≫ (coefficientProEtaleDirectRingMap g A).hom =
        (proEtaleBaseChange g).op.whiskerLeft ηX :=
      ((sheafificationAdjunction (ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).homEquiv _ _).apply_symm_apply _
    change (((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        (proEtaleIsoCommaArrow g U).op)
        ((coefficientProEtaleDirectRingMap g A).hom.app
          (op ((proEtaleIsoPostcompose g).obj U))
          (ηY.app (op ((proEtaleIsoPostcompose g).obj U)) a)) = ηX.app (op U) a
    have hρ' := congrArg (fun f ↦ f.app (op ((proEtaleIsoPostcompose g).obj U)) a) hρ
    change (coefficientProEtaleDirectRingMap g A).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        (ηY.app (op ((proEtaleIsoPostcompose g).obj U)) a) = _ at hρ'
    rw [hρ']
    exact (congrArg (fun f ↦ f a) (ηX.naturality (proEtaleIsoCommaArrow g U).op)).symm

private def siteEquiv : Y.ProEt ≌ X.ProEt := by
  let : (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let := adj.isEquivalence_right_of_isEquivalence_left
  exact adj.toEquivalence.symm

private theorem finiteDirectImage_equivalence (n : ℕ) :
    (coefficientProEtaleModuleDirectImage g
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        ).IsEquivalence := by
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let ρ : integralCoefficientSheaf l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat
        (ProEt.topology Y) (ProEt.topology X)).obj (integralCoefficientSheaf l E X n) :=
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (coefficientProEtaleDirectRingMap g A)
  let G := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  let : G.IsEquivalence := (isoSectionwiseInverseImage_equivalence.{t, _, _, 0, 0} g _).1
  let a := quotientSheafAdjunction g RingCat.{max u (t + 1)}
  have : IsIso (G.map ρ ≫ a.counit.app (integralCoefficientSheaf l E X n)) := by
    have he : G.map ρ ≫ a.counit.app (integralCoefficientSheaf l E X n) =
        isoSectionwiseConstantMap g A := (coefficientTransport_mate g A).symm
    rw [he]
    infer_instance
  have : IsIso (G.map ρ) := IsIso.of_isIso_comp_right (G.map ρ)
    (a.counit.app (integralCoefficientSheaf l E X n))
  have : IsIso ρ := isIso_of_reflects_iso ρ G
  let e := siteEquiv g
  have : e.functor.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleBaseChange_isContinuous g
  have : e.inverse.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  let shAdj := e.toAdjunction.sheafPushforwardContinuous (E := RingCat.{max u (t + 1)})
    (ProEt.topology Y) (ProEt.topology X)
  let ψ : integralCoefficientSheaf l E X n ⟶
      (e.inverse.sheafPushforwardContinuous RingCat _ _).obj
        (integralCoefficientSheaf l E Y n) :=
    shAdj.unit.app _ ≫ (e.inverse.sheafPushforwardContinuous _ _ _).map (inv ρ)
  have H₁ : Functor.whiskerRight (NatTrans.op e.counit)
      (integralCoefficientSheaf l E X n).obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft ρ.hom := by
    ext U : 2
    simp [ψ, shAdj]
    rfl
  have H₂ : ρ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit)
        (integralCoefficientSheaf l E Y n).obj = 𝟙 _ := by
    have hh : ρ ≫ (e.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app _ = 𝟙 _ := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality (inv ρ)]
      have ht := shAdj.left_triangle_components (integralCoefficientSheaf l E X n)
      calc
        _ = ρ ≫ ((e.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app _) ≫ shAdj.counit.app
              ((e.functor.sheafPushforwardContinuous RingCat _ _).obj
                (integralCoefficientSheaf l E X n))) ≫ inv ρ := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = ρ ≫ 𝟙 _ ≫ inv ρ := congrArg (fun h ↦ ρ ≫ h ≫ inv ρ) ht
        _ = _ := by simp
    exact congrArg (fun h ↦ h.hom) hh
  exact (SheafOfModules.pushforwardPushforwardEquivalence e ρ ψ H₁ H₂).isEquivalence_functor

private theorem tensorUnit_bijective (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt) :
    Function.Bijective (tensorSection l E g n K i U 1) := by
  let := finiteDirectImage_equivalence l E g n
  let : (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  have : IsIso (proEtaleIsoCommaArrow g U) :=
    inferInstanceAs (IsIso (adj.unit.app U))
  let a := coefficientProEtaleModuleAdjunction g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let η := a.unit.app (K.X i)
  have hu := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op ((proEtaleIsoPostcompose g).obj U))).map η)
  have hr := ConcreteCategory.bijective_of_isIso
    (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.presheaf.map
      (proEtaleIsoCommaArrow g U).op)
  have h : tensorSection l E g n K i U 1 =
      (fun y ↦ ((integralOperationsLevelPullback l E g n).obj (K.X i)).val.map
        (proEtaleIsoCommaArrow g U).op y) ∘
      (fun x ↦ η.val.app (op ((proEtaleIsoPostcompose g).obj U)) x) := by
    funext x
    exact one_smul _ _
  rw [h]
  exact hr.comp hu

/-- Insertion x to x tensor 1 is a unique completed-linear chain map.
Source: Stacks 03EK and 03CY, blueprint clause (3)
(blueprint: lem-trf-quotient-tensor-insertion).
Proof: on the sectionwise tensor presheaf insert 1 and then apply sheafification.
Restrictions preserve 1. The structure square c_n G(pi_Y,n) c_R inverse = pi_X,n
and balancing give j(ax)=a j(x). The differential acts on x alone, so insertion
commutes with it. The published finite comparison has precisely this section formula;
the completed action square makes it a map with the displayed endpoints. Equality
on every section in every degree proves uniqueness. These are split steps 1 and 2. -/
theorem insertion_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    ∃! j : (source l E g n).obj K ⟶ (target l E g n).obj K,
      ∀ (i : ℤ) (U : X.ProEt)
        (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (j.f i).val.app (op U) x = tensorSection l E g n K i U 1 x := by
  let f := (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose
  have hf := (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose_spec
  let j : (source l E g n).obj K ⟶ (target l E g n).obj K :=
    { f := fun i ↦ ⟨PresheafOfModules.homMk
        ((SheafOfModules.toSheaf (integralCoefficientSheaf l E X n)).map (f.f i)).hom
        (by
          intro U a x
          let V := op ((proEtaleIsoPostcompose g).obj U.unop)
          let r := (inv (inverseImageCompletedCoefficientMap l E g)).hom.app U a
          let b := (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U a
          have hπ : inverseImageCompletedCoefficientMap l E g ≫
              limit.π (integralCoefficientSheafSystem l E X) (op n) =
            (isoSectionwiseInverseImage g RingCat).map
              (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
                inverseImageFiniteCoefficientMap l E g n := by
            simp only [inverseImageCompletedCoefficientMap, limit.lift_π,
              inverseImageCompletedCoefficientComponent]
          have hc := congrArg (fun k ↦ k.hom.app U r) hπ
          have hi := congrArg (fun k ↦ k.hom.app U a)
            (IsIso.inv_hom_id (inverseImageCompletedCoefficientMap l E g))
          change (inverseImageCompletedCoefficientMap l E g).hom.app U r = a at hi
          change (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U
              ((inverseImageCompletedCoefficientMap l E g).hom.app U r) =
            (inverseImageFiniteCoefficientMap l E g n).hom.app U
              ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app V r) at hc
          rw [hi] at hc
          have hfin := congrArg (fun k ↦ k.hom.app U
              ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app V r))
            (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l E g n))
          have hs : (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app V r =
              (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U b :=
            hfin.symm.trans (congrArg
              ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U) hc.symm)
          change (f.f i).val.app U
              ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app V r •
                (show (K.X i).val.obj V from x)) =
            b • (f.f i).val.app U x
          rw [hs]
          exact ((f.f i).val.app U).hom.map_smul b x)⟩
      comm' := by
        intro i k hik
        ext U x
        exact congrArg (fun h ↦ h.val.app U x) (f.comm i k) }
  refine ⟨j, ?_, ?_⟩
  · intro i U x
    change (f.f i).val.app (op U) x = _
    simpa only [tensorSection, one_smul, f]
      using hf i U x
  · intro j' hj'
    ext i U x
    calc
      _ = tensorSection l E g n K i U.unop 1 x := hj' i U.unop x
      _ = _ := by
        change _ = (f.f i).val.app U x
        symm
        simpa only [tensorSection, one_smul, f]
          using hf i U.unop x

/-- The insertion is chosen only from its unique actual sheafified section formula.
Source: Stacks 03EK and 03CY (blueprint: lem-trf-quotient-tensor-insertion). -/
def insertion (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    (source l E g n).obj K ⟶ (target l E g n).obj K :=
  (insertion_existsUnique l E g n K).exists.choose

private theorem insertion_apply (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt)
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((insertion l E g n K).f i).val.app (op U) x =
      tensorSection l E g n K i U 1 x :=
  (insertion_existsUnique l E g n K).exists.choose_spec i U x

private theorem insertion_isIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    IsIso (insertion l E g n K) := by
  have (i : ℤ) : IsIso ((insertion l E g n K).f i) := by
    let h := (insertion l E g n K).f i
    have (U : X.ProEtᵒᵖ) : IsIso (h.val.app U) := by
      obtain ⟨U⟩ := U
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (fun x ↦ ((insertion l E g n K).f i).val.app (op U) x)
      simpa only [insertion_apply] using tensorUnit_bijective l E g n K i U
    let e := PresheafOfModules.isoMk (fun U ↦ asIso (h.val.app U))
      (by intro U V f; exact h.val.naturality f)
    let e' : ((source l E g n).obj K).X i ≅ ((target l E g n).obj K).X i :=
      (SheafOfModules.fullyFaithfulForget _).preimageIso e
    exact e'.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

attribute [local instance] insertion_isIso

private theorem tensorSection_smul (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt)
    (b : (integralCoefficientSheaf l E X n).obj.obj (op U))
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    tensorSection l E g n K i U b x =
      tensorSection l E g n K i U 1
        ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) b • x) := by
  let f := (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose
  have hf (y : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
      (f.f i).val.app (op U) y = tensorSection l E g n K i U 1 y := by
    simpa only [tensorSection, one_smul, f] using
      (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose_spec i U y
  calc
    _ = b • (f.f i).val.app (op U) x := by rw [hf]; simp only [tensorSection, one_smul]
    _ = (f.f i).val.app (op U)
        ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) b • x) :=
      (((f.f i).val.app (op U)).hom.map_smul b x).symm
    _ = _ := hf _

private theorem insertion_naturality (n : ℕ)
    {K L : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ} (f : K ⟶ L) :
    (source l E g n).map f ≫ insertion l E g n L =
      insertion l E g n K ≫ (target l E g n).map f := by
  ext i U x
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let adj := coefficientProEtaleModuleAdjunction g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have hu := congrArg (fun k ↦ k.val.app (op V) x) (adj.unit.naturality (f.f i))
  have hr := congrArg (fun k ↦ k (integralOperationsPullbackGenerator l E g n
      (K.X i) V x))
    (((integralOperationsLevelPullback l E g n).map (f.f i)).val.naturality
      (proEtaleIsoCommaArrow g U.unop).op)
  change ((insertion l E g n L).f i).val.app U ((f.f i).val.app _ x) =
    (((integralOperationsLevelPullback l E g n).map (f.f i)).val.app U)
      (((insertion l E g n K).f i).val.app U x)
  rw [insertion_apply, insertion_apply]
  simp only [tensorSection, one_smul]
  exact (congrArg
    (((integralOperationsLevelPullback l E g n).obj (L.X i)).val.map
      (proEtaleIsoCommaArrow g U.unop).op) hu).trans hr.symm

private theorem insertion_inverse_apply (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (i : ℤ) (U : X.ProEt)
    (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((inv (insertion l E g n K)).f i).val.app (op U)
      (tensorSection l E g n K i U 1 x) = x := by
  have h := congrArg (fun k ↦ (k.f i).val.app (op U) x)
    (IsIso.hom_inv_id (insertion l E g n K))
  change ((inv (insertion l E g n K)).f i).val.app (op U)
    (((insertion l E g n K).f i).val.app (op U) x) = x at h
  rwa [insertion_apply] at h

private theorem coefficientInverse_reduction (n : ℕ) (U : X.ProEt)
    (b : (integralCoefficientSheaf l E X (n + 1)).obj.obj (op U)) :
    (integralCoefficientSheafTransition l E Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        ((inv (inverseImageFiniteCoefficientMap l E g (n + 1))).hom.app (op U) b) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U)
        ((integralCoefficientSheafTransition l E X n).hom.app (op U) b) := by
  let r := (inv (inverseImageFiniteCoefficientMap l E g (n + 1))).hom.app (op U) b
  have h := coefficientTransport_naturality g (CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))
  have hc := congrArg (fun k ↦ k.hom.app (op U) r) h
  have hi := congrArg (fun k ↦ k.hom.app (op U) b)
    (IsIso.inv_hom_id (inverseImageFiniteCoefficientMap l E g (n + 1)))
  change (inverseImageFiniteCoefficientMap l E g (n + 1)).hom.app (op U) r = b at hi
  change (inverseImageFiniteCoefficientMap l E g n).hom.app (op U)
      ((integralCoefficientSheafTransition l E Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) r) =
    (integralCoefficientSheafTransition l E X n).hom.app (op U)
      ((inverseImageFiniteCoefficientMap l E g (n + 1)).hom.app (op U) r) at hc
  rw [hi] at hc
  have hfin := congrArg (fun k ↦ k.hom.app (op U)
      ((integralCoefficientSheafTransition l E Y n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U)) r))
    (IsIso.hom_inv_id (inverseImageFiniteCoefficientMap l E g n))
  exact hfin.symm.trans
    (congrArg ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U)) hc)

/-- Quotient semilinearity of a chain map, written on every sheaf section.
The completed-linear map is just the same map after restriction by the limit projections.
Source: blueprint clause (3) (blueprint: lem-trf-quotient-tensor-insertion). -/
def IsReductionLinear (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y (n + 1)) ℤ)
    (L : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (w : (integralOperationsRestrict l E Y (n + 1)).obj K ⟶
      (integralOperationsRestrict l E Y n).obj L) : Prop :=
  ∀ (i : ℤ) (U : Y.ProEt)
    (a : (integralCoefficientSheaf l E Y (n + 1)).obj.obj (op U))
    (x : (K.X i).val.obj (op U)),
    (w.f i).val.app (op U) (a • x) =
      @SMul.smul _ ((L.X i).val.obj (op U)) inferInstance
        ((integralCoefficientSheafTransition l E Y n).hom.app (op U) a)
        ((w.f i).val.app (op U) x)

/-- The actual cross-coefficient tensor map exists uniquely as a completed-linear chain map.
Source: Stacks 03EK and 03CY, blueprint clause (3)
(blueprint: lem-trf-quotient-tensor-insertion).
Proof: put B_n=G S_Y,n, T_n=S_X,n, q_n=G rho_Y,n and p_n=rho_X,n.
Coefficient naturality gives p_n c_(n+1)=c_n q_n. Hence semilinearity of w gives
w(bx) tensor p(t)=w(x) tensor c_n(q(b))p(t)=w(x) tensor p(c_(n+1)(b)t).
The formula is balanced and commutes with restrictions. The limit projection identity
p_n pi_(n+1)=pi_n makes it completed-linear. Apply the module sheafification
interface with base ring R_X to obtain its unique extension. The differential
commutes on pure tensors since w is a chain map, and hence after sheafification.
These are split steps 1, 3 and 4; no exactness of tensor is used. -/
theorem transition_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y (n + 1)) ℤ)
    (L : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (w : (integralOperationsRestrict l E Y (n + 1)).obj K ⟶
      (integralOperationsRestrict l E Y n).obj L)
    (_hw : IsReductionLinear l E n K L w) :
    ∃! v : (target l E g (n + 1)).obj K ⟶ (target l E g n).obj L,
      ∀ (i : ℤ) (U : X.ProEt)
        (b : (integralCoefficientSheaf l E X (n + 1)).obj.obj (op U))
        (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (v.f i).val.app (op U) (tensorSection l E g (n + 1) K i U b x) =
          tensorSection l E g n L i U
            ((integralCoefficientSheafTransition l E X n).hom.app (op U) b)
            ((w.f i).val.app (op ((proEtaleIsoPostcompose g).obj U)) x) := by
  let G := (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)
  let v := inv (insertion l E g (n + 1) K) ≫ G.map w ≫ insertion l E g n L
  have hv : ∀ (i : ℤ) (U : X.ProEt)
      (b : (integralCoefficientSheaf l E X (n + 1)).obj.obj (op U))
      (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (v.f i).val.app (op U) (tensorSection l E g (n + 1) K i U b x) =
        tensorSection l E g n L i U
          ((integralCoefficientSheafTransition l E X n).hom.app (op U) b)
          ((w.f i).val.app (op ((proEtaleIsoPostcompose g).obj U)) x) := by
    intro i U b x
    calc
      _ = tensorSection l E g n L i U 1
          ((w.f i).val.app (op ((proEtaleIsoPostcompose g).obj U))
            ((inv (inverseImageFiniteCoefficientMap l E g (n + 1))).hom.app (op U) b •
              x)) := by
        change ((insertion l E g n L).f i).val.app (op U)
          ((w.f i).val.app _ (((inv (insertion l E g (n + 1) K)).f i).val.app (op U)
            (tensorSection l E g (n + 1) K i U b x))) = _
        rw [tensorSection_smul, insertion_inverse_apply, insertion_apply]
        rfl
      _ = tensorSection l E g n L i U 1
          ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U)
            ((integralCoefficientSheafTransition l E X n).hom.app (op U) b) •
              (show (L.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U)) from
                (w.f i).val.app (op ((proEtaleIsoPostcompose g).obj U)) x)) := by
        rw [_hw i _ _ _, coefficientInverse_reduction]
        rfl
      _ = _ := (tensorSection_smul l E g n L i U _ _).symm
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  apply (cancel_epi (insertion l E g (n + 1) K)).1
  ext i U x
  change (v'.f i).val.app U (((insertion l E g (n + 1) K).f i).val.app U x) =
    (v.f i).val.app U (((insertion l E g (n + 1) K).f i).val.app U x)
  rw [insertion_apply]
  calc
    _ = tensorSection l E g n L i U.unop 1 ((w.f i).val.app _ x) := by
      simpa only [map_one] using hv' i U.unop 1 x
    _ = _ := by
      symm
      simpa only [map_one] using hv i U.unop 1 x

/-- The unique sheafified map x tensor b to G(w)(x) tensor rho_X,n(b).
Source: Stacks 03EK and 03CY (blueprint: lem-trf-quotient-tensor-insertion). -/
def transition (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y (n + 1)) ℤ)
    (L : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (w : (integralOperationsRestrict l E Y (n + 1)).obj K ⟶
      (integralOperationsRestrict l E Y n).obj L)
    (hw : IsReductionLinear l E n K L w) :
    (target l E g (n + 1)).obj K ⟶ (target l E g n).obj L :=
  (transition_existsUnique l E g n K L w hw).exists.choose

/-- The specified augmentation theta_n=j_n G(r_n), retaining completed scalar linearity.
Source: blueprint clause (3), augmentation in strict-quotient step 4
(blueprint: lem-trf-quotient-tensor-insertion). -/
def augmentation (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ)
    (r : P ⟶ (integralOperationsRestrict l E Y n).obj K) :
    ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (target l E g n).obj K :=
  ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map r ≫
    insertion l E g n K

end WeilConjectures.QuotientTensor
