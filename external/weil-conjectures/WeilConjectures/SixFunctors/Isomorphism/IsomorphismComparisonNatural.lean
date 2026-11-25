/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Naturality of the specified inverse-image comparison

Source: Deligne, Weil II, (1.1.3), p. 150 and (1.1.7), pp. 150--151;
the explicit pro-etale/completed argument is agent-written, extracted from
`lem-weil-frobenius-point-transport-natural`, steps 3--6 and 9
(blueprint: lem-weil-isomorphism-comparison-natural).

The finite comparison is fixed on every complex by the recorded tensor-unit map.
The integral comparison is the recorded chosen-resolution map, on every ambient
object, and agrees with the actual completion unit through the normalization
isomorphism. Both natural transformations can be postcomposed with any functor
and preceded by any natural transformation. The finite index `n` means exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u r s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ZeroObject
open AlgebraicGeometry.Scheme
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard

private theorem reduction_generator_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t}) (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N)
    (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
    ((unrestrictedIntegralReductionFunctor l E Y n).map a).val.app V
        (unrestrictedIntegralTensorSection l E Y n M V 1 x) =
      unrestrictedIntegralTensorSection l E Y n N V 1 (a.val.app V x) := by
  have h : eqToHom (unrestrictedReduction_obj l E Y n M).symm ≫
      (unrestrictedIntegralReductionFunctor l E Y n).map a =
      SheafOfModules.changeOfRingsHom (completedIntegralCommRingProjectionUnrestricted l E Y n)
        M a ≫ eqToHom (unrestrictedReduction_obj l E Y n N).symm := by
    rw [unrestrictedReduction_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  calc
    _ = (eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V
        ((SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M a).val.app V
          (SheafOfModules.UnrestrictedTowerProof.tensorSection
            (completedIntegralCommRingProjectionUnrestricted l E Y n) M V 1 x)) :=
      congrArg (fun k ↦ k.val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M V 1 x)) h
    _ = _ := congrArg ((eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V)
      (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M a V 1 x)

private theorem reduction_theta_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    {K L : CochainComplex (integralTowerModules l E Y) ℤ} (f : K ⟶ L) :
    ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map f ≫
        inverseImageReductionTheta l E g n L =
      inverseImageReductionTheta l E g n K ≫
        (integralOperationsPullbackLevel l E g n).map f := by
  have hv (K : CochainComplex (integralTowerModules l E Y) ℤ) :=
    (inverseImageReductionTheta_existsUnique l E g n K).exists.choose_spec
  ext i U x
  change ((inverseImageReductionTheta l E g n L).f i).val.app U
      ((f.f i).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x) =
    (((integralOperationsLevelPullback l E g n).map
      ((unrestrictedIntegralReductionFunctor l E Y n).map (f.f i))).val.app U)
      (((inverseImageReductionTheta l E g n K).f i).val.app U x)
  dsimp only [inverseImageReductionTheta]
  erw [hv L i U.unop, hv K i U.unop]
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let a := (unrestrictedIntegralReductionFunctor l E Y n).map (f.f i)
  let A := coefficientProEtaleModuleAdjunction g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let z := unrestrictedIntegralTensorSection l E Y n (K.X i) (op V) 1 x
  have hu := congrArg (fun k ↦ k.val.app (op V) z) (A.unit.naturality a)
  have hr := congrArg (fun k ↦ k
      (integralOperationsPullbackGenerator l E g n
        ((unrestrictedIntegralReductionFunctor l E Y n).obj (K.X i)) V z))
    (((integralOperationsLevelPullback l E g n).map a).val.naturality
      (proEtaleIsoCommaArrow g U.unop).op)
  rw [← reduction_generator_map l E Y n (f.f i) (op V) x]
  exact (congrArg
    (((integralOperationsLevelPullback l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj (L.X i))).val.map
      (proEtaleIsoCommaArrow g U.unop).op) hu).trans hr.symm

private theorem zero_lift_f
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (α : M ⟶ K)
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0) (i : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 h).f i = α.f i ≫
      HomologicalComplex.homotopyCofiber.inlX φ i (i + (-1))
        (by change i + (-1) + 1 = i; omega) := by
  simp only [CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ i _ _ (i + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  erw [Category.comp_id]

private theorem zero_lift_naturality
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M N : CochainComplex A ℤ} (φ : K ⟶ K) (ψ : L ⟶ L)
    (a : K ⟶ L) (ha : φ ≫ a = a ≫ ψ) (f : M ⟶ N) (α : M ⟶ K) (β : N ⟶ L)
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M K (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0)
    (hβ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain N L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (β ≫ ψ) = 0)
    (hn : f ≫ β = α ≫ a) :
    f ≫ CochainComplex.mappingCocone.lift ψ β 0 hβ =
      CochainComplex.mappingCocone.lift φ α 0 hα ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom φ ψ
            (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
            (Arrow.homMk a a ha.symm)) := by
  ext i : 1
  dsimp only [HomologicalComplex.comp_f]
  rw [zero_lift_f, zero_lift_f, CochainComplex.shiftFunctor_map_f']
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  simpa only [HomologicalComplex.comp_f, Category.assoc, Arrow.homMk_left] using
    congrArg (fun k ↦ k.f i ≫ HomologicalComplex.homotopyCofiber.inlX ψ
      i (i + (-1)) (by change i + (-1) + 1 = i; omega)) hn

private def roos_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E g where
  app := inverseImageRoosComparisonComplex l E g
  naturality K L f := by
    have hn : ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map f ≫
        inverseImageReductionProduct l E g L =
      inverseImageReductionProduct l E g K ≫
        Limits.Pi.map (fun n ↦ (integralOperationsPullbackLevel l E g n).map f) := by
      apply Limits.Pi.hom_ext
      intro n
      simp only [Category.assoc, Limits.Pi.map_π, inverseImageReductionProduct,
        Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
      exact reduction_theta_natural l E g n f
    exact zero_lift_naturality _ _ _ (integralOperationsRoos_square
      ((integralOperationsPullbackTowerFunctor l E g).map f)) _ _ _ _ _ hn

private theorem integral_comparison_descent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ κ : inverseImageIntegralDerived l E g ⟶ integralDerivedPullback l E g,
      ∀ (K : CochainComplex (integralTowerModules l E Y) ℤ)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q],
        κ.app (DerivedCategory.Q.obj K) =
          inverseImagePullbackComparison l E g hX hY K P q := by
  let J := (integralOperationsGoodComplex l E Y).ι
  let L := integralOperationsGoodLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage J
  let : L.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E Y
  let F := inverseImageIntegralModules l E g
  let ff := Localization.fullyFaithfulWhiskeringLeft L V
    (DerivedCategory (integralTowerModules l E X))
  let σ : L ⋙ inverseImageIntegralDerived l E g ⟶ L ⋙ integralDerivedPullback l E g :=
    whiskerLeft J F.mapDerivedCategoryFactors.hom ≫
      whiskerLeft J (whiskerRight (roos_comparison l E g) DerivedCategory.Q) ≫
        (integralDerivedPullbackComparison l E g).inv
  let κ := ff.preimage σ
  have hk (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      κ.app (DerivedCategory.Q.obj P.obj) =
        F.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
            (integralDerivedPullbackComparison l E g).inv.app P :=
    by simpa only [κ, σ, whiskeringLeft_obj_map, whiskerLeft_app, NatTrans.comp_app,
      whiskerRight_app, roos_comparison, J, L, integralOperationsGoodLocalization,
      ObjectProperty.ι_obj, Functor.comp_obj] using congr_app (ff.map_preimage σ) P
  refine ⟨κ, ?_⟩
  intro K P q hq
  apply (cancel_epi ((inverseImageIntegralDerived l E g).map (DerivedCategory.Q.map q))).1
  rw [κ.naturality, hk]
  unfold inverseImagePullbackComparison
  have hn := F.mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  erw [IsIso.hom_inv_id_assoc]

private theorem integral_comparison_representative
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (κ : inverseImageIntegralDerived l E g ⟶ integralDerivedPullback l E g)
    (hk : ∀ (K : CochainComplex (integralTowerModules l E Y) ℤ)
      (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q], κ.app (DerivedCategory.Q.obj K) =
        inverseImagePullbackComparison l E g hX hY K P q)
    (N : DerivedCategory (integralTowerModules l E Y)) :
    κ.app N = inverseImagePullbackComparisonDerived l E g hX hY N := by
  unfold inverseImagePullbackComparisonDerived
  dsimp only
  rw [← hk]
  rw [← κ.naturality]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [(inverseImageIntegralDerived l E g).map_id, Category.id_comp]

private theorem complete_zero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t}) :
    IsDerivedCompleteUnrestricted l E Y
      (DerivedCategory.Q.obj
        (HomologicalComplex.zero : CochainComplex (integralTowerModules l E Y) ℤ)) := by
  let : Zero (DerivedCategory (integralTowerModules l E Y)) := HasZeroObject.zero' _
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  have hf : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := R) HomologicalComplex.zero := by
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    intro F _
    apply HomologicalComplex.acyclic_of_isZero
    apply (IsZero.iff_id_eq_zero _).2
    ext j : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h
    exact (Functor.map_isZero ((MonoidalCategory.curriedTensor _).obj (F.X a))
      (isZero_zero _)).eq_of_src _ _
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1
      cardinality_eq := (pow_one p).symm, k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  refine ⟨D, hl, ?_⟩
  unfold IsDerivedComplete
  refine ⟨HomologicalComplex.zero, HomologicalComplex.zero, 𝟙 _,
    ⟨inferInstance, hf⟩, Iso.refl _, ?_⟩
  let F := integralReductionTower l E Y D hl HomologicalComplex.zero
  have hz (n : ℕ) : IsZero (F.obj (op n)) :=
    Functor.map_isZero DerivedCategory.Q
      (Functor.map_isZero ((scalarReductionRestriction l E Y n).mapHomologicalComplex _)
        (Functor.map_isZero ((scalarReductionExtension l E Y n).mapHomologicalComplex _)
          HomologicalComplex.isZero_zero))
  let : HasProduct (fun n : ℕ ↦ F.obj (op n)) :=
    HasLimit.mk ⟨Cone.mk 0 0, IsLimit.ofIsZero _
      ((Discrete.functor (fun n : ℕ ↦ F.obj (op n))).isZero (fun n ↦ hz n.as))
      (isZero_zero _)⟩
  have hprod : IsZero (∏ᶜ fun n : ℕ ↦ F.obj (op n)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Pi.hom_ext
    intro n
    exact (hz n).eq_of_tgt _ _
  refine ⟨inferInstance, 0, ?_⟩
  apply (Pretriangulated.Triangle.distinguished_iff_of_isZero₃ _ hprod).2
  refine ⟨⟨0, ?_, ?_⟩⟩
  · exact (Functor.map_isZero DerivedCategory.Q
      (HomologicalComplex.isZero_zero (V := integralTowerModules l E Y))).eq_of_src _ _
  · exact hprod.eq_of_src _ _

/-- The specified ambient integral components are natural, independent of the
chosen flat-term K-flat resolutions, and are the inverse normalization followed
by inverse image of the actual completion unit. They remain natural after the
stated composition, including on incomplete objects.
Source: Deligne, Weil II, (1.1.3), (1.1.7), as motivation; blueprint
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
clauses (2)--(3), through the agent-written entire-cone normalization
(blueprint: lem-weil-isomorphism-comparison-natural).

Proof, node steps 3--5: apply
lem-weil-isomorphism-derived-pullback-comparison-normalization to the canonical
calculus S of lem-coef-derived-system-evaluation-calculus. Its entire-cone identity
is κ_N followed by θ_N = G(u_N), with zero shifted coordinate, for every ambient
N and under the canonical resolution comparisons. Thus κ_N = G(u_N) followed by
θ_N inverse. The completion is S.reduction followed by coefficientSequenceLimit,
and u is the actual adjunction unit. For v : N → N', unit naturality gives
completion(v) u_N = u_N' v. Naturality of θ therefore identifies θ_N' P_g(v) κ_N
with G(completion(v)) G(u_N), hence with θ_N' κ_N' G(v). Cancel θ_N' to obtain
naturality of the specified κ. No inverse of u_N is used. The same normalization
and the canonical representative comparisons identify the chosen derived component
with inverseImagePullbackComparison for every good resolution q : P → K.
Finally η = ρ followed by the right whiskering of κ with S has components
ρ_N followed by S(κ_N), and its naturality is the composite of the two squares. -/
theorem inverseImagePullbackComparisonIntegral_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ κ : inverseImageIntegralDerived l E g ⟶ integralDerivedPullback l E g,
      (∀ N : DerivedCategory (integralTowerModules l E Y),
        κ.app N = inverseImagePullbackComparisonDerived l E g hX hY N) ∧
      (∀ (K : CochainComplex (integralTowerModules l E Y) ℤ)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q],
        κ.app (DerivedCategory.Q.obj K) =
          inverseImagePullbackComparison l E g hX hY K P q) ∧
      (∀ (C : CoefficientDerivedSystemCalculus l E Y),
        Nonempty (CoefficientDerivedSystemCoherence l E Y C) →
        ∃ θ : integralDerivedPullback l E g ≅
            (C.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
              inverseImageIntegralDerived l E g,
          ∀ N : DerivedCategory (integralTowerModules l E Y),
            κ.app N = (inverseImageIntegralDerived l E g).map (C.adjunction.unit.app N) ≫
              θ.inv.app N) ∧
      (∀ (T : Type r) [Category.{s} T]
        (S : DerivedCategory (integralTowerModules l E X) ⥤ T)
        (H : DerivedCategory (integralTowerModules l E Y) ⥤ T)
        (ρ : H ⟶ inverseImageIntegralDerived l E g ⋙ S),
        ∃ η : H ⟶ integralDerivedPullback l E g ⋙ S,
          ∀ N : DerivedCategory (integralTowerModules l E Y),
            η.app N = ρ.app N ≫ S.map (κ.app N)) := by
  let Z := DerivedCategory.Q.obj
    (HomologicalComplex.zero : CochainComplex (integralTowerModules l E Y) ℤ)
  have hZ : IsDerivedCompleteUnrestricted l E Y Z := complete_zero l E Y
  have hn (C : CoefficientDerivedSystemCalculus l E Y)
      (hC : Nonempty (CoefficientDerivedSystemCoherence l E Y C)) :
      ∃ θ : integralDerivedPullback l E g ≅
          (C.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
            inverseImageIntegralDerived l E g,
        ∀ N, inverseImagePullbackComparisonDerived l E g hX hY N =
          (inverseImageIntegralDerived l E g).map (C.adjunction.unit.app N) ≫
            θ.inv.app N := by
    obtain ⟨θ, he, ht, _⟩ :=
      isomorphismDerivedPullbackComparisonNormalization l E g hX hY C hC Z hZ
    refine ⟨NatIso.ofComponents θ (fun f ↦ ht _ _ f), ?_⟩
    intro N
    exact (Iso.eq_comp_inv (θ N)).2 (he N)
  obtain ⟨κ, hres⟩ := integral_comparison_descent l E g hX hY
  have hk (N) : κ.app N = inverseImagePullbackComparisonDerived l E g hX hY N :=
    integral_comparison_representative l E g hX hY κ hres N
  refine ⟨κ, hk, hres, ?_, ?_⟩
  · intro C hC
    obtain ⟨θ, he⟩ := hn C hC
    exact ⟨θ, fun N ↦ (hk N).trans (he N)⟩
  · intro T _ S H ρ
    exact ⟨ρ ≫ whiskerRight κ S, fun _ ↦ rfl⟩

end WeilConjectures
