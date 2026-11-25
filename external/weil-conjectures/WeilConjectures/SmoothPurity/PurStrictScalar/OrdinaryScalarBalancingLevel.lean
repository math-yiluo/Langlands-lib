/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteQuotientModuleBalancing
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement

/-! # Ordinary scalar reduction at one quotient level

Source: Stacks 03EK and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem tensorUnit (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction a).unit.app M).val.app U x =
      pbcTensorSection a M U 1 x :=
  (pbcScalarAdjunction_exists a).exists.choose_spec M U x

private theorem tensor_smul (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules W R) (U : W.ProEtᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    pbcTensorSection a M U b x = b • pbcTensorSection a M U 1 x := by
  change completedAdicChangeTensor W a M U b x =
    b • completedAdicChangeTensor W a M U 1 x
  simpa only [mul_one] using completedTensor_smul W a M U b 1 x

private theorem tensor_map (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : pbcModules W R} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (b : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend a).map f).val.app U (pbcTensorSection a M U b x) =
      pbcTensorSection a N U b (f.val.app U x) := by
  have h := congrArg (fun k ↦ k.val.app U x)
    ((pbcScalarAdjunction a).unit.naturality f)
  change ((pbcScalarAdjunction a).unit.app N).val.app U (f.val.app U x) =
    ((pbcExtend a).map f).val.app U
      (((pbcScalarAdjunction a).unit.app M).val.app U x) at h
  rw [tensorUnit, tensorUnit] at h
  rw [tensor_smul, map_smul, ← h, ← tensor_smul]

private theorem scalarSquare_exists (W : Scheme.{u})
    {A B C D : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : A ⟶ B) (r : A ⟶ C) (s : B ⟶ D) (q : C ⟶ D)
    (h : a ≫ s = r ≫ q) (M : pbcModules W A) :
    ∃ d : (pbcExtend q).obj ((pbcExtend r).obj M) ≅
        (pbcExtend s).obj ((pbcExtend a).obj M),
      ∀ (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U),
        d.hom.val.app U (pbcTensorSection q _ U (s.hom.app U b)
          (pbcTensorSection r M U 1 x)) =
        pbcTensorSection s _ U 1 (pbcTensorSection a M U b x) := by
  let c := r ≫ q
  let k₁ := pbcRestrictComp r q c rfl
  let k₂ := pbcRestrictComp a s c h
  let a₁ := ((pbcScalarAdjunction r).comp (pbcScalarAdjunction q)).ofNatIsoRight k₁
  let a₂ := ((pbcScalarAdjunction a).comp (pbcScalarAdjunction s)).ofNatIsoRight k₂
  let d := (a₁.leftAdjointUniq a₂).app M
  have h₁ (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (a₁.unit.app M).val.app U x =
        pbcTensorSection q _ U 1 (pbcTensorSection r M U 1 x) := by
    change (k₁.hom.app _).val.app U
      (((pbcScalarAdjunction q).unit.app _).val.app U
        (((pbcScalarAdjunction r).unit.app M).val.app U x)) = _
    refine ((pbcRestrictComp_exists r q c rfl).exists.choose_spec _ U _).trans ?_
    exact (congrArg (((pbcScalarAdjunction q).unit.app _).val.app U)
      (tensorUnit W r M U x)).trans (tensorUnit W q _ U _)
  have h₂ (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (a₂.unit.app M).val.app U x =
        pbcTensorSection s _ U 1 (pbcTensorSection a M U 1 x) := by
    change (k₂.hom.app _).val.app U
      (((pbcScalarAdjunction s).unit.app _).val.app U
        (((pbcScalarAdjunction a).unit.app M).val.app U x)) = _
    refine ((pbcRestrictComp_exists a s c h).exists.choose_spec _ U _).trans ?_
    exact (congrArg (((pbcScalarAdjunction s).unit.app _).val.app U)
      (tensorUnit W a M U x)).trans (tensorUnit W s _ U _)
  have hd (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      d.hom.val.app U (pbcTensorSection q _ U 1 (pbcTensorSection r M U 1 x)) =
        pbcTensorSection s _ U 1 (pbcTensorSection a M U 1 x) := by
    have hu := congrArg (fun k ↦ k.val.app U x)
      (Adjunction.unit_leftAdjointUniq_hom_app a₁ a₂ M)
    change d.hom.val.app U ((a₁.unit.app M).val.app U x) =
      (a₂.unit.app M).val.app U x at hu
    rw [h₁, h₂] at hu
    exact hu
  refine ⟨d, ?_⟩
  intro U b x
  let y := pbcTensorSection r M U 1 x
  let z := pbcTensorSection a M U 1 x
  let sb := s.hom.app U b
  have hq := tensor_smul W q ((pbcExtend r).obj M) U sb y
  have hlin := (d.hom.val.app U).hom.map_smul sb (pbcTensorSection q _ U 1 y)
  have hs := (((pbcScalarAdjunction s).unit.app ((pbcExtend a).obj M)).val.app U).hom
    |>.map_smul b z
  have hs' : sb • pbcTensorSection s _ U 1 z =
      pbcTensorSection s _ U 1 (b • z) :=
    (congrArg (fun w : ((pbcExtend s).obj ((pbcExtend a).obj M)).val.obj U ↦ sb • w)
      (tensorUnit W s _ U z).symm).trans
      (hs.symm.trans (tensorUnit W s _ U (b • z)))
  exact (congrArg (d.hom.val.app U) hq).trans (hlin.trans
    ((congrArg (fun w ↦ sb • w) (hd U x)).trans
      (hs'.trans (congrArg (fun w ↦ pbcTensorSection s _ U 1 w)
        (tensor_smul W a M U b x).symm))))

private def levelProjection (W : Scheme.{u}) (n : ℕ) :
    ordinaryLimit l E W ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)) ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom

private theorem reductionEvaluation_exists (W : Scheme.{u}) (n : ℕ) :
    ∃ t : ordinaryReduction l E W ⋙ coefficientSequenceEvaluation l E W n ≅
        scalarReductionExtension l E W n,
      ∀ M : scalarReductionSource l E W,
        (ordinaryReductionAdj l E W).unit.app M ≫
          (levelProjection l E W n).app ((ordinaryReduction l E W).obj M) ≫
          (scalarReductionRestriction l E W n).map (t.hom.app M) =
        (purSequenceFiniteAdjunction l E W n).unit.app M := by
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E W
  let a := O.adjunction.ofNatIsoRight O.limit
  let c := (ordinaryReductionAdj l E W).leftAdjointUniq a
  let t := Functor.isoWhiskerRight c (coefficientSequenceEvaluation l E W n) ≪≫ O.tensor n
  refine ⟨t, ?_⟩
  intro M
  have hu := O.transpose M (O.pullback.obj M) (O.adjunction.unit.app M) n
  simp only [Adjunction.homEquiv_symm_unit, Adjunction.homEquiv_apply] at hu
  have hu' := congrArg (· ≫ (scalarReductionRestriction l E W n).map
    ((O.tensor n).hom.app M)) hu
  simp only [Category.assoc, ← Functor.map_comp] at hu'
  have hm := (coefficientSequenceEvaluation l E W n).map_id (O.pullback.obj M)
  have hz : (O.tensor n).inv.app M ≫
      (coefficientSequenceEvaluation l E W n).map (𝟙 (O.pullback.obj M)) ≫
      (O.tensor n).hom.app M = 𝟙 ((scalarReductionExtension l E W n).obj M) := by
    erw [hm, Category.id_comp]
    exact ((O.tensor n).app M).inv_hom_id
  have hu'' := congrArg (fun f ↦ (purSequenceFiniteAdjunction l E W n).unit.app M ≫
    (scalarReductionRestriction l E W n).map f) hz
  have hid := (scalarReductionRestriction l E W n).map_id
    ((scalarReductionExtension l E W n).obj M)
  have huNorm := hu'.symm.trans (hu''.trans
    ((congrArg (fun f ↦ (purSequenceFiniteAdjunction l E W n).unit.app M ≫ f) hid).trans
      (Category.comp_id _)))
  have hc := Adjunction.unit_leftAdjointUniq_hom_app (ordinaryReductionAdj l E W) a M
  have hn := (levelProjection l E W n).naturality (c.hom.app M)
  change (ordinaryLimit l E W).map (c.hom.app M) ≫
      (levelProjection l E W n).app (O.pullback.obj M) =
    (levelProjection l E W n).app ((ordinaryReduction l E W).obj M) ≫
      (scalarReductionRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).map (c.hom.app M)) at hn
  have hp : O.projection (O.pullback.obj M) n = O.limit.hom.app (O.pullback.obj M) ≫
      (levelProjection l E W n).app (O.pullback.obj M) :=
    O.projection_limit (O.pullback.obj M) n
  dsimp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [Functor.map_comp]
  have hn' := congrArg (fun f ↦ (ordinaryReductionAdj l E W).unit.app M ≫ f ≫
    (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M)) hn.symm
  calc
    _ = ((ordinaryReductionAdj l E W).unit.app M ≫
        (ordinaryLimit l E W).map (c.hom.app M)) ≫
        (levelProjection l E W n).app (O.pullback.obj M) ≫
        (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M) := by
      simpa only [Category.assoc] using hn'
    _ = a.unit.app M ≫ (levelProjection l E W n).app (O.pullback.obj M) ≫
        (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M) :=
      congrArg (fun f ↦ f ≫ (levelProjection l E W n).app (O.pullback.obj M) ≫
        (scalarReductionRestriction l E W n).map ((O.tensor n).hom.app M)) hc
    _ = (purSequenceFiniteAdjunction l E W n).unit.app M := by
      change (O.adjunction.unit.app M ≫ O.limit.hom.app (O.pullback.obj M)) ≫ _ = _
      simpa only [hp, Category.assoc] using huNorm

private theorem reductionLevel_exists (W : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource l E W) :
    let r := completedIntegralCommRingProjectionUnrestricted l E W n
    ∃ t : (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ≅
        (pbcRestrict r ⋙ constantRestriction l E W).obj ((pbcExtend r).obj M),
      ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        t.hom.val.app U
          ((((ordinaryReductionAdj l E W).unit.app M ≫
            limit.π ((coefficientSequenceRestriction l E W).obj
              ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x) =
          pbcTensorSection r M U 1 x := by
  let r := completedIntegralCommRingProjectionUnrestricted l E W n
  obtain ⟨t, ht⟩ := reductionEvaluation_exists l E W n
  let a : pbcExtend r ⊣ scalarReductionRestriction l E W n := pbcScalarAdjunction r
  let c := (purSequenceFiniteAdjunction l E W n).leftAdjointUniq a
  let d := t ≪≫ c
  let z := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app
    ((ordinaryReduction l E W).obj M)
  let e := (constantRestriction l E W).mapIso z ≪≫
    (scalarReductionRestriction l E W n ⋙ constantRestriction l E W).mapIso (d.app M)
  refine ⟨e, ?_⟩
  intro U x
  have h := (ht M)
  have hc := Adjunction.unit_leftAdjointUniq_hom_app
    (purSequenceFiniteAdjunction l E W n) a M
  have hh := (congrArg (· ≫ (scalarReductionRestriction l E W n).map
    (c.hom.app M)) h).trans hc
  have hu := congrArg (fun k ↦ k.val.app U x) hh
  change e.hom.val.app U
    ((((ordinaryReductionAdj l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj
        ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x) =
    (a.unit.app M).val.app U x at hu
  exact hu.trans (tensorUnit W r M U x)

private theorem positiveReductionLevel_exists (W : Scheme.{u}) (k : ℕ) (hk : 1 ≤ k)
    (M : scalarReductionSource l E W) :
    let r := PurCompactSupport.projection l E k hk W
    ∃ t : (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op (k - 1))) ≅
        (pbcRestrict r ⋙ constantRestriction l E W).obj ((pbcExtend r).obj M),
      ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        t.hom.val.app U
          ((((ordinaryReductionAdj l E W).unit.app M ≫
            limit.π ((coefficientSequenceRestriction l E W).obj
              ((ordinaryReduction l E W).obj M)) (op (k - 1))).val.app U) x) =
          pbcTensorSection r M U 1 x := by
  cases k with
  | zero => omega
  | succ n =>
    change ∃ t : (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ≅
        (pbcRestrict (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) W) ⋙ constantRestriction l E W).obj
          ((pbcExtend (PurCompactSupport.projection l E (n + 1)
            (Nat.le_add_left 1 n) W)).obj M), _
    have hr : PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W =
        completedIntegralCommRingProjectionUnrestricted l E W n := by
      unfold PurCompactSupport.projection
      simp only [eqToHom_refl, Category.comp_id]
      rfl
    erw [hr]
    exact reductionLevel_exists l E W n M

private theorem iso_section_injective (W : Scheme.{u})
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    {M N : pbcModules W R} (t : M ≅ N) (U : W.ProEtᵒᵖ) :
    Function.Injective (t.hom.val.app U) := by
  intro x y h
  have hi (z : M.val.obj U) : t.inv.val.app U (t.hom.val.app U z) = z :=
    congrArg (fun f ↦ f.val.app U z) t.hom_inv_id
  exact (hi x).symm.trans ((congrArg (t.inv.val.app U) h).trans (hi y))

/-- At a single quotient level the scalar reassociation has its prescribed tensor formula.
Source: Stacks 03EK (tensor/restriction adjunction), 0940 (quotient systems).
Proof: evaluation of the quotient-system left adjoint identifies its unit with the
quotient map M to M modulo the source uniformizer power. The ramification equality
identifies its extension to B with the retained target uniformizer ideal. Tensor
associativity and the quotient tensor equivalence therefore give an isomorphism
B tensor_A (M modulo t^(n+1)) to (Bhat tensor_Ahat M) modulo v^(e(n+1)).
Send b tensor (1 tensor x) to 1 tensor (b tensor x). The inverse is the reverse
reassociation, using the quotient ideal equality; both composites are identity on
local tensor generators. Apply module sheafification, whose universal property
preserves these inverse maps and the formula. Transport the quotient adjunction
unit by uniqueness of left adjoints to obtain exactly the unit appearing here.
This only asserts existence separately for M,n; horizontal and module naturality
are proved by the consuming tower construction. Positivity ensures the retained
exponent is positive, and the zero module and empty site object cause no exception.
(blueprint: lem-pur-ordinary-scalar-balancing-level). -/
theorem ordinaryScalarBalancingLevel_exists (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    let ηE (M : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : M.val.obj U) :=
      (((ordinaryReductionAdj l E W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
          ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x
    let ηF (M : scalarReductionSource l F W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : M.val.obj U) :=
      (((ordinaryReductionAdj l F W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction.{u, u} l F W).obj
          ((ordinaryReduction l F W).obj M)) (op n)).val.app U) x
    ∀ (M : scalarReductionSource l E W) (n : ℕ),
    ∃ β : (pbcExtend (constantMap l E F i W)).obj
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ≅
      (((ordinaryReduction l F W ⋙ systemRestriction l F W).obj
        ((pbcExtend (completedCoefficientMap l E F i W)).obj M)).obj
          (op (e * (n + 1) - 1))),
      ∀ (U : W.ProEtᵒᵖ)
        (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.val.app U)
            (pbcTensorSection (constantMap l E F i W)
              ((((ordinaryReduction l E W ⋙ systemRestriction l E W)).obj M).obj (op n)) U b
              (ηE M n U x)) =
          ηF
            ((pbcExtend (completedCoefficientMap l E F i W)).obj M)
            (e * (n + 1) - 1) U
            (pbcTensorSection (completedCoefficientMap l E F i W) M U
              (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x) := by
  dsimp only
  intro M n
  let a := completedCoefficientMap l E F i W
  let r := PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W
  let s := PurCompactSupport.projection l F (e * (n + 1))
    (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W
  let q := (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
    (Nat.le_add_left 1 n)).map W
  let N := (pbcExtend a).obj M
  obtain ⟨tE, htE⟩ := positiveReductionLevel_exists l E W (n + 1)
    (Nat.le_add_left 1 n) M
  obtain ⟨tF, htF⟩ := positiveReductionLevel_exists l F W (e * (n + 1))
    (Nat.mul_pos hepos (Nat.le_add_left 1 n)) N
  obtain ⟨b₀, hb₀⟩ := finiteQuotientModuleBalancing_exists l E F i W e he hepos n
    ((pbcExtend r).obj M)
  have hsquare : a ≫ s = r ≫ q :=
    PurCompactSupport.ramified_reduction_square l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n) W
  obtain ⟨d, hd⟩ := scalarSquare_exists W a r s q hsquare M
  let β := (pbcExtend (constantMap l E F i W)).mapIso tE ≪≫ b₀ ≪≫
    (pbcRestrict s ⋙ constantRestriction l F W).mapIso d ≪≫ tF.symm
  refine ⟨β, ?_⟩
  intro U b x
  apply iso_section_injective W tF U
  have hi (z) : tF.hom.val.app U (tF.inv.val.app U z) = z :=
    congrArg (fun f ↦ f.val.app U z) tF.inv_hom_id
  change tF.hom.val.app U (tF.inv.val.app U
    (d.hom.val.app U (b₀.hom.val.app U
      (((pbcExtend (constantMap l E F i W)).map tE.hom).val.app U
        (pbcTensorSection (constantMap l E F i W) _ U b _))))) = _
  have htE' : tE.hom.val.app U
      ((((ordinaryReductionAdj l E W).unit.app M ≫
        limit.π ((coefficientSequenceRestriction l E W).obj
          ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x) =
        pbcTensorSection r M U 1 x := htE U x
  erw [hi, tensor_map, htE', hb₀, hd, htF]

end WeilConjectures.PurStrictScalar
