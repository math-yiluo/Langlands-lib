/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import all WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportNativeTowerComparison

/-! The total-limit projection identity for the strict compact-support system.
(blueprint: lem-qcqs-compact-support-strict-reduction-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u uC vC uD vD uV vV uW vW
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

private theorem whiskeredComparison_heq
    {C : Type uC} {D : Type uD} {V : Type uV} {W : Type uW}
    [Category.{vC} C] [Category.{vD} D] [Category.{vV} V] [Category.{vW} W]
    (i : C ⥤ D) (T : D ⥤ V) {RF L : V ⥤ W} {F : C ⥤ W}
    (γ : F ≅ i ⋙ T ⋙ RF) (ζ : RF ≅ L)
    {Ev : V ⥤ W} (p : L ⟶ Ev) (π : RF ⟶ Ev)
    (hp : ζ.hom ≫ p = π) (K : C) {B : W}
    (e : Ev.obj (T.obj (i.obj K)) ⟶ B) {α : Type vW} (r : α)
    (hr : HEq (γ.hom.app K ≫ π.app (T.obj (i.obj K)) ≫ e) r) :
    HEq ((γ ≪≫ Functor.isoWhiskerLeft i (Functor.isoWhiskerLeft T ζ)).hom.app K ≫
      p.app (T.obj (i.obj K)) ≫ e) r := by
  change HEq ((γ.hom.app K ≫ ζ.hom.app (T.obj (i.obj K))) ≫
    p.app (T.obj (i.obj K)) ≫ e) r
  have h := congrArg (fun a ↦ a.app (T.obj (i.obj K))) hp
  dsimp only [NatTrans.comp_app] at h
  rw [← Category.assoc,
    Category.assoc (γ.hom.app K) (ζ.hom.app (T.obj (i.obj K)))
      (p.app (T.obj (i.obj K))), h, Category.assoc]
  exact hr

private theorem rightDerived_transport
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (F : C ⥤ H) (W : MorphismProperty C) [L.IsLocalization W]
    (RF RF' : D ⥤ H) (η : F ⟶ L ⋙ RF) (η' : F ⟶ L ⋙ RF')
    (hr : RF = RF') (hη : HEq η η')
    (hd : RF'.IsRightDerivedFunctor η' W) : RF.IsRightDerivedFunctor η W := by
  subst RF'
  cases eq_of_heq hη
  exact hd

private theorem normalizedLimitComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u})
    (RF : coefficientSequenceRestrictedDerived l E Y ⥤
      DerivedCategory (scalarReductionSource l E Y))
    (η : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
        scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    (hd : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)))
    (π : ∀ n : ℕ, RF ⟶ pbcTowerEvaluation Y
      (completedIntegralCommRingSheafUnrestricted l E Y) n)
    (hπ : ∀ (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ),
      η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E Y n).hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (Opposite.op n)) (.up ℤ)).app I)) :
    ∃ ζ : RF ≅ coefficientConstantTowerLimit l E Y,
      ∀ n, ζ.hom ≫ coefficientConstantTowerProjection l E Y n = π n := by
  let := hd
  let U := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
  have := canonicalDerivedUnit_isDerived U
  let ζ : RF ≅ coefficientConstantTowerLimit l E Y :=
    Functor.rightDerivedUnique RF U.rightDerivedFunctor η (canonicalDerivedUnit U)
      (HomologicalComplex.quasiIso _ (.up ℤ))
  have hz (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ) :
      η.app I ≫ ζ.hom.app (DerivedCategory.Q.obj I) = (canonicalDerivedUnit U).app I := by
    dsimp only [ζ, coefficientConstantTowerLimit, U]
    simpa only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom, Iso.refl_hom,
      Category.id_comp, NatTrans.id_app] using
      Functor.rightDerivedNatTrans_app RF U.rightDerivedFunctor η
        (canonicalDerivedUnit U) (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟙 _) I
  refine ⟨ζ, fun n ↦ ?_⟩
  apply NatTrans.ext
  funext K
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI
  have hu : IsIso ((canonicalDerivedUnit U).app I) := by
    dsimp [canonicalDerivedUnit]
    infer_instance
  have : IsIso (η.app I ≫ ζ.hom.app (DerivedCategory.Q.obj I)) := by
    rw [hz]
    exact hu
  have : IsIso (η.app I) := IsIso.of_isIso_comp_right _ (ζ.hom.app _)
  have hq : (ζ.hom ≫ coefficientConstantTowerProjection l E Y n).app
        (DerivedCategory.Q.obj I) = (π n).app (DerivedCategory.Q.obj I) := by
    apply (cancel_epi (η.app I)).1
    apply (cancel_mono
      ((coefficientConstantTowerEvaluationFactors l E Y n).hom.app I)).1
    simp only [NatTrans.comp_app, ← Category.assoc, hz]
    have hpr := (coefficientConstantTowerProjection_exists l E Y n).choose_spec.1 I
    change (coefficientConstantTowerProjection l E Y n).app
      (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerEvaluationFactors l E Y n).hom.app I = _ at hpr
    rw [Category.assoc, Category.assoc, hpr,
      ← Category.assoc, canonicalDerivedUnit_objIso U I, Category.id_comp]
    exact (hπ n I).symm
  apply (cancel_mono ((coefficientConstantTowerEvaluation l E Y n).map e.hom)).1
  rw [← (ζ.hom ≫ coefficientConstantTowerProjection l E Y n).naturality, hq]
  simpa only [coefficientConstantTowerEvaluation, pbcTowerEvaluation] using
    (π n).naturality e.hom

private theorem recordedTowerLimit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K₀ : Type u) [Field K₀] (hk : IsUnit (l : K₀))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    (e : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      compactSupportRestrictedLevel l E c n)
    (hT : T = Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower l E K₀ X Y f hk c))).2.2)
    (he : HEq e (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E K₀ X Y f hk c))).2.2).2).2)) :
    ∃ ρ : sfCompactSupportFiniteIntegralFunctor l K₀ hk c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ T ⋙ coefficientConstantTowerLimit l E Y,
      ∀ (C : sfIntegralConstructibleCategory l E X) (n : ℕ),
        HEq (ρ.hom.app C ≫
            (coefficientConstantTowerProjection l E Y n).app (T.obj C.obj) ≫
              (e n).hom.app C.obj)
          (Classical.choose (Classical.choose_spec
            (exists_isDerivedLimit_and_iso (sfCompactSupportTerm l E c C.obj)
              (sfCompactSupportTransition l E c C.obj)).1) ≫
            Pi.π (sfCompactSupportTerm l E c C.obj) n) := by
  classical
  let H := exists_compactSupportRepresentativeComparison l E K₀ hk X Y f c
  let Tr := H.choose
  let er := H.choose_spec.choose
  let HR := H.choose_spec.choose_spec.2.2
  let RF := HR.choose
  let η := HR.choose_spec.choose
  let HP := HR.choose_spec.choose_spec.2.2
  let π := HP.choose
  have hTr := H.choose_spec.choose_spec.1
  have her := H.choose_spec.choose_spec.2.1
  have hF : SfCompactSupportFiniteRealizationSpec l K₀ hk c E
      (sfCompactSupportFiniteIntegralFunctor l K₀ hk c E) := by
    unfold sfCompactSupportFiniteIntegralFunctor
    exact (sfCompactSupportFiniteRealization l K₀ hk c E).choose_spec
  let γType := sfCompactSupportFiniteIntegralFunctor l K₀ hk c E ⋙
    (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ Tr ⋙ RF
  -- Project the large realization predicate without re-elaborating its telescope.
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hF) none
    let mut ty ← Lean.Meta.inferType h
    for right in [true, true, true, false] do
      ty ← Lean.Meta.whnf ty
      let args := ty.getAppArgs
      unless ty.isAppOfArity ``And 2 do
        throwError "expected a realization conjunct"
      h := Lean.mkAppN (Lean.mkConst (if right then ``And.right else ``And.left))
        #[args[0]!, args[1]!, h]
      ty := args[if right then 1 else 0]!
    ty ← Lean.Meta.whnf ty
    unless ty.isAppOfArity ``Exists 2 do
      throwError "expected the normalized realization isomorphism"
    let args := ty.getAppArgs
    let levels := [← Lean.Meta.getLevel args[0]!]
    let witness := Lean.mkAppN (Lean.mkConst ``Exists.choose levels)
      #[args[0]!, args[1]!, h]
    let spec := Lean.mkAppN (Lean.mkConst ``Exists.choose_spec levels)
      #[args[0]!, args[1]!, h]
    let gtype ← Lean.Elab.Term.elabTerm (Lean.mkIdent `γType) none
    let (gvar, goal) ← (← (← Lean.Elab.Tactic.getMainGoal).define `γ
      gtype witness).intro1P
    let (_, goal) ← goal.note `hγ spec (args[1]!.beta #[Lean.mkFVar gvar])
    Lean.Elab.Tactic.replaceMainGoal [goal]
  let hR := @ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
    Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
    ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
    (fun U a b ↦ @mul_comm
      ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
    (scalarReductionSourceDerived l E Y)
    (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))
  have hr : RF = hR.choose := HR.choose_spec.choose_spec.1
  have hη : HEq η hR.choose_spec.choose := HR.choose_spec.choose_spec.2.1
  have hd : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    rightDerived_transport DerivedCategory.Q _
      (HomologicalComplex.quasiIso _ (.up ℤ)) RF hR.choose η hR.choose_spec.choose hr hη
      hR.choose_spec.choose_spec.1
  have hπ := HP.choose_spec.1
  -- The arguments have already been typed by the recorded realization. Construct
  -- the application directly, avoiding repeated reduction of its large telescope.
  run_tac Lean.Elab.Tactic.withMainContext do
    let eE ← Lean.Elab.Term.elabTerm (Lean.mkIdent `E) none
    let .succ level := (← Lean.Meta.getLevel eE).normalize
      | throwError "expected a coefficient type universe"
    let mut app := Lean.mkConst ``normalizedLimitComparison [level]
    let mut ty ← Lean.Meta.inferType app
    let mut names := [`l, `E, `Y, `RF, `η, `hd, `π, `hπ]
    while let .forallE _ domain body bi := ty do
      let arg ← if bi.isInstImplicit then Lean.Meta.synthInstance domain else do
        let name :: rest := names | throwError "unexpected comparison parameter"
        names := rest
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
      app := Lean.mkApp app arg
      ty := body.instantiate1 arg
    unless names.isEmpty do
      throwError "missing comparison parameter"
    let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hlim app ty
    Lean.Elab.Tactic.replaceMainGoal [goal]
  let ζ := hlim.choose
  have hζ := hlim.choose_spec
  have hTrT : Tr = T := hTr.trans hT.symm
  clear hT
  subst T
  have he' : HEq er e := her.trans he.symm
  have heq : er = e := eq_of_heq he'
  subst e
  let ρ := γ ≪≫ Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι
    (Functor.isoWhiskerLeft Tr ζ)
  refine ⟨ρ, fun C n ↦ ?_⟩
  let i := (sfIntegralConstructible l E X).ι
  let p := coefficientConstantTowerProjection l E Y n
  let pn := π n
  have hpn := hζ n
  have hγn := hγ C n
  -- All terms already have their types. Avoid re-solving the large inferred
  -- category telescope; the completed application is checked by the kernel.
  run_tac Lean.Elab.Tactic.withMainContext do
    let localTerm (name : Lean.Name) :=
      Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
    let i ← localTerm `i
    let t ← localTerm `Tr
    let rf ← localTerm `RF
    let gamma ← localTerm `γ
    let zeta ← localTerm `ζ
    let p ← localTerm `p
    let pn ← localTerm `pn
    let hpn ← localTerm `hpn
    let k ← localTerm `C
    let hr ← localTerm `hγn
    let args (label : String) (e : Lean.Expr) (size : Nat) := do
      let a := e.getAppArgs
      unless a.size = size do
        throwError "{label}: expected {size} arguments, got {a.size}"
      pure a
    let it ← args "inclusion" (← Lean.Meta.whnf (← Lean.Meta.inferType i)) 4
    let tt ← args "tower" (← Lean.Meta.whnf (← Lean.Meta.inferType t)) 4
    let rt ← args "derived limit" (← Lean.Meta.whnf (← Lean.Meta.inferType rf)) 4
    let gt ← args "realization" (← Lean.Meta.whnf (← Lean.Meta.inferType gamma)) 4
    let zt ← args "limit comparison" (← Lean.Meta.whnf (← Lean.Meta.inferType zeta)) 4
    let pt ← args "limit projection" (← Lean.Meta.whnf (← Lean.Meta.inferType p)) 6
    let ht ← args "Roos equation" (← Lean.Meta.whnf (← Lean.Meta.inferType hr)) 4
    let outer := ht[1]!.getAppArgs
    unless outer.size > 0 do throwError "expected the outer Roos composite"
    let inner := outer.back!.getAppArgs
    unless inner.size > 0 do throwError "expected the inner Roos composite"
    let e := inner.back!
    let et := (← Lean.Meta.inferType e).getAppArgs
    unless et.size > 0 do throwError "expected a projection morphism type"
    let catLevels (inst : Lean.Expr) := do
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType inst)
      let ls := ty.getAppFn.constLevels!
      unless ls.length = 2 do throwError "expected two category universes"
      pure ls
    let ci ← catLevels it[1]!
    let di ← catLevels it[3]!
    let vi ← catLevels tt[3]!
    let wi ← catLevels rt[3]!
    let levels := [("vC", ci[0]!), ("uC", ci[1]!),
      ("vD", di[0]!), ("uD", di[1]!), ("vV", vi[0]!), ("uV", vi[1]!),
      ("vW", wi[0]!), ("uW", wi[1]!)]
    let info ← Lean.getConstInfo ``whiskeredComparison_heq
    let us ← info.levelParams.mapM fun name ↦ do
      match levels.lookup name.toString with
      | some level => pure level
      | none => throwError "unexpected comparison universe {name}"
    let app := Lean.mkAppN (Lean.mkConst ``whiskeredComparison_heq us)
      #[it[0]!, it[2]!, tt[2]!, rt[2]!, it[1]!, it[3]!, tt[3]!, rt[3]!,
        i, t, rf, zt[3]!, gt[2]!, gamma, zeta, pt[5]!, p, pn, hpn, k,
        et.back!, e, ht[2]!, ht[3]!, hr]
    (← Lean.Elab.Tactic.getMainGoal).assign app
    Lean.Elab.Tactic.replaceMainGoal []

private theorem projectionTransport
    {A B : Type*} [Category A] [Category B] (I : A ⥤ B)
    {x y : A} (h : x = y) {Z : B} (p : I.obj x ⟶ Z) (q : I.obj y ⟶ Z)
    (hp : HEq p q) : p = I.map (eqToHom h) ≫ q := by
  subst y
  cases eq_of_heq hp
  simp

private theorem projectionPaste
    {C : Type*} [Category C] {A B D F G H J : C}
    (a : A ⟶ B) (b : B ⟶ D) (p : D ⟶ F) (q : B ⟶ G)
    (v : G ⟶ F) (r : F ⟶ H) (s : H ⟶ J) (t : G ⟶ J)
    (hn : b ≫ p = q ≫ v) (ht : v ≫ r ≫ s = t) :
    (a ≫ b) ≫ (p ≫ r) ≫ s = a ≫ q ≫ t := by
  simp only [Category.assoc]
  rw [← Category.assoc b p, hn]
  simp only [Category.assoc]
  rw [ht]

private theorem adjunctTransport
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    {x y : C} {z : D} (t : x ⟶ y) (p : y ⟶ R.obj z) :
    t ≫ p = adj.unit.app x ≫ R.map (F.map t ≫ (adj.homEquiv y z).symm p) := by
  have h := adj.homEquiv_naturality_left t ((adj.homEquiv y z).symm p)
  simpa only [Adjunction.homEquiv_unit, Equiv.apply_symm_apply] using h.symm

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

-- SY is retained verbatim in the existing public interface.
set_option linter.unusedVariables false in
/-- The recorded integral comparison has the prescribed native finite projections.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-strict-reduction-comparison).

Restrict the coherent compact-support tower to completed scalars and use the specified
right-derived total-limit comparison.  The representative-independence comparison then
provides `γ`; normalization of the derived-limit projections gives the displayed finite
scalar-adjunction equation.  This subclaim concerns the projection identity only.
-/
theorem qcqsCompactSupport_strictReductionGamma
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) :
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) : N ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
        scalarReductionDerivedExtension l E X n ⋙
          sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ (γ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
          (sfIntegralConstructible l E Y).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ N ⋙
          coefficientSequenceLimit l E Y),
      ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
        γ.hom.app K ≫ (coefficientSequenceProjection l E Y n).app
              ((N).obj K.obj) ≫
            (coefficientFiniteDerivedRestriction l E Y n).map
              ((e n).hom.app K.obj) =
          (coefficientFiniteAdjunction l E Y n).unit.app
              ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≫
            (coefficientFiniteDerivedRestriction l E Y n).map
              (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom := by
  classical
  let hT := exists_compactSupportReductionTower l E K₀ X Y f hl c
  let T := hT.choose_spec.choose_spec.2.2.choose
  let eT := hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose
  obtain ⟨ρ, hρ⟩ := recordedTowerLimit l E K₀ hl c T eT rfl HEq.rfl
  dsimp only
  let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g
  let e (n : ℕ) :=
    Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
      Functor.isoWhiskerRight (SX.reductionEvaluation n)
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
  obtain ⟨α, hα⟩ := qcqsCompactSupport_nativeTowerComparison l E K₀ hl c SX
  let γ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
      (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ N ⋙ coefficientSequenceLimit l E Y :=
    ρ ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι α)
      (coefficientConstantTowerLimit l E Y)
  refine ⟨γ, fun K n ↦ ?_⟩
  have hcoord := projectionTransport (sfIntegralConstructible l E Y).ι
    (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K) _ _ (hρ K n)
  have hnat := (coefficientConstantTowerProjection l E Y n).naturality (α.hom.app K.obj)
  have heq : γ.hom.app K ≫ (coefficientSequenceProjection l E Y n).app (N.obj K.obj) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map ((e n).hom.app K.obj) =
      ρ.hom.app K ≫ (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj) ≫
        (eT n).hom.app K.obj := by
    dsimp only [γ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      coefficientSequenceProjection]
    exact projectionPaste _ _ _ _ _ _ _ _ hnat (hα K.obj n)
  rw [heq, hcoord]
  change _ = (coefficientFiniteAdjunction l E Y n).unit.app _ ≫
    (coefficientFiniteDerivedRestriction l E Y n).map
      ((scalarReductionDerivedExtension l E Y n).map
        ((sfIntegralConstructible l E Y).ι.map
          (eqToHom (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K))) ≫
        sfCompactSupportChosenReduction l K₀ hl c E K n)
  exact adjunctTransport (coefficientFiniteAdjunction l E Y n)
    ((sfIntegralConstructible l E Y).ι.map
      (eqToHom (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K))) _

end WeilConjectures
