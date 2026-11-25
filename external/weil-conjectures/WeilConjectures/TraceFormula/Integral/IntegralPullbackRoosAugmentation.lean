/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-!
# The strict Roos lift of the integral inverse-image comparison

Source: Stacks Project, Tags 03D6, 06YY and 0941
(blueprint: lem-trf-integral-pullback-reduction-counit).
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

/-- Maps into a mapping cocone are determined by their `fst` and `snd` coordinates. -/
private theorem cone_ext
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    {X Y P : CochainComplex A ℤ} (δ : X ⟶ Y)
    (f g : P ⟶ CochainComplex.mappingCocone δ)
    (hf : f ≫ CochainComplex.mappingCocone.fst δ =
      g ≫ CochainComplex.mappingCocone.fst δ)
    (hs : ∀ i : ℤ, f.f i ≫ (CochainComplex.mappingCocone.snd δ).v
      i (i - 1) (by omega) = g.f i ≫ (CochainComplex.mappingCocone.snd δ).v
      i (i - 1) (by omega)) : f = g := by
  ext i : 1
  have hfi := congrArg (fun f ↦ HomologicalComplex.Hom.f f i) hf
  dsimp only [HomologicalComplex.comp_f] at hfi
  calc
    _ = _ ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ ≫ ((CochainComplex.mappingCocone.fst δ).f i ≫
        (CochainComplex.mappingCocone.inl δ).v i i (add_zero _) +
        (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr δ).1.v (i - 1) i (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X]
    _ = _ := by
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hs i, hfi]
      conv_rhs => rw [← Category.comp_id (g.f i),
        ← CochainComplex.mappingCocone.id_X δ i (i - 1) (by omega)]
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]

/-- A Roos map preserves a vanishing shifted coordinate, also after precomposition. -/
private theorem roosMap_comp_snd_eq_zero
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {P Q : CochainComplex A ℤ} {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (a : P ⟶ Q) (f : Q ⟶ integralOperationsRoos C) (q : C ⟶ D)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega) = 0)
    (i : ℤ) :
    (a ≫ f ≫ integralOperationsRoosFunctor.map q).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary D)).v i (i - 1) (by omega) =
        0 := by
  have hq : (integralOperationsRoosFunctor.map q).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary D)).v i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega) ≫
        (Limits.Pi.map (fun n : ℕ ↦ q.app (op n))).f (i - 1) :=
    (IntegralAmbient.roosMap_coordinates q).2 i (i - 1) (by omega)
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [hq, ← Category.assoc (f.f i), hf i, zero_comp, comp_zero]

private theorem cast_map
    {A : Type*} [Category A] {P Q : A ⥤ AddCommGrpCat.{u + 1}} (e : P = Q)
    {U V : A} (f : U ⟶ V) (x : Q.obj U) :
    P.map f (cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj U)) e).symm x) =
      cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj V)) e).symm (Q.map f x) := by
  subst e
  rfl

/-- Restricted sections are compatible with restriction maps. -/
private theorem restrictedSection_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (M : coefficientSequenceModules l E X) (n : ℕ)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.map f
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X M n V
        (M.val.map (Prod.mkHom (𝟙 n) f.unop).op x) := by
  have e : (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.presheaf =
      (Prod.sectR n X.ProEt).op ⋙ M.val.presheaf := by
    change (((coefficientSequenceRestriction_exists l E X).exists.choose.obj M).obj
      (op n)).val.presheaf = _
    rw [(coefficientSequenceRestriction_exists l E X).exists.choose_spec.1 M n]
    rfl
  exact cast_map e f x

/-- The defining Roos lift of the inverse-image comparison is the limit lift of the
inverse image of a strict quotient presentation, followed by the whole-tower tensor
unit and the normalized pullback tower identification.

Source: Stacks Project, Tags 03D6, 06YY and 0941; Steps 3 and 5 of the
resolution-matching argument (blueprint: lem-trf-integral-pullback-reduction-counit).

Proof: both sides are maps into a Roos cone, so they are determined by their
unshifted coordinates and their shifted coordinate. The shifted coordinates vanish
for both. In the unshifted coordinate at level n, the left side is theta_n. On a
section x over U, the right side sends x to b(x), which is the strict reduction of
the tensor generator 1 tensor x, then inserts the sequence-pullback generator and
restricts along the comma arrow of U, and finally applies q. By the generator
formula for q and naturality of q under restriction this is the restriction of the
finite pullback generator of 1 tensor x, which is the defining formula of theta_n. -/
theorem inverseImageRoosComparisonComplex_eq_limitToRoos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)
    (hb : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((b.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E W (C.X i) n U
          (integralComparisonSequenceSection l E W (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))
    (q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E h).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange h).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E h).obj (C.X i)) n
            (op ((proEtaleBaseChange h).obj U))
            (integralComparisonSequenceGenerator l E h (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E h n
            (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E W (C.X i) n (op U) x))) :
    inverseImageRoosComparisonComplex l E h P =
      ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Z)).mapHomologicalComplex
          (.up ℤ)).homEquiv _ _
        ((NatTrans.mapHomologicalComplex
            (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E h)).hom (.up ℤ)).app P ≫
          ((integralTowerInverseImage l E h).mapHomologicalComplex (.up ℤ)).map b ≫
          (NatTrans.mapHomologicalComplex (integralTowerInverseImageUnit l E h).hom
            (.up ℤ)).app C) ≫
        integralComparisonLimitToRoos l E Z _ ≫ integralOperationsRoosFunctor.map q.hom := by
  let T := ((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
    (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj C)
  let A := ((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).obj P
  let c := (NatTrans.mapHomologicalComplex
      (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E h)).hom (.up ℤ)).app P ≫
    ((integralTowerInverseImage l E h).mapHomologicalComplex (.up ℤ)).map b ≫
    (NatTrans.mapHomologicalComplex (integralTowerInverseImageUnit l E h).hom
      (.up ℤ)).app C
  let adj := (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Z)).mapHomologicalComplex
    (.up ℤ)
  let a := adj.homEquiv A T c
  have ha (n : ℕ) (i : ℤ) :
      a.f i ≫ limit.π (T.X i) (op n) = (c.f i).app (op n) := by
    have h := (adj.homEquiv A T).symm_apply_apply c
    rw [Adjunction.homEquiv_counit] at h
    exact congrArg (fun f ↦ (f.f i).app (op n)) h
  have hi := (integralComparisonLimitToRoos_existsUnique l E Z T).exists.choose_spec
  change (∀ n, integralComparisonLimitToRoos l E Z T ≫ _ ≫ _ = _) ∧ _ at hi
  let δ := scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)
  have hfirst : integralOperationsRoosFunctor.map q.hom ≫
      CochainComplex.mappingCocone.fst δ =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary T.asFunctor) ≫
        Limits.Pi.map (fun n : ℕ ↦ q.hom.app (op n)) :=
    (IntegralAmbient.roosMap_coordinates q.hom).1
  have hi2 (i : ℤ) : (integralComparisonLimitToRoos l E Z T).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary T.asFunctor)).v
        i (i - 1) (by omega) = 0 := hi.2 i (i - 1) (by omega)
  change _ = a ≫ integralComparisonLimitToRoos l E Z T ≫
    integralOperationsRoosFunctor.map q.hom
  apply cone_ext δ
  · simp only [Category.assoc]
    rw [hfirst]
    unfold inverseImageRoosComparisonComplex
    rw [CochainComplex.mappingCocone.lift_fst]
    apply Pi.hom_ext
    intro n
    symm
    calc
      _ = (a ≫ (NatTrans.mapHomologicalComplex (lim.π (op n))
            (.up ℤ)).app T) ≫ q.hom.app (op n) := by
        have hπ : Limits.Pi.map (fun m : ℕ ↦ q.hom.app (op m)) ≫
            Pi.π (fun m ↦ (integralOperationsPullbackLevel l E h m).obj P) n =
            Pi.π (fun m ↦ T.asFunctor.obj (op m)) n ≫ q.hom.app (op n) :=
          Limits.Pi.map_π (f := fun m ↦ T.asFunctor.obj (op m))
            (fun m ↦ q.hom.app (op m)) n
        simp only [Category.assoc]
        rw [hπ]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ a ≫ z ≫ q.hom.app (op n)) (hi.1 n)
      _ = _ := by
        rw [inverseImageReductionProduct, Pi.lift_comp_π]
        ext i U x
        change ((q.hom.app (op n)).f i).val.app U
          ((a.f i ≫ limit.π (T.X i) (op n)).val.app U x) = _
        rw [ha]
        let V := (proEtaleIsoPostcompose h).obj U.unop
        let t := unrestrictedIntegralTensorSection l E W n (P.X i) (op V) 1 x
        let y := integralComparisonSequenceSection l E W (C.X i) n (op V)
          (((κ n).inv.f i).val.app (op V) t)
        let N := (integralComparisonSequencePullback l E h).obj (C.X i)
        have hθ := (inverseImageReductionTheta_existsUnique l E h n P).exists.choose_spec
          i U.unop x
        have hu := (integralTowerInverseImageUnit_existsUnique l E h).exists.choose_spec
          (C.X i) n U.unop y
        have hr := restrictedSection_naturality l E Z N n (proEtaleIsoCommaArrow h U.unop).op
          (integralComparisonSequenceGenerator l E h (C.X i) n V y)
        have hn := PresheafOfModules.naturality_apply ((q.hom.app (op n)).f i).val
          (proEtaleIsoCommaArrow h U.unop).op
          (integralComparisonRestrictedSection l E Z N n
            (op ((proEtaleBaseChange h).obj V))
            (integralComparisonSequenceGenerator l E h (C.X i) n V y))
        have hk : ((κ n).hom.f i).val.app (op V) (((κ n).inv.f i).val.app (op V) t) = t :=
          congrArg (fun k ↦ (k.f i).val.app (op V) t) (κ n).inv_hom_id
        have hy : coefficientEvaluationSection l E W (C.X i) n (op V) y =
            ((κ n).inv.f i).val.app (op V) t := by
          dsimp only [y, integralComparisonSequenceSection, coefficientEvaluationSection]
          rw [← ConcreteCategory.comp_apply, eqToHom_trans]
          rfl
        have hqy := hq n i V y
        rw [hy, hk] at hqy
        have hbx := hb n i (op V) x
        refine Eq.trans ?_ hθ.symm
        refine Eq.trans ?_ (hn.trans (congrArg
          ((((integralOperationsPullbackLevel l E h n).obj P).X i).val.map
            (proEtaleIsoCommaArrow h U.unop).op) hqy))
        exact congrArg (fun z ↦ ((q.hom.app (op n)).f i).val.app U z)
          ((congrArg (fun z ↦ (((integralTowerInverseImageUnit l E h).hom.app (C.X i)).app
            (op n)).val.app U z) hbx).trans (hu.trans hr.symm))
  · intro i
    calc
      _ = 0 := by
        unfold inverseImageRoosComparisonComplex
        rw [CochainComplex.mappingCocone.lift_f_snd_v]
        rfl
      _ = _ :=
        (roosMap_comp_snd_eq_zero a (integralComparisonLimitToRoos l E Z T) q.hom hi2 i).symm

end WeilConjectures
