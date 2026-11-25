/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Constructor laws for ordinary strict quotient adjuncts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientFiniteQuotientExtension
  scalarReductionExistence scalarReductionDerivedExistence

private theorem compatible_adjoint_isIso
    {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R)
    {M M' : B} {N N' : C} (em : M ≅ M') (en : N ≅ N')
    (t : M ⟶ R.obj N) (u : M' ⟶ R.obj N')
    (h : t ≫ R.map en.hom = em.hom ≫ u)
    (hu : IsIso ((aq.homEquiv _ _).symm u)) :
    IsIso ((aq.homEquiv _ _).symm t) := by
  have hf : (aq.homEquiv _ _).symm t ≫ en.hom =
      L.map em.hom ≫ (aq.homEquiv _ _).symm u := by
    apply (aq.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  have : IsIso ((aq.homEquiv _ _).symm t ≫ en.hom) := by
    rw [hf]
    infer_instance
  exact IsIso.of_isIso_comp_right _ en.hom

private theorem single_mate_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
    (F : A ⥤ B) [F.Additive] (H : A ⥤ C) [H.Additive]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R) [L.Additive] [R.Additive]
    (τ : F ⟶ H ⋙ R) (M : A)
    (hM : IsIso ((aq.homEquiv _ _).symm (τ.app M))) :
    IsIso (((aq.mapHomologicalComplex (.up ℤ)).homEquiv
      ((F.mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single A (.up ℤ) 0).obj M))
      ((H.mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single A (.up ℤ) 0).obj M))).symm
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M))) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let g := ((aq.mapHomologicalComplex (.up ℤ)).homEquiv
      ((F.mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single A (.up ℤ) 0).obj M))
      ((H.mapHomologicalComplex (.up ℤ)).obj
        ((HomologicalComplex.single A (.up ℤ) 0).obj M))).symm
    ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P)
  have hi (k : ℤ) : IsIso (g.f k) := by
    by_cases hk : k = 0
    · subst k
      change IsIso ((aq.homEquiv _ _).symm (τ.app (P.X 0)))
      let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
      exact compatible_adjoint_isIso aq (F.mapIso e) (H.mapIso e)
        (τ.app (P.X 0)) (τ.app M) (τ.naturality e.hom).symm hM
    · have hz : IsZero (P.X k) := HomologicalComplex.isZero_single_obj_X _ 0 M k hk
      exact (Functor.map_isZero L (Functor.map_isZero F hz)).isIso
        (Functor.map_isZero H hz) (g.f k)
  exact HomologicalComplex.Hom.isIso_of_components g

private theorem unit_mate_isIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{u}}
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (φ : A ⟶ B) {F : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B}
    (ad : F ⊣ SheafOfModules.restrictScalars φ)
    (q : SheafOfModules.unit A ⟶
      (SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit B))
    (hq : ∀ U, q.val.app U (1 : A.obj.obj U) = (1 : B.obj.obj U)) :
    IsIso ((ad.homEquiv _ _).symm q) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  let e : M.sections ≃ ((SheafOfModules.restrictScalars φ).obj M).sections :=
    Equiv.refl _
  rw [← (ad.homEquiv _ M).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert e.bijective.comp (SheafOfModules.unitHomEquiv M).bijective using 1
  ext f : 1
  dsimp
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  change f.val.app U (q.val.app U (1 : A.obj.obj U)) = f.val.app U (1 : B.obj.obj U)
  rw [hq]

private abbrev sequenceRing (W : Scheme.{t}) :
    Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      RingCat.{max u (t + 1)} :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)

private abbrev sequenceUnit (W : Scheme.{t}) : coefficientSequenceModules l E W :=
  SheafOfModules.unit (sequenceRing l E W)

private def evaluationUnit (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (integralCoefficientSheaf l E W n) ≅
      (coefficientSequenceEvaluation l E W n).obj
        (sequenceUnit l E W) := by
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  let h : SheafOfModules.unit (integralCoefficientSheaf l E W n) ⟶
      (coefficientSequenceEvaluation l E W n).obj (sequenceUnit l E W) :=
    SheafOfModules.unitToPushforwardObjUnit (F := Prod.sectR n W.ProEt)
      (R := sequenceRing l E W) φ
  have hi (U : W.ProEtᵒᵖ) : IsIso (h.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (φ.hom.app U)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ asIso (h.val.app U)) (fun {_ _} f ↦ h.val.naturality f))

private theorem evaluationUnit_hom (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientSheaf l E W n).obj.obj U) :
    (evaluationUnit l E W n).hom.val.app U a =
      (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U a := rfl

private theorem evaluationUnit_one (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (evaluationUnit l E W n).hom.val.app U
      (1 : (integralCoefficientSheaf l E W n).obj.obj U) =
      (1 : (sequenceRing l E W).obj.obj (op (n, U.unop))) := by
  exact (evaluationUnit_hom l E W n U 1).trans
    (((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U).hom.map_one)

attribute [local irreducible] evaluationUnit

private theorem unit_transition_one (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    ((coefficientSequenceTransition l E W hmn).app
      (sequenceUnit l E W)).val.app U
      (1 : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (m, U.unop))) =
      (1 : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, U.unop))) := by
  have ht := (coefficientSequenceTransition_exists l E W hmn).exists.choose_spec
    (sequenceUnit l E W) U
  have hx := congrArg (fun f ↦ f (1 :
    (coefficientSequenceCommRingSheaf l E W).obj.obj (op (m, U.unop)))) ht
  change ((coefficientSequenceTransition l E W hmn).app
      (sequenceUnit l E W)).val.app U
      (1 : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (m, U.unop))) = _ at hx
  exact hx.trans (PresheafOfModules.unit_map_one (sequenceRing l E W).obj
    ((Prod.mkHom (homOfLE hmn) (𝟙 U.unop) : (n, U.unop) ⟶ (m, U.unop))).op)

private theorem unit_module_adjoint_isIso (W : Scheme.{t})
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m) :
    IsIso (((D.ordinaryAdjunction hmn).homEquiv _ _).symm
      ((coefficientSequenceTransition l E W hmn).app
        (sequenceUnit l E W))) := by
  let em := evaluationUnit l E W m
  let en := evaluationUnit l E W n
  let q : SheafOfModules.unit (integralCoefficientSheaf l E W m) ⟶
      (normalizedDVRModuleRes l E W hmn).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) :=
    SheafOfModules.unitToPushforwardObjUnit
    (F := 𝟭 W.ProEt) (R := integralCoefficientSheaf l E W n)
    (normalizedDVRQuotient l E W hmn)
  let τ := (coefficientSequenceTransition l E W hmn).app
    (sequenceUnit l E W)
  have ht : em.hom ≫ τ = q ≫ (normalizedDVRModuleRes l E W hmn).map en.hom := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext U
    change τ.val.app U
        (em.hom.val.app U (1 : (integralCoefficientSheaf l E W m).obj.obj U)) =
      en.hom.val.app U ((normalizedDVRQuotient l E W hmn).hom.app U
        (1 : (integralCoefficientSheaf l E W m).obj.obj U))
    calc
      τ.val.app U (em.hom.val.app U
          (1 : (integralCoefficientSheaf l E W m).obj.obj U)) =
          τ.val.app U (1 : (sequenceRing l E W).obj.obj (op (m, U.unop))) :=
        congrArg (τ.val.app U) (evaluationUnit_one l E W m U)
      _ = (1 : (sequenceRing l E W).obj.obj (op (n, U.unop))) :=
        unit_transition_one l E W hmn U
      _ = en.hom.val.app U ((normalizedDVRQuotient l E W hmn).hom.app U
          (1 : (integralCoefficientSheaf l E W m).obj.obj U)) := by
        rw [((normalizedDVRQuotient l E W hmn).hom.app U).hom.map_one]
        exact (evaluationUnit_one l E W n U).symm
  have he : (D.ordinaryAdjunction hmn).homEquiv _ _
      ((coefficientFiniteQuotientExtension l E W hmn).map em.inv ≫
        ((D.ordinaryAdjunction hmn).homEquiv _ _).symm q ≫ en.hom) = τ := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [← ht, ← Category.assoc, em.inv_hom_id, Category.id_comp]
  have hi := unit_mate_isIso (normalizedDVRQuotient l E W hmn)
    (D.ordinaryAdjunction hmn) q
    (fun U ↦ (normalizedDVRQuotient l E W hmn).hom.app U |>.hom.map_one)
  change IsIso (((D.ordinaryAdjunction hmn).homEquiv
    ((coefficientSequenceEvaluation l E W m).obj (sequenceUnit l E W))
    ((coefficientSequenceEvaluation l E W n).obj (sequenceUnit l E W))).symm τ)
  rw [← he, Equiv.symm_apply_apply]
  infer_instance

/-- Scalar extension of the strict coefficient unit has invertible ordinary adjunct.
Source: Stacks Project, sites-cohomology.tex, Tag 07A6 (lemma-adjoint), and
sites-modules.tex, Tag 03EL; the unit case of quotient normalization step 7.
(blueprint: lem-pur-strict-unit-ordinary-adjoint).

Proof: the unit complex has its coefficient module in degree zero and zero in all
other degrees. Its actual horizontal map in degree zero is the ring quotient q.
The ordinary adjunct sends b tensor c to q(b)c. Multiplication identifies scalar
extension of the rank-one coefficient module with the smaller coefficient module;
its inverse sends c to 1 tensor c. Balancing proves both inverse identities.
The ordinary_unit clause fixes this adjunct for every coefficient calculus, so it
is the displayed ordinaryAlpha. In other degrees the unique zero map is invertible.
The degreewise inverses commute with the zero differentials and hence give a chain
isomorphism. The argument also covers equal levels, zero coefficient sheaves and
empty schemes and does not assume flatness of the quotient ring map. -/
theorem strictUnitOrdinaryAdjoint (W : Scheme.{t})
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m) :
    IsIso (ordinaryAlpha l E (𝟙_ (Complex l E W)) S D hmn) := by
  change IsIso (ordinaryAlpha l E
    ((HomologicalComplex.single (coefficientSequenceModules l E W) (.up ℤ) 0).obj
      (sequenceUnit l E W)) S D hmn)
  exact single_mate_isIso (coefficientSequenceEvaluation l E W m)
    (coefficientSequenceEvaluation l E W n) (D.ordinaryAdjunction hmn)
    (coefficientSequenceTransition l E W hmn) (sequenceUnit l E W)
    (unit_module_adjoint_isIso l E W S D hmn)

end WeilConjectures.StrictQuotient
