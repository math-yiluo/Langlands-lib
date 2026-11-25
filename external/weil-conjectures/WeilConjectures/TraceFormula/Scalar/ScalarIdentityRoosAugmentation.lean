/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Multiplication and the strict scalar identity augmentation

Source: Bhatt--Scholze, Definition 3.4.10; Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-scalar-identity-roos-augmentation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u})

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

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel
  completedIntegralCoefficientSheafUnrestricted

private theorem restriction_apply
    {M N : coefficientSequenceModules l E X} (f : M ⟶ N)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U)
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X N n U (f.val.app (op (n, U.unop)) x) := by
  have h : HEq
      (fun y ↦ ((((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U) y)
      (fun y ↦ f.val.app (op (n, U.unop)) y) := by
    simpa only [coefficientSequenceRestriction] using
      (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 f n U
  have hx : HEq (integralComparisonRestrictedSection l E X M n U x) x := cast_heq _ x
  have hy : HEq
      (integralComparisonRestrictedSection l E X N n U (f.val.app (op (n, U.unop)) x))
      (f.val.app (op (n, U.unop)) x) := cast_heq _ _
  have hh : HEq
      (((((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U)
        (integralComparisonRestrictedSection l E X M n U x))
      (f.val.app (op (n, U.unop)) x) :=
    dcongr_heq hx (fun _ _ _ ↦ integralComparisonRestrictedSectionType l E X N n U)
      (fun _ _ ↦ h)
  exact eq_of_heq (hh.trans hy.symm)

private theorem multiplication_inv_apply
    (M : coefficientSequenceModules l E X) (V : (ℕ × X.ProEt)ᵒᵖ)
    (x : M.val.obj V) :
    ((integralComparisonSequenceScalarUnit l E X).inv.app M).val.app V x =
      integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) X M V 1 x := by
  let e := (integralComparisonSequenceScalarUnit l E X).app M
  have hinj : Function.Injective (fun y ↦ e.hom.val.app V y) := by
    intro y z h
    have hi (w) : e.inv.val.app V (e.hom.val.app V w) = w :=
      congrArg (fun k ↦ k.val.app V w) e.hom_inv_id
    exact (hi y).symm.trans ((congrArg (fun w ↦ e.inv.val.app V w) h).trans (hi z))
  apply hinj
  have hi : e.hom.val.app V (e.inv.val.app V x) = x :=
    congrArg (fun k ↦ k.val.app V x) e.inv_hom_id
  change e.hom.val.app V (e.inv.val.app V x) =
    e.hom.val.app V (integralComparisonSequenceTensorSection l E E
      (AlgHom.id ℚ_[l] E) X M V 1 x)
  rw [hi]
  have hu := (integralComparisonSequenceScalarUnit_existsUnique l E X).exists.choose_spec
    M V 1 x
  simpa only [e, integralComparisonSequenceScalarUnit, Iso.app_hom, one_smul] using hu.symm

/-- Inserting the scalar one into a strict quotient family and applying its
normalized tower identification gives the specified scalar identity cone augmentation.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 06YY and 0941;
scalar-model-unit proof steps 2--3.
(blueprint: lem-trf-scalar-identity-roos-augmentation).

Proof: the inverse ordinary scalar unitor inserts 1 tensor x, since multiplication
and insertion are inverse on sheafified tensor generators. In each quotient the
section formula for b, followed by this insertion and q, is precisely the scalar
tensor generator 1 tensor x by hq with s=1. The ordinary adjunction transpose has
these components as its limit projections. The limit-to-Roos map has that limit
tuple in its unshifted coordinate and zero in its shifted coordinate. Roos(q)
acts by the product of q in both coordinates and has zero off-diagonal entries.
Consequently the composite has the same unshifted components and zero shifted
component as completedScalarIdentityUnit. Product and biproduct extensionality
identify the chain maps. The computation respects all quotient transitions and
works also for the zero complex; it uses no derived-category faithfulness. -/
theorem scalarIdentityRoosAugmentation
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C)
    (hb : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((b.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E X (C.X i) n U
          (integralComparisonSequenceSection l E X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))))
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E E
          (AlgHom.id ℚ_[l] E) X).E.mapHomologicalComplex (.up ℤ)).obj C)).asFunctor ≅
      (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) X).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l E X).obj.obj (op (n, U.unop)))
        (x : (P.X i).val.obj U),
      ((q.hom.app (op n)).f i).val.app U
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).E.obj
            (C.X i)) n U
          (integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) X
            (C.X i) (op (n, U.unop)) s
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))))) =
        integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X n (P.X i) U s x) :
    ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).mapHomologicalComplex
        (.up ℤ)).homEquiv P _
      (b ≫ ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X)
          (.up ℤ)).inv.app C)) ≫
      integralComparisonLimitToRoos l E X _ ≫
      integralOperationsRoosFunctor.map q.hom =
        (completedScalarIdentityUnit l E X).app P := by
  let R := coefficientSequenceRestriction l E X
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let m := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let μ := NatIso.mapHomologicalComplex (integralComparisonSequenceScalarUnit l E X) (.up ℤ)
  let D := (m.E.mapHomologicalComplex (.up ℤ)).obj C
  let T := Rc.obj D
  let c := b ≫ Rc.map (μ.inv.app C)
  let adj := (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).mapHomologicalComplex
    (.up ℤ)
  let a := adj.homEquiv P T c
  have ha (n : ℕ) (i : ℤ) :
      a.f i ≫ limit.π (T.X i) (op n) = (c.f i).app (op n) := by
    have h := (adj.homEquiv P T).symm_apply_apply c
    rw [Adjunction.homEquiv_counit] at h
    exact congrArg (fun f ↦ (f.f i).app (op n)) h
  have hi := (integralComparisonLimitToRoos_existsUnique l E X T).exists.choose_spec
  have hη := (completedScalarIdentityUnit_existsUnique l E X).exists.choose_spec
  change (∀ n, integralComparisonLimitToRoos l E X T ≫ _ ≫ _ = _) ∧ _ at hi
  change (∀ P i n U x, (((completedScalarIdentityUnit l E X).app P).f i ≫ _ ≫ _).val.app U
    x = _) ∧ _ at hη
  let δ := completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) X P
  have hfirst : integralOperationsRoosFunctor.map q.hom ≫
      CochainComplex.mappingCocone.fst δ =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary T.asFunctor) ≫
        Limits.Pi.map (fun n : ℕ ↦ q.hom.app (op n)) :=
    (IntegralAmbient.roosMap_coordinates q.hom).1
  have hi2 (i : ℤ) : (integralComparisonLimitToRoos l E X T).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary T.asFunctor)).v
        i (i - 1) (by omega) = 0 := hi.2 i (i - 1) (by omega)
  have hη2 (i : ℤ) : ((completedScalarIdentityUnit l E X).app P).f i ≫
      (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) = 0 := hη.2 P i
  have hsecond (i : ℤ) : (integralOperationsRoosFunctor.map q.hom).f i ≫
      (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary T.asFunctor)).v
        i (i - 1) (by omega) ≫ (Limits.Pi.map (fun n : ℕ ↦ q.hom.app (op n))).f (i - 1) :=
    (IntegralAmbient.roosMap_coordinates q.hom).2 i (i - 1) (by omega)
  change a ≫ integralComparisonLimitToRoos l E X T ≫
    integralOperationsRoosFunctor.map q.hom = (completedScalarIdentityUnit l E X).app P
  apply cone_ext δ
  · simp only [Category.assoc]
    rw [hfirst]
    apply Pi.hom_ext
    intro n
    calc
      _ = (a ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T) ≫
          q.hom.app (op n) := by
        have hπ : Limits.Pi.map (fun m : ℕ ↦ q.hom.app (op m)) ≫
            Pi.π (fun m ↦ ((integralScalarTowerFunctor l E E
              (AlgHom.id ℚ_[l] E) X).obj P).obj (op m)) n =
            Pi.π (fun m ↦ T.asFunctor.obj (op m)) n ≫ q.hom.app (op n) :=
          Limits.Pi.map_π (f := fun m ↦ T.asFunctor.obj (op m))
            (fun m ↦ q.hom.app (op m)) n
        simp only [Category.assoc]
        rw [hπ]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ a ≫ z ≫ q.hom.app (op n)) (hi.1 n)
      _ = _ := by
        ext i U x
        change ((q.hom.app (op n)).f i).val.app U
          ((a.f i ≫ limit.π (T.X i) (op n)).val.app U x) = _
        rw [ha]
        dsimp only [c, HomologicalComplex.comp_f, NatTrans.comp_app,
          Rc, Functor.mapHomologicalComplex_map_f]
        change ((q.hom.app (op n)).f i).val.app U
          ((((R.map ((integralComparisonSequenceScalarUnit l E X).inv.app
              (C.X i))).app (op n)).val.app U)
            ((((b.f i).app (op n)).val.app U) x)) = _
        rw [hb]
        let y : (C.X i).val.obj (op (n, U.unop)) :=
          integralComparisonSequenceSection l E X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x))
        have hr := restriction_apply l E X
          ((integralComparisonSequenceScalarUnit l E X).inv.app (C.X i)) n U y
        have hm := multiplication_inv_apply l E X (C.X i) (op (n, U.unop)) y
        have hrq := congrArg (fun z ↦ ((q.hom.app (op n)).f i).val.app U z) hr
        have hmq := congrArg (fun z ↦ ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l E X (D.X i) n U z)) hm
        exact hrq.trans (hmq.trans ((hq n i U 1 x).trans (hη.1 P i n U x).symm))
  · intro i
    calc
      _ = a.f i ≫ ((integralComparisonLimitToRoos l E X T).f i ≫
          (CochainComplex.mappingCocone.snd (scalarRoosBoundary T.asFunctor)).v
            i (i - 1) (by omega)) ≫
          (Limits.Pi.map (fun n : ℕ ↦ q.hom.app (op n))).f (i - 1) := by
        simp only [HomologicalComplex.comp_f, Category.assoc, hsecond i]
      _ = 0 := by rw [hi2 i, zero_comp, comp_zero]
      _ = _ := (hη2 i).symm

end WeilConjectures
