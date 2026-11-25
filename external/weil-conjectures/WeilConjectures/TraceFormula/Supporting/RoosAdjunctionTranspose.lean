/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Strict compatible families and their Roos adjuncts

Source: Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-roos-adjunction-transpose)
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

private theorem inclusion_natural
    {C D : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ} (f : C ⟶ D) :
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ _).mapHomologicalComplex
        (.up ℤ)).map f ≫ integralComparisonLimitToRoos l E X D =
      integralComparisonLimitToRoos l E X C ≫
        integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) := by
  let F : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  have hc := (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose_spec
  have hd := (integralComparisonLimitToRoos_existsUnique l E X D).exists.choose_spec
  change (∀ n, integralComparisonLimitToRoos l E X C ≫ _ ≫ _ = _) ∧ _ at hc
  change (∀ n, integralComparisonLimitToRoos l E X D ≫ _ ≫ _ = _) ∧ _ at hd
  have hfirst : integralOperationsRoosFunctor.map (F.map f) ≫
      CochainComplex.mappingCocone.fst (scalarRoosBoundary D.asFunctor) =
      CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
        Limits.Pi.map (fun n : ℕ ↦ (F.map f).app (op n)) :=
    (IntegralAmbient.roosMap_coordinates (F.map f)).1
  have hc2 (i : ℤ) : (integralComparisonLimitToRoos l E X C).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v
        i (i - 1) (by omega) = 0 := hc.2 i (i - 1) (by omega)
  have hd2 (i : ℤ) : (integralComparisonLimitToRoos l E X D).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary D.asFunctor)).v
        i (i - 1) (by omega) = 0 := hd.2 i (i - 1) (by omega)
  have hsecond (i : ℤ) : (integralOperationsRoosFunctor.map (F.map f)).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary D.asFunctor)).v
        i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v
        i (i - 1) (by omega) ≫
          (Limits.Pi.map (fun n : ℕ ↦ (F.map f).app (op n))).f (i - 1) :=
    (IntegralAmbient.roosMap_coordinates (F.map f)).2 i (i - 1) (by omega)
  apply cone_ext (scalarRoosBoundary D.asFunctor)
  · simp only [Category.assoc]
    rw [hfirst]
    apply Pi.hom_ext
    intro n
    calc
      _ = ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ _).mapHomologicalComplex
            (.up ℤ)).map f ≫
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app D := by
        simp only [Category.assoc]
        rw [hd.1 n]
      _ = (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C ≫
          (F.map f).app (op n) :=
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).naturality f
      _ = _ := by
        have hπ : Limits.Pi.map (fun m : ℕ ↦ (F.map f).app (op m)) ≫
            Pi.π (fun m ↦ D.asFunctor.obj (op m)) n =
            Pi.π (fun m ↦ C.asFunctor.obj (op m)) n ≫ (F.map f).app (op n) :=
          Limits.Pi.map_π (f := fun m ↦ C.asFunctor.obj (op m))
            (g := fun m ↦ D.asFunctor.obj (op m)) (fun m ↦ (F.map f).app (op m)) n
        simp only [Category.assoc]
        rw [hπ]
        simpa only [Category.assoc] using
          (congrArg (fun z ↦ z ≫ (F.map f).app (op n)) (hc.1 n)).symm
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [hd2 i, comp_zero, hsecond i, ← Category.assoc, hc2 i, zero_comp]

private theorem derivedUnit_comparison
    (ρ : IntegralComparisonRoosModel l E X)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ _).rightDerivedFunctorUnitQ C ≫
        ρ.comparison.hom.app C =
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X C) := by
  let G := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X)
  let F : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  obtain ⟨I, hi, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  let := hi
  let := hf
  have hQ : IsIso (DerivedCategory.Q.map f) := inferInstance
  have hG : IsIso (G.rightDerivedFunctor.map (DerivedCategory.Q.map f)) := inferInstance
  have hn : G.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
      ρ.comparison.hom.app I = ρ.comparison.hom.app C ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map (F.map f)) :=
    ρ.comparison.hom.naturality f
  have hiso : IsIso (DerivedCategory.Q.map (integralOperationsRoosFunctor.map (F.map f))) :=
    IsIso.of_isIso_fac_left hn.symm
  change G.rightDerivedFunctorUnitQ C ≫ ρ.comparison.hom.app C = _
  have hI : G.rightDerivedFunctorUnitQ I ≫ ρ.comparison.hom.app I =
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I) := by
    rw [ρ.computes I, G.rightDerivedFunctorUnitQ_eq I]
    exact Iso.inv_hom_id_assoc _ _
  apply (cancel_mono (DerivedCategory.Q.map
    (integralOperationsRoosFunctor.map (F.map f)))).1
  calc
    _ = G.rightDerivedFunctorUnitQ C ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        ρ.comparison.hom.app I := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ G.rightDerivedFunctorUnitQ C ≫ z) hn.symm
    _ = DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫
        G.rightDerivedFunctorUnitQ I ≫ ρ.comparison.hom.app I := by
      rw [G.rightDerivedFunctorUnitQ_naturality_assoc f]
    _ = DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫
        DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I) := by
      rw [hI]
    _ = _ := by
      rw [← Functor.map_comp, inclusion_natural l E X f, Functor.map_comp]

/-- The normalized derived-limit comparison sends the adjunct of an entire strict
compatible family to its ordinary limit lift followed by the zero-shifted Roos inclusion.
Source: Stacks 06YY and 0941; scalar-model-unit proof step 3.
(blueprint: lem-trf-roos-adjunction-transpose).

Proof: transpose b through the ordinary constant/limit adjunction to obtain a map a
into the termwise limit. The derived adjunction formula identifies the adjunct of
Q(b), preceded by the exact constant-functor comparison, with Q(a) followed by the
right-derived limit unit. On K-injective towers the normalization of rho identifies
that derived unit followed by rho with Q of the ordinary limit-to-Roos inclusion.
For a general tower choose a simultaneous K-injective resolution. Naturality of the
right-derived unit, rho and the limit-to-Roos inclusion transports this identity
back along the resolution; its Roos map is a quasi-isomorphism because rho is a
natural isomorphism. Cancel it. Composing with Q(a) proves the formula. This uses
entire strict families and both cone coordinates, and imposes no boundedness. -/
theorem integralComparisonRoosTranspose
    (ρ : IntegralComparisonRoosModel l E X)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
      ℕᵒᵖ ⥤ scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).obj P ⟶ C) :
    (integralComparisonConstantAdjunction l E X).homEquiv _ _
        ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
          ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map b) ≫ ρ.comparison.hom.app C =
      DerivedCategory.Q.map
        (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).mapHomologicalComplex
          (.up ℤ)).homEquiv P C b ≫ integralComparisonLimitToRoos l E X C) := by
  let G := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X)
  let adj := constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)
  let a := (adj.mapHomologicalComplex (.up ℤ)).homEquiv P C b
  have ht := derived_transpose_ordinary adj P C a
  rw [Equiv.symm_apply_apply] at ht
  have he : (integralComparisonConstantAdjunction l E X).homEquiv _ _
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map b) = DerivedCategory.Q.map a ≫ G.rightDerivedFunctorUnitQ C := by
    apply ((integralComparisonConstantAdjunction l E X).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    exact ht.symm
  rw [he, Category.assoc, derivedUnit_comparison l E X ρ C, ← Functor.map_comp]

end WeilConjectures
