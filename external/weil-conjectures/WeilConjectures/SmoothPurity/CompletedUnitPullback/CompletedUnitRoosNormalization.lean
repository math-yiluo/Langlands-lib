/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PrimitiveCounit.PrimitiveCounitComparisonModels
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Comparison of the two normalized strict Roos realizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback
attribute [local implicit_reducible] PrimitiveCounit.RoosComparison
  coefficientConstantTowerLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem primitive_roos_inverse_kinjective (W : Scheme.{u})
    (ρ : PrimitiveCounit.RoosRealization l E W)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective] :
    ρ.comparison.inv.app I =
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).hom ≫
      DerivedCategory.Q.map ((PrimitiveCounit.limitComplexIso l E W I).inv ≫ roosι I) := by
  obtain ⟨ι, hι, hi⟩ := ρ.resolution I I (𝟙 I)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hi
  have he : ρ.comparison.app I =
      ι.symm ≪≫ DerivedCategory.Q.mapIso (PrimitiveCounit.limitComplexIso l E W I) ≪≫
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
          I).symm := by
    apply Iso.ext
    exact (Category.comp_id _).symm.trans hi
  have hinv := congrArg Iso.inv he
  simpa only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    hι, CategoryTheory.Functor.map_comp, Category.assoc] using hinv

private theorem mappingCocone_hom_ext {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L)
    {f g : M ⟶ CochainComplex.mappingCocone φ}
    (hfst : f ≫ CochainComplex.mappingCocone.fst φ =
      g ≫ CochainComplex.mappingCocone.fst φ)
    (hsnd : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun a ↦ a.f i) hfst
  have he := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by rw [he]
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [show f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
        g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i from h, hsnd i]
    _ = g.f i := by rw [he, Category.comp_id]

private theorem generic_roos_unit
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (h : Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) ≫ roosU I = 0) :
    (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).inv ≫ roosι I =
      roosLift (Pi.lift (fun n : ℕ ↦
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) h := by
  apply mappingCocone_hom_ext
  · simp only [Category.assoc, roosι, roosLift,
      CochainComplex.mappingCocone.lift_fst]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_comp_π]
    exact limit.isoLimitCone_inv_π _ _
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc, roosι, roosLift,
      CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v, comp_zero]

private theorem generic_roos_augmentation_zero
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) ≫ roosU I = 0 := by
  have hp : Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) =
      (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).inv ≫
          Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_comp_π]
    erw [Pi.lift_comp_π]
    exact (limit.isoLimitCone_inv_π (F := I.asFunctor)
      ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
        HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩ (op n)).symm
  have hz : Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) ≫ roosU I = 0 := by
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, limit.w]
  rw [hp, Category.assoc, hz, comp_zero]

attribute [local implicit_reducible] pullbackTensorConstantLimit
  pullbackTensorRoosUnit pullbackTensorRoosAugmentation PrimitiveCounit.roosBridge
  PrimitiveCounit.limitComplexIso integralOperationsTowerStep integralOperationsRoos

private theorem primitive_roos_unit (W : Scheme.{u})
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    (PrimitiveCounit.limitComplexIso l E W I).inv ≫ roosι I =
      pullbackTensorRoosUnit l E W I ≫ (PrimitiveCounit.roosBridge l E W I).hom := by
  have hz : Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) ≫ roosU I = 0 :=
    generic_roos_augmentation_zero I
  change (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).inv ≫ roosι I =
    roosLift (Pi.lift (fun n : ℕ ↦
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) hz ≫ 𝟙 _
  exact (generic_roos_unit I hz).trans (Category.comp_id _).symm

private theorem cofiberMap_eq_coneMap
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : a ≫ g = f ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map f g a b h.symm := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, CochainComplex.HomComplex.Cochain.comp_v,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst,
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inr]

private def generic_roos_bridge {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ≅ roosF (A := A) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp only [CategoryTheory.Functor.comp_map, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Iso.refl_hom,
      integralOperationsRoosFunctor, integralOperationsRoosMap]
    rw [cofiberMap_eq_coneMap]
    simp only [Category.id_comp, Category.comp_id]
    rfl)

private theorem primitive_roos_inverse_kinjective_eq (W : Scheme.{u})
    (ρ : PrimitiveCounit.RoosRealization l E W)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective] :
    ρ.comparison.inv.app I =
      (pullbackTensorRoosModel l E W).hom.app I ≫
        DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E W I).hom := by
  have hn := (pullbackTensorRoosModel_existsUnique l E W).exists.choose_spec I
  change (pullbackTensorRoosModel l E W).hom.app I = _ at hn
  rw [primitive_roos_inverse_kinjective l E W ρ I, primitive_roos_unit l E W I,
    CategoryTheory.Functor.map_comp]
  simpa only [pullbackTensorConstantLimit, Category.assoc] using
    congrArg (fun a ↦ a ≫
      DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E W I).hom) hn.symm

private theorem generic_iso_eq_on_kinjective
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [Category B]
    (H : DerivedCategory A ⥤ B) (G : CochainComplex A ℤ ⥤ B)
    (e e' : DerivedCategory.Q ⋙ H ≅ G)
    (h : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], e.hom.app I = e'.hom.app I) :
    e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  have : I.IsKInjective := hI
  have : QuasiIso q := hq
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance
  have : IsIso ((DerivedCategory.Q ⋙ H).map q) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : IsIso (G.map q) := (NatIso.isIso_map_iff e q).1 inferInstance
  apply (cancel_mono (G.map q)).1
  rw [← e.hom.naturality q, ← e'.hom.naturality q, h I]

attribute [local implicit_reducible] pullbackTensorTowerQ

/-- The primitive resolution-normalized comparison is the tensor Roos comparison
followed by the actual strict bridge between the two shifted cone presentations.
Source: Stacks 0941, proof of lemma-derived-limit-is-ok.
(blueprint: lem-pur-completed-unit-roos-normalization).

Proof: specialize the primitive resolution equation to the identity of a K-injective
complex and invert it. Its resulting chain map is the termwise-limit isomorphism
followed by roosι. The two-coordinate mapping-cocone identity identifies this with
the tensor augmentation: its unshifted coordinate is the family of limit projections
and its shifted coordinate is zero. These are precisely the defining normalization
of pullbackTensorRoosModel. The strict bridge is natural because its maps are the
same diagonal product maps under the two definitions of mapping-cone maps. Finally,
resolve an arbitrary complex by a K-injective one. Both natural comparisons invert
that quasi-isomorphism, so naturality and cancellation extend equality to every
complex. No faithfulness of the individual derived evaluations is used. -/
theorem primitive_roos_inverse_eq (W : Scheme.{u})
    (ρ : PrimitiveCounit.RoosRealization l E W)
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ρ.comparison.inv.app Z =
      (pullbackTensorRoosModel l E W).hom.app Z ≫
        DerivedCategory.Q.map (PrimitiveCounit.roosBridge l E W Z).hom := by
  let e : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W ≅
      roosF ⋙ DerivedCategory.Q :=
    pullbackTensorRoosModel l E W ≪≫
      Functor.isoWhiskerRight generic_roos_bridge DerivedCategory.Q
  have he : e = ρ.comparison.symm := by
    apply generic_iso_eq_on_kinjective
    intro I hI
    exact (primitive_roos_inverse_kinjective_eq l E W ρ I).symm
  have h := congrArg (fun a ↦ a.hom.app Z) he
  exact h.symm

end WeilConjectures.CompletedUnitPullback
