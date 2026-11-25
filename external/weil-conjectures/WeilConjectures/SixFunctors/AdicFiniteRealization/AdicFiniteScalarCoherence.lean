/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteRawScalarComparison
import all WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationScalarCoherence

/-! # Scalar coherence of finite adic realizations

Source: BS Proposition 6.8.14(2); quotient comparison and balanced tensor normalization.
(blueprint: lem-sf-adic-finite-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.ScalarLocalization.category
  CategoryTheory.ScalarLocalization.composition
  HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum
  AlgebraicGeometry.Scheme.pbcAmbientScalarUnit
  AlgebraicGeometry.Scheme.pbcAmbientScalarAssociator
  AlgebraicGeometry.Scheme.pbcScalarIntegralComparison
  AlgebraicGeometry.Scheme.pbcScalarAssociator
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
  AlgebraicGeometry.Scheme.pbcIntegralScalarUnit

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

@[irreducible] private def coefficient (C : Core l T)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :=
  rationalScalarCanonical l (pbcFiniteField.{u} l (PadicAlgCl l) E)
    (pbcFiniteField.{u} l (PadicAlgCl l) F) (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
    T (C.realization E) (C.realization F)

private def theta (C : Core l T)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient l T C h).coefficient :=
  Functor.isoWhiskerRight (pbcFiniteRawScalarComparison l (PadicAlgCl l) T h)
    (C.realization F).J ≪≫ (coefficient l T C h).theta

private theorem completed_square (C : Core l T)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :
    pbcCompletedScalarMap l (PadicAlgCl l) T h ≫
        rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F) =
      rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
        (coefficient l T C h).coefficient := by
  rw [rawScalar_coefficientMap l (PadicAlgCl l) T h]
  exact (coefficient l T C h).coefficient_square

private theorem map_heq {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) {X Y Y' : A} (f : X ⟶ Y) (f' : X ⟶ Y')
    (e : Y = Y') (hf : HEq f f') : HEq (J.map f) (J.map f') := by
  subst Y'
  cases hf
  rfl

omit [AlgebraicGeometry.IsNoetherian T] dT in
private theorem normalization_heq
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (f f' : R ⟶ S) (g : S ⟶ B) (c : R ⟶ B)
    (h : f ≫ g = c) (h' : f' ≫ g = c) (e : f = f')
    (K : DerivedCategory (pbcModules T R)) :
    HEq (pbcReductionNormalization f g c h K).hom
      (pbcReductionNormalization f' g c h' K).hom := by
  subst f'
  rfl

private theorem integral (C : Core l T) :
    integralNormalization l T C (coefficient l T C) (theta l T C)
      (completed_square l T C) := by
  unfold integralNormalization
  intro E F h K
  have hc := (pbcFiniteRawScalarComparison_existsUnique l (PadicAlgCl l) T h).exists.choose_spec K
  have hi := (coefficient l T C h).integral_normalization K
  have ht := rawScalar_integralTensor l (PadicAlgCl l) T h
  have ho := congrArg (fun I ↦
    (pbcStageLocalization l (PadicAlgCl l) T F).obj (I.obj K)) ht.symm
  simp only [theta, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc]
  rw [hi]
  apply eq_of_heq
  refine heq_comp rfl (congrArg (C.realization F).J.obj ho) rfl ?_ ?_
  · exact map_heq (C.realization F).J _ _ ho hc
  · refine (eqToHom_comp_heq (C := DerivedCategory (pbcModules T
      (rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) F)))) _ _).trans ?_
    refine HEq.trans ?_ (eqToHom_comp_heq (C := DerivedCategory (pbcModules T
      (rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) F)))) _ _).symm
    exact normalization_heq T _ _ _ _ _ _
      (rawScalar_coefficientMap l (PadicAlgCl l) T h).symm K.obj

private theorem inclusion_comp
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G) :
    (pbcFiniteFieldInclusion.{u} l (PadicAlgCl l) k).comp
        (pbcFiniteFieldInclusion.{u} l (PadicAlgCl l) h) =
      pbcFiniteFieldInclusion.{u} l (PadicAlgCl l) (h.trans k) := by
  ext x
  change (Shrink.algEquiv (Padic l) G.val).symm
      (IntermediateField.inclusion k
        ((Shrink.algEquiv (Padic l) F.val)
          ((Shrink.algEquiv (Padic l) F.val).symm
            (IntermediateField.inclusion h ((Shrink.algEquiv (Padic l) E.val) x))))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

private theorem inclusion_id (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    pbcFiniteFieldInclusion.{u} l (PadicAlgCl l) (le_refl E) =
      AlgHom.id (Padic l) (pbcFiniteField.{u} l (PadicAlgCl l) E) := by
  ext x
  exact (Shrink.algEquiv (Padic l) E.val).symm_apply_apply x

omit [AlgebraicGeometry.IsNoetherian T] dT in
private theorem normalization_heq_three
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (f f' : R ⟶ S) (g g' : S ⟶ B) (c c' : R ⟶ B)
    (h : f ≫ g = c) (h' : f' ≫ g' = c') (ef : f = f') (eg : g = g') (ec : c = c')
    (K : DerivedCategory (pbcModules T R)) :
    HEq (pbcReductionNormalization f g c h K).hom
      (pbcReductionNormalization f' g' c' h' K).hom := by
  subst f'
  subst g'
  subst c'
  rfl

omit dT iT in
private theorem ambient_associator
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l (PadicAlgCl l) T E) :
    HEq ((pbcAmbientScalarAssociator l (PadicAlgCl l) T h k).hom.app K.obj)
      ((pbcAmbientScalarComp l (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteField.{u} l (PadicAlgCl l) F)
        (pbcFiniteField.{u} l (PadicAlgCl l) G)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) k) T).hom.app K.obj) := by
  rw [show (pbcAmbientScalarAssociator l (PadicAlgCl l) T h k).hom.app K.obj =
    (pbcReductionNormalization (pbcCompletedScalarMap l (PadicAlgCl l) T h)
      (pbcCompletedScalarMap l (PadicAlgCl l) T k)
      (pbcCompletedScalarMap l (PadicAlgCl l) T (h.trans k))
      (pbcCompletedScalarMap_comp l (PadicAlgCl l) T h k) K.obj).hom from
      by
        unfold pbcAmbientScalarAssociator
        exact rationalScalarNormalizationIso_hom _ _ _ _ K.obj]
  unfold pbcAmbientScalarComp
  dsimp only [NatIso.ofComponents_hom_app]
  apply normalization_heq_three T
  · exact rawScalar_coefficientMap l (PadicAlgCl l) T h
  · exact rawScalar_coefficientMap l (PadicAlgCl l) T k
  · rw [inclusion_comp l h k]
    exact rawScalar_coefficientMap l (PadicAlgCl l) T (h.trans k)

private theorem map_heq_both {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) {X Y X' Y' : A} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (ex : X = X') (ey : Y = Y') (hf : HEq f f') : HEq (J.map f) (J.map f') := by
  subst X'
  subst Y'
  cases hf
  rfl

private theorem full_hom_heq {A : Type*} [Category A] (P : ObjectProperty A)
    {X Y X' Y' : P.FullSubcategory} (f : X ⟶ Y) (g : X' ⟶ Y')
    (ex : X.obj = X'.obj) (ey : Y.obj = Y'.obj) (hf : HEq f.hom g.hom) : HEq f g := by
  have hx : X = X' := ObjectProperty.FullSubcategory.ext ex
  have hy : Y = Y' := ObjectProperty.FullSubcategory.ext ey
  subst X'
  subst Y'
  exact heq_of_eq (ObjectProperty.hom_ext P (eq_of_heq hf))

private theorem integral_associator
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l (PadicAlgCl l) T E) :
    HEq ((pbcStageLocalization l (PadicAlgCl l) T G).map
      ((pbcIntegralScalarAssociator l (PadicAlgCl l) T dT.out iT.out h k).hom.app K))
      ((pbcRationalScalarComp l (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteField.{u} l (PadicAlgCl l) F)
        (pbcFiniteField.{u} l (PadicAlgCl l) G)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) k) T dT.out iT.out).hom.app
        ((pbcStageLocalization l (PadicAlgCl l) T E).obj K)) := by
  have hx := rawScalar_integralTensor l (PadicAlgCl l) T h
  have hy := rawScalar_integralTensor l (PadicAlgCl l) T k
  have hz : pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out (h.trans k) =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteField.{u} l (PadicAlgCl l) G)
        ((pbcFiniteFieldInclusion l (PadicAlgCl l) k).comp
          (pbcFiniteFieldInclusion l (PadicAlgCl l) h)) T dT.out iT.out := by
    rw [inclusion_comp l h k]
    exact rawScalar_integralTensor l (PadicAlgCl l) T (h.trans k)
  have hs := congrArg (fun (I : pbcIntegralStage l (PadicAlgCl l) T E ⥤
      pbcIntegralStage l (PadicAlgCl l) T F) ↦
    (pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out k).obj (I.obj K)) hx
  have hs' := congrArg (fun I ↦ I.obj
    ((pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T dT.out iT.out).obj K)) hy
  have ht := congrArg (fun I ↦ I.obj K) hz
  unfold pbcRationalScalarComp pbcRationalScalarCompComponent
  apply map_heq_both _ _ _ (hs.trans hs') ht
  apply full_hom_heq _ _ _ (congrArg (·.obj) (hs.trans hs')) (congrArg (·.obj) ht)
  rw [pbcIntegralScalarAssociator_hom]
  exact ambient_associator l T h k K

private theorem raw_obj
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F)
    (K : pbcIntegralStage l (PadicAlgCl l) T E) :
    (pbcRationalScalarExtension l (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T dT.out iT.out).obj
        ((pbcStageLocalization l (PadicAlgCl l) T E).obj K) =
      (pbcStageLocalization l (PadicAlgCl l) T F).obj
        ((pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out h).obj K) := by
  exact congrArg (fun (I : pbcIntegralStage l (PadicAlgCl l) T E ⥤
      pbcIntegralStage l (PadicAlgCl l) T F) ↦
    (pbcStageLocalization l (PadicAlgCl l) T F).obj (I.obj K))
    (rawScalar_integralTensor l (PadicAlgCl l) T h).symm

private theorem app_heq {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (a : F ⟶ G) {X Y : A} (h : X = Y) : HEq (a.app X) (a.app Y) := by
  subst Y
  rfl

private theorem raw_coherence
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G)
    (K : pbcStageCategory l (PadicAlgCl l) T E) :
    HEq ((pbcScalarAssociator l (PadicAlgCl l) T dT.out iT.out h k).hom.app K ≫
      (pbcFiniteRawScalarComparison l (PadicAlgCl l) T (h.trans k)).hom.app K)
      ((pbcFiniteRawScalarComparison l (PadicAlgCl l) T k).hom.app
        ((pbcScalarExtension l (PadicAlgCl l) T dT.out iT.out h).obj K) ≫
      (pbcRationalScalarExtension l (pbcFiniteField.{u} l (PadicAlgCl l) F)
        (pbcFiniteField.{u} l (PadicAlgCl l) G)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) k) T dT.out iT.out).map
          ((pbcFiniteRawScalarComparison l (PadicAlgCl l) T h).hom.app K) ≫
      (pbcRationalScalarComp l (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteField.{u} l (PadicAlgCl l) F)
        (pbcFiniteField.{u} l (PadicAlgCl l) G)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) k) T dT.out iT.out).hom.app K) := by
  obtain ⟨K⟩ := K
  let Q := pbcStageLocalization l (PadicAlgCl l) T E
  let QG := pbcStageLocalization l (PadicAlgCl l) T G
  let Ih := pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out h
  let Ik := pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out k
  let Rk := pbcRationalScalarExtension l (pbcFiniteField.{u} l (PadicAlgCl l) F)
    (pbcFiniteField.{u} l (PadicAlgCl l) G)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) k) T dT.out iT.out
  let Sk := pbcScalarExtension l (PadicAlgCl l) T dT.out iT.out k
  let ch := pbcFiniteRawScalarComparison l (PadicAlgCl l) T h
  let ck := pbcFiniteRawScalarComparison l (PadicAlgCl l) T k
  let cih := pbcScalarIntegralComparison l (PadicAlgCl l) T dT.out iT.out h
  let cik := pbcScalarIntegralComparison l (PadicAlgCl l) T dT.out iT.out k
  let a := pbcIntegralScalarAssociator l (PadicAlgCl l) T dT.out iT.out h k
  have hh := (pbcFiniteRawScalarComparison_existsUnique l (PadicAlgCl l) T h).exists.choose_spec K
  have hk := (pbcFiniteRawScalarComparison_existsUnique l (PadicAlgCl l) T k).exists.choose_spec
    (Ih.obj K)
  have hd := (pbcFiniteRawScalarComparison_existsUnique l (PadicAlgCl l) T
    (h.trans k)).exists.choose_spec K
  have ho := raw_obj l T h K
  have ho' := (congrArg Rk.obj ho).trans (raw_obj l T k (Ih.obj K))
  have ht := (congrArg (fun i ↦
    (pbcRationalScalarExtension l (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) G) i T dT.out iT.out).obj (Q.obj K))
        (inclusion_comp l h k)).trans (raw_obj l T (h.trans k) K)
  have hl : HEq
      ((pbcScalarAssociator l (PadicAlgCl l) T dT.out iT.out h k).hom.app (Q.obj K) ≫
        (pbcFiniteRawScalarComparison l (PadicAlgCl l) T (h.trans k)).hom.app (Q.obj K))
      (Sk.map (cih.hom.app K) ≫ cik.hom.app (Ih.obj K) ≫ QG.map (a.hom.app K)) := by
    exact (heq_comp rfl rfl (raw_obj l T (h.trans k) K) HEq.rfl hd).trans
      (heq_of_eq (pbcScalarAssociator_normalization l (PadicAlgCl l) T
        dT.out iT.out h k K))
  apply hl.trans
  symm
  have hn := ck.hom.naturality (ch.hom.app (Q.obj K))
  refine (heq_of_eq ((reassoc_of% hn) _).symm).trans ?_
  refine heq_comp rfl (congrArg Sk.obj ho) ht ?_ ?_
  · exact map_heq Sk _ _ ho hh
  · refine heq_comp (congrArg Sk.obj ho) ho' ht ?_ ?_
    · exact (app_heq ck.hom ho).trans hk
    · exact (integral_associator l T h k K).symm

private theorem mate_unit {A : Type*} [Category A] {F G : A ⥤ A}
    (a : F ⊣ G) (e : G ≅ 𝟭 A) :
    Adjunction.leftAdjointIdIso a e =
      ((conjugateIsoEquiv a (Adjunction.id : (𝟭 A) ⊣ 𝟭 A)).symm e).symm := by
  apply Iso.ext
  rfl

private theorem pretransport {A : Type*} [Category A]
    {F F' G : A ⥤ A} (h : F = F') (e : F' ≅ G) (K : A) :
    HEq ((eqToIso h ≪≫ e).hom.app K) (e.hom.app K) := by
  cases h
  exact heq_of_eq (Category.id_comp _)

omit [AlgebraicGeometry.IsNoetherian T] dT in
private theorem unit_mate_heq
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (f f' : R ⟶ R) (h : f = 𝟙 R) (h' : f' = 𝟙 R) (e : f = f')
    (K : DerivedCategory (pbcModules T R)) :
    HEq ((Adjunction.leftAdjointIdIso (pbcDerivedScalarAdjunction f)
      (Functor.exactDerivedRestrictionUnit _
        (SheafOfModules.systemScalarRestrictionUnit f h))).hom.app K)
      ((Adjunction.leftAdjointIdIso (pbcDerivedScalarAdjunction f')
        (Functor.exactDerivedRestrictionUnit _
          (SheafOfModules.systemScalarRestrictionUnit f' h'))).hom.app K) := by
  cases e
  rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem restriction_id_section
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.systemScalarRestrictionUnit (𝟙 R) rfl).hom.app M).val.app U x = x := by
  rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem embedding_unit_mate
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    HEq ((Adjunction.leftAdjointIdIso (pbcDerivedScalarAdjunction (𝟙 _))
      (Functor.exactDerivedRestrictionUnit _
        (SheafOfModules.systemScalarRestrictionUnit
          (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))) rfl))).hom.app K)
      ((pbcEmbeddingAmbientUnit l E T).hom.app K) := by
  have hu : SheafOfModules.systemScalarRestrictionUnit
      (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))) rfl =
      pbcScalarRestrictId l E T := by
    apply (pbcScalarRestrictId_exists l E T).unique
    · exact restriction_id_section T _
    · unfold pbcScalarRestrictId
      exact (pbcScalarRestrictId_exists l E T).exists.choose_spec
  unfold pbcEmbeddingAmbientUnit
  rw [← mate_unit]
  refine HEq.trans ?_ (pretransport _ _ K).symm
  unfold Functor.exactDerivedRestrictionUnit
  rw [hu]
  exact HEq.rfl

omit dT iT in
private theorem ambient_unit (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (K : pbcAmbientStage l (PadicAlgCl l) T E) :
    HEq ((pbcAmbientScalarUnit l (PadicAlgCl l) T E).hom.app K)
      ((pbcEmbeddingAmbientUnit l (pbcFiniteField.{u} l (PadicAlgCl l) E) T).hom.app K) := by
  have hp := congrArg (fun e ↦ e.hom.app K)
    (pbcAmbientScalarUnit_mate l (PadicAlgCl l) T E)
  apply (heq_of_eq hp).trans
  have hh := unit_mate_heq T
    (pbcCompletedScalarMap l (PadicAlgCl l) T (le_refl E)) (𝟙 _)
    (pbcCompletedScalarMap_id l (PadicAlgCl l) T E) rfl
    (pbcCompletedScalarMap_id l (PadicAlgCl l) T E) K
  exact hh.trans (embedding_unit_mate l T _ K)

@[irreducible] private def rationalUnitTransport
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E) :
    pbcRationalScalarExtension l E E i T dT.out iT.out ≅ 𝟭 _ :=
  eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E E i T dT.out iT.out) e) ≪≫
    pbcRationalScalarUnit l E T dT.out iT.out

private theorem rational_unit_projection
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : PbcRationalDerivedCategory l E T dT.out iT.out) :
    (pbcRationalScalarUnit l E T dT.out iT.out).hom.app K =
      (pbcRationalScalarUnitComponent l E T dT.out iT.out K).hom := by
  unfold pbcRationalScalarUnit
  exact NatIso.ofComponents_hom_app _ _ K

private theorem rational_unit_map
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : PbcRationalDerivedCategory l E T dT.out iT.out) :
    HEq ((pbcRationalScalarUnitComponent l E T dT.out iT.out K).hom)
      ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk
          (X := (pbcEmbeddingIntegralTensor l E E (AlgHom.id (Padic l) E)
            T dT.out iT.out).obj K.obj) (Y := K.obj)
          ((pbcEmbeddingAmbientUnit l E T).hom.app K.obj.obj))) := by
  unfold pbcRationalScalarUnitComponent
  exact HEq.rfl

private theorem rational_unit_of_integral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (I : PbcIntegralCategory l E T dT.out iT.out ⥤
      PbcIntegralCategory l E T dT.out iT.out)
    (v : I ≅ 𝟭 _)
    (hI : I = pbcEmbeddingIntegralTensor l E E (AlgHom.id (Padic l) E) T dT.out iT.out)
    (hv : ∀ K, HEq ((v.hom.app K).hom) ((pbcEmbeddingAmbientUnit l E T).hom.app K.obj))
    (K : PbcRationalDerivedCategory l E T dT.out iT.out) :
    HEq ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map
      (v.hom.app K.obj))
      ((pbcRationalScalarUnit l E T dT.out iT.out).hom.app K) := by
  refine HEq.trans ?_ (heq_of_eq (rational_unit_projection l T E K)).symm
  refine HEq.trans ?_ (rational_unit_map l T E K).symm
  apply map_heq_both _ _ _ (congrArg (fun I ↦ I.obj K.obj) hI) rfl
  apply full_hom_heq _ _ _ (congrArg (fun I ↦ (I.obj K.obj).obj) hI) rfl
  exact hv K.obj

private theorem rational_unit_of_integral_transport_at
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (I : PbcIntegralCategory l E T dT.out iT.out ⥤
      PbcIntegralCategory l E T dT.out iT.out)
    (v : I ≅ 𝟭 _) (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E)
    (hI : I = pbcEmbeddingIntegralTensor l E E (AlgHom.id (Padic l) E) T dT.out iT.out)
    (hv : ∀ K, HEq ((v.hom.app K).hom) ((pbcEmbeddingAmbientUnit l E T).hom.app K.obj))
    (K : PbcRationalDerivedCategory l E T dT.out iT.out) :
    HEq ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map
      (v.hom.app K.obj)) ((rationalUnitTransport l T E i e).hom.app K) := by
  cases e
  simpa only [rationalUnitTransport, eqToIso_refl, Iso.refl_trans] using
    rational_unit_of_integral l T E I v hI hv K

private theorem map_heq_functor {A B : Type*} [Category A] [Category B]
    {Q Q' : A ⥤ B} (hQ : Q = Q') {X Y : A} (f : X ⟶ Y) :
    HEq (Q.map f) (Q'.map f) := by
  cases hQ
  rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem stage_localization_eq (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    pbcStageLocalization l (PadicAlgCl l) T E =
      pbcRationalization T (pbcIntegralDatum l (pbcFiniteField.{u} l (PadicAlgCl l) E))
        (pbcUniformizer l (pbcFiniteField.{u} l (PadicAlgCl l) E)) := by
  rfl

private theorem integralTensor_id
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E) :
    pbcEmbeddingIntegralTensor l E E i T dT.out iT.out =
      pbcEmbeddingIntegralTensor l E E (AlgHom.id (Padic l) E) T dT.out iT.out := by
  cases e
  rfl

private theorem integral_identity_functor
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :
    pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out (le_refl E) =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteField.{u} l (PadicAlgCl l) E) (AlgHom.id (Padic l) _) T
        dT.out iT.out := by
  exact (rawScalar_integralTensor l (PadicAlgCl l) T (le_refl E)).trans
    (integralTensor_id l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E))

private theorem integral_unit_ambient (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (M : PbcIntegralCategory l (pbcFiniteField.{u} l (PadicAlgCl l) E) T dT.out iT.out) :
    HEq (((pbcIntegralScalarUnit l (PadicAlgCl l) T dT.out iT.out E).hom.app M).hom)
      ((pbcEmbeddingAmbientUnit l (pbcFiniteField.{u} l (PadicAlgCl l) E) T).hom.app
        M.obj) := by
  exact (heq_of_eq (pbcIntegralScalarUnit_hom l (PadicAlgCl l) T dT.out iT.out E M)).trans
    (ambient_unit l T E M.obj)

private theorem integral_unit_specialized
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (K : PbcIntegralCategory l (pbcFiniteField.{u} l (PadicAlgCl l) E) T dT.out iT.out) :
    HEq ((pbcStageLocalization l (PadicAlgCl l) T E).map
      ((pbcIntegralScalarUnit l (PadicAlgCl l) T dT.out iT.out E).hom.app K))
      ((rationalUnitTransport l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)).hom.app
          ((pbcStageLocalization l (PadicAlgCl l) T E).obj K)) := by
  refine (map_heq_functor (stage_localization_eq l T E)
    ((pbcIntegralScalarUnit l (PadicAlgCl l) T dT.out iT.out E).hom.app K)).trans ?_
  exact rational_unit_of_integral_transport_at l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
    (pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out (le_refl E))
    (pbcIntegralScalarUnit l (PadicAlgCl l) T dT.out iT.out E)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
    (integral_identity_functor l T E) (fun N ↦ integral_unit_ambient l T E N)
    ((pbcStageLocalization l (PadicAlgCl l) T E).obj K)

private theorem integral_comparison_unit {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (I : A ⥤ A) (S : B ⥤ B) (hs : S = 𝟭 B) (v : I ≅ 𝟭 A)
    (c : Q ⋙ S ≅ I ⋙ Q)
    (hc : c = eqToIso (congrArg (fun S ↦ Q ⋙ S) hs) ≪≫
      (Functor.rightUnitor Q ≪≫ (Functor.leftUnitor Q).symm ≪≫
        Functor.isoWhiskerRight v.symm Q)) (K : A) :
    HEq (c.hom.app K ≫ Q.map (v.hom.app K)) (𝟙 (Q.obj K)) := by
  cases hs
  rw [hc]
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Functor.id_obj]
  exact heq_of_eq (Category.id_comp (𝟙 (Q.obj K)))

private theorem raw_unit (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (K : pbcStageCategory l (PadicAlgCl l) T E) :
    HEq ((pbcFiniteRawScalarComparison l (PadicAlgCl l) T (le_refl E)).hom.app K ≫
      (rationalUnitTransport l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)).hom.app K)
      (𝟙 K) := by
  obtain ⟨K⟩ := K
  have hq : (pbcStageLocalization l (PadicAlgCl l) T E).obj K =
      (⟨K⟩ : pbcStageCategory l (PadicAlgCl l) T E) := rfl
  rw [← hq]
  have hh := (pbcFiniteRawScalarComparison_existsUnique l (PadicAlgCl l) T
    (le_refl E)).exists.choose_spec K
  have ho := raw_obj l T (le_refl E) K
  have he := heq_comp rfl ho rfl hh (integral_unit_specialized l T E K).symm
  have hs := (pbcScalarSystem_units l (PadicAlgCl l) T dT.out iT.out (le_refl E)).1
  exact he.trans (integral_comparison_unit (pbcStageLocalization l (PadicAlgCl l) T E)
    (pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out (le_refl E))
    (pbcScalarExtension l (PadicAlgCl l) T dT.out iT.out (le_refl E)) hs
    (pbcIntegralScalarUnit l (PadicAlgCl l) T dT.out iT.out E)
    (pbcScalarIntegralComparison l (PadicAlgCl l) T dT.out iT.out (le_refl E))
    (pbcScalarIntegralComparison_refl l (PadicAlgCl l) T dT.out iT.out E hs) K)

private theorem tower_transport
    (E F G : Type u) [Field E] [Field F] [Field G]
    [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    [FiniteDimensional (Padic l) G]
    (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G) (ij : E →ₐ[Padic l] G)
    (e : j.comp i = ij)
    (sE : RationalModuleRealization l E T) (sF : RationalModuleRealization l F T)
    (sG : RationalModuleRealization l G T)
    (bEF : RationalRealizationScalarComparison l E F i T sE sF)
    (bFG : RationalRealizationScalarComparison l F G j T sF sG)
    (bEG : RationalRealizationScalarComparison l E G ij T sE sG) :
    ∃ hc : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient,
      ∀ (K : PbcRationalDerivedCategory l E T dT.out iT.out)
        (Z : PbcRationalDerivedCategory l G T dT.out iT.out)
        (a : Z ⟶ (pbcRationalScalarExtension l E G ij T dT.out iT.out).obj K)
        (x : Z ⟶ (pbcRationalScalarExtension l F G j T dT.out iT.out).obj
          ((pbcRationalScalarExtension l E F i T dT.out iT.out).obj K)),
      HEq a (x ≫ (pbcRationalScalarComp l E F G i j T dT.out iT.out).hom.app K) →
      sG.J.map a ≫ bEG.theta.hom.app K =
        sG.J.map x ≫ bFG.theta.hom.app
          ((pbcRationalScalarExtension l E F i T dT.out iT.out).obj K) ≫
        (pbcDerivedExtend bFG.coefficient).map (bEF.theta.hom.app K) ≫
        (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
          hc (sE.J.obj K)).hom := by
  cases e
  have ht := rationalRealizationScalarTower l E F i G j sE sF sG bEF bFG bEG
  refine ⟨ht.coefficient, ?_⟩
  intro K Z a x ha
  rw [eq_of_heq ha, Functor.map_comp, Category.assoc, ht.compatibility K]

private theorem coefficient_comp (C : Core l T)
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G) :
    (coefficient l T C h).coefficient ≫ (coefficient l T C k).coefficient =
      (coefficient l T C (h.trans k)).coefficient := by
  exact (tower_transport l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
    (pbcFiniteField.{u} l (PadicAlgCl l) F) (pbcFiniteField.{u} l (PadicAlgCl l) G)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) k)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) (h.trans k)) (inclusion_comp l h k)
    (C.realization E) (C.realization F) (C.realization G)
    (coefficient l T C h) (coefficient l T C k) (coefficient l T C (h.trans k))).choose

private theorem theta_tower (C : Core l T)
    {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) (k : F ≤ G)
    (K : pbcStageCategory l (PadicAlgCl l) T E) :
    (C.realization G).J.map
        ((pbcScalarAssociator l (PadicAlgCl l) T dT.out iT.out h k).hom.app K) ≫
      (theta l T C (h.trans k)).hom.app K =
    (theta l T C k).hom.app
        ((pbcScalarExtension l (PadicAlgCl l) T dT.out iT.out h).obj K) ≫
      (pbcDerivedExtend (coefficient l T C k).coefficient).map
        ((theta l T C h).hom.app K) ≫
      (pbcReductionNormalization (coefficient l T C h).coefficient
        (coefficient l T C k).coefficient (coefficient l T C (h.trans k)).coefficient
        (coefficient_comp l T C h k) ((C.realization E).J.obj K)).hom := by
  obtain ⟨hc, ht⟩ := tower_transport l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
    (pbcFiniteField.{u} l (PadicAlgCl l) F) (pbcFiniteField.{u} l (PadicAlgCl l) G)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) h)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) k)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) (h.trans k)) (inclusion_comp l h k)
    (C.realization E) (C.realization F) (C.realization G)
    (coefficient l T C h) (coefficient l T C k) (coefficient l T C (h.trans k))
  have hr := raw_coherence l T h k K
  simp only [← Category.assoc] at hr
  have hh := ht K _ _ _ hr
  simp only [theta, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] at hh ⊢
  rw [hh]
  have hn := (coefficient l T C k).theta.hom.naturality
    ((pbcFiniteRawScalarComparison l (PadicAlgCl l) T h).hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

private def unitAmbient
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E)
    (s : RationalModuleRealization l E T)
    (b : RationalRealizationScalarComparison l E E i T s s) :
    pbcDerivedExtend b.coefficient ≅ 𝟭 _ := by
  cases e
  exact (rationalRealizationScalarUnit l E s b).some.ambient

private theorem unitAmbient_normalization
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E)
    (s : RationalModuleRealization l E T)
    (b : RationalRealizationScalarComparison l E E i T s s) :
    ∃ o : pbcExtend b.coefficient ≅ 𝟭 _,
      (∀ (M : pbcModules T (rationalCoefficientSheaf l T E)) (U : T.ProEtᵒᵖ)
        (a : (rationalCoefficientSheaf l T E).obj.obj U) (x : M.val.obj U),
        (o.hom.app M).val.app U (pbcTensorSection b.coefficient M U a x) =
          @SMul.smul _ _ (ModuleCat.isModule (M.val.obj U)).toSMul a x) ∧
      ∀ P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ,
        (unitAmbient l T E i e s b).hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit b.coefficient P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) := by
  cases e
  let u := (rationalRealizationScalarUnit l E s b).some
  exact ⟨u.ordinary, u.sections, u.normalization⟩

private theorem unitAmbient_compatibility
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (e : i = AlgHom.id (Padic l) E)
    (s : RationalModuleRealization l E T)
    (b : RationalRealizationScalarComparison l E E i T s s)
    (K : PbcRationalDerivedCategory l E T dT.out iT.out) :
    b.theta.hom.app K ≫ (unitAmbient l T E i e s b).hom.app (s.J.obj K) =
      s.J.map ((rationalUnitTransport l T E i e).hom.app K) := by
  cases e
  simpa only [rationalUnitTransport, unitAmbient, eqToIso_refl, Iso.refl_trans] using
    (rationalRealizationScalarUnit l E s b).some.compatibility K

private theorem realized_unit {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) {X Y Z : A} {W : B}
    (a : X ⟶ Y) (b : Y ⟶ Z) (g : J.obj Y ⟶ W) (u : W ⟶ J.obj Z)
    (hu : g ≫ u = J.map b) (hz : X = Z) (ha : HEq (a ≫ b) (𝟙 Z)) :
    HEq (J.map a ≫ g ≫ u) (𝟙 (J.obj Z)) := by
  rw [hu, ← Functor.map_comp]
  exact (map_heq_both J _ _ hz rfl ha).trans (heq_of_eq (J.map_id Z))

private theorem theta_unit (C : Core l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
    (K : pbcStageCategory l (PadicAlgCl l) T E) :
    HEq ((theta l T C (le_refl E)).hom.app K ≫
      (unitAmbient l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
        (C.realization E) (coefficient l T C (le_refl E))).hom.app ((C.realization E).J.obj K))
      (𝟙 ((C.realization E).J.obj K)) := by
  have hu := unitAmbient_compatibility l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
    (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
    (C.realization E) (coefficient l T C (le_refl E)) K
  have hs := (pbcScalarSystem_units l (PadicAlgCl l) T dT.out iT.out (le_refl E)).1
  have ht := realized_unit (C.realization E).J (Z := K)
    ((pbcFiniteRawScalarComparison l (PadicAlgCl l) T (le_refl E)).hom.app K)
    ((rationalUnitTransport l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)).hom.app K)
    ((coefficient l T C (le_refl E)).theta.hom.app K)
    ((unitAmbient l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
        (C.realization E) (coefficient l T C (le_refl E))).hom.app ((C.realization E).J.obj K)) hu
    (congrArg (fun S ↦ S.obj K) hs) (raw_unit l T E K)
  simpa only [theta, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.id_obj, Functor.comp_obj, Category.assoc] using ht

private def scalarData (C : Core l T) : ScalarData l T C where
  coefficient := coefficient l T C
  theta := theta l T C
  completed_square := completed_square l T C
  integral := integral l T C

private theorem comp_heq_right_id {A : Type*} [Category A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (e : Y = Z)
    (h : HEq g (𝟙 Z)) : HEq (f ≫ g) f := by
  subst Z
  cases h
  exact heq_of_eq (Category.comp_id f)

/-- The finite realization comparisons intertwine the specified raw associators and units.
Source: BS Proposition 6.8.14(2); finite realization node, steps 5--6
(blueprint: lem-sf-adic-finite-scalar-coherence).

Proof:
1. For each inclusion take rationalRealizationScalarCoherence for the two supplied
realizations. Its coefficient is the continuous-function inclusion, and its integral
normalization identifies both routes through the single derived tensor over B_E.
2. Identify pbcCompletedScalarMap with the finite-quotient coefficient inclusion by
uniqueness of the limit map. This gives completed_square. Conjugate the tensor theta
by the integral comparison of the literal-identity raw stage transition. Its component
on QK followed by J_F of that comparison has exactly the two single-tensor formulas
in ScalarData.integral. At equal fields it includes the actual multiplication unitor;
no heterogeneous equality of distinct tensor presentations is asserted.
3. Compose the actual field inclusions to obtain coefficient_comp. Substitute the
three normalized theta components into the tower equation. Use raw.coherence for
the inverse chi comparisons and the scalar-completion associator normalization.
The inner chi and its inverse cancel. The remaining tensor reassociations agree
by multiplication of the scalar factors on K-flat representatives. Naturality and
the fraction formulas extend the equation to all raw rational arrows.
4. For equal fields take the ordinary and derived multiplication unitors of
rationalRealizationScalarUnit. Their section and cochain equations give precisely
unit_normalization. raw.unit cancels the identity completion inverse; multiplication
by one leaves the actual framework unitor. This gives identity, also for repeated
fields and ramified inclusions. No essential-image or closure comparison is used. -/
theorem adic_finite_scalar_coherence (C : Core l T) :
    ∃ B : ScalarData l T C, Nonempty (Coherence l T C B) := by
  refine ⟨scalarData l T C, ⟨{
    coefficient_comp := coefficient_comp l T C
    tower := ?_
    unit := fun E ↦ unitAmbient l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
        (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
        (C.realization E) (coefficient l T C (le_refl E))
    unit_normalization := ?_
    identity := ?_ }⟩⟩
  · intro E F G h k K
    unfold scalarComparison
    simp only [scalarData, finiteFunctor, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Functor.comp_map, Category.assoc]
    rw [← Functor.map_comp_assoc, ← C.raw.coherence.1 h k K]
    simp only [Functor.map_comp, Category.assoc]
    rw [theta_tower l T C]
    have hn := (theta l T C k).hom.naturality ((C.raw.family.β h).inv.app K)
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp only [Functor.comp_obj]
  · intro E
    exact unitAmbient_normalization l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) (le_refl E)) (inclusion_id l E)
      (C.realization E) (coefficient l T C (le_refl E))
  · intro E K
    unfold scalarComparison
    simp only [scalarData, finiteFunctor, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
    have hs := (pbcScalarSystem_units l (PadicAlgCl l) T dT.out iT.out (le_refl E)).1
    have ho := congrArg (fun S ↦ (C.realization E).J.obj
      (S.obj ((C.raw.family.Φ E).obj K))) hs
    apply (comp_heq_right_id _ _ ho
      (theta_unit l T C E ((C.raw.family.Φ E).obj K))).trans
    exact map_heq_both (C.realization E).J
      ((C.raw.family.β (le_refl E)).inv.app K)
      ((C.raw.family.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K))
      (by
        simpa only [Functor.comp_obj] using
          congrArg (fun (F : GeneralAlgebraicallyClosedCoefficients.Stage
            l (PadicAlgCl l) T E ⥤
            GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E) ↦
            (C.raw.family.Φ E).obj (F.obj K))
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
              l (PadicAlgCl l) T).exists.choose_spec.1 E E (le_refl E)))
      (congrArg (fun S ↦ S.obj ((C.raw.family.Φ E).obj K)) hs)
      (C.raw.unit E K)

end WeilConjectures.AdicFiniteRealization
