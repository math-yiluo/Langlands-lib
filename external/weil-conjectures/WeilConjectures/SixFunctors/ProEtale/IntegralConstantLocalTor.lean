/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor

/-! # The two-term Tor bound for integral finite constant local models

Source: integral-models opening equality; Stacks Tags 0651 and 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

attribute [local instance] constantScalarSheaf_laxBraided
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  Mod.extendScalars Mod.extendScalarsComp Mod.extendScalarsIsoOfEq
  Mod.extendScalarsIsoComapInv Mod.extendRestrictAdjunction Mod.regularExtensionIso
  scalarCoefficientHom finiteConstantScalarExtension

private noncomputable def integralScalarEquiv
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ULift.{u + 1} A ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A) where
  toFun a := ULift.up (ContinuousMap.const _ a.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext x
    exact congrArg f.down (Subsingleton.elim PUnit.unit x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def integralScalarHom
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    AddCommGrpCat.of (ULift.{u + 1} A) ⟶
      scalarRingObj (Profinite.continuousCoefficientRingObj A) :=
  (integralScalarEquiv A).toAddEquiv.toAddCommGrpIso.hom

private instance integralScalarHom_iso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsIso (integralScalarHom.{u} A) := by
  unfold integralScalarHom
  infer_instance

private instance integralScalarHom_mon
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsMonHom (integralScalarHom.{u} A) := by
  have hm : (scalarSections.{u}).monObjObj (Profinite.continuousCoefficientRingObj A) =
      AddCommGrpCat.ringMonObj
        (ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A)) := by
    rw [scalarSections_monoidal_eq]
    apply MonObj.ext
    let R := Profinite.continuousCoefficientRingSheaf.{u} A
    let : MonObj (Profinite.continuousCoefficientRingObj.{u} A).obj := R.obj.monObjCompForget₂
    exact congr_app (Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj A))
      (Opposite.op (Profinite.of PUnit.{u + 1}))
  change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
  rw [hm]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (integralScalarEquiv A).toRingHom

set_option backward.isDefEq.respectTransparency false in
private theorem integralScalarExtension_leftExact
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))]
    (φ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousCoefficientRingObj A)
    [IsMonHom φ]
    (hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ φ).app S) a = ULift.up (ContinuousMap.const S.unop a.down)) :
    PreservesFiniteLimits (Mod.extendScalars φ) := by
  let J := coherentTopology Profinite.{u}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let R := (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj P := (Functor.const Profinite.{u}ᵒᵖ).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  let η : P ⟶ R.obj := toSheafify J P
  have hη : IsMonHom η := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have he : (inferInstance : MonObj R) =
        (presheafToSheaf J Ab.{u + 1}).monObjObj P :=
      Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
        (presheafToSheaf J Ab.{u + 1}) (AddCommGrpCat.of (ULift.{u + 1} A))
    have he' := congrArg (fun m : MonObj R ↦
      @Functor.monObjObj _ _ _ _ _ _ (sheafToPresheaf J Ab.{u + 1}) _ R m) he
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl he'.symm h
  let RR := InternalAbelianSheafModule.sectionRingSheaf J R
  let ι (S : Profinite.{u}ᵒᵖ) : A →+* RR.obj.obj S :=
    { ((η.app S).hom.comp
        (ULift.moduleEquiv.symm : A ≃ₗ[A] ULift.{u + 1} A).toAddMonoidHom) with
      map_one' := by
        have h := congr_app (IsMonHom.one_hom (f := η)) S
        change (η.app S) (ULift.up (1 : A)) = _
        have he := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
        change (η.app S) (ULift.up ((1 : ℤ) : A)) = (1 : RR.obj.obj S) at he
        simpa using he
      map_mul' := fun a b ↦ ConcreteCategory.congr_hom
        (congr_app (IsMonHom.mul_hom (f := η)) S) (ULift.up a ⊗ₜ[ℤ] ULift.up b) }
  let N := (Mod.comap φ).obj (Mod.regular (Profinite.continuousCoefficientRingObj A))
  let M := (InternalAbelianSheafModule.sectionModuleFunctor J R).obj N
  have hsmul (S : Profinite.{u}ᵒᵖ) (a : A) (s : M.val.obj S) :
      ι S a • s = a • (show ULift.{u + 1} C(S.unop, A) from s) := by
    have he := hφ S (ULift.up a)
    change (φ.hom.app S) ((η.app S) (ULift.up a)) = _ at he
    change ((φ.hom.app S) ((η.app S) (ULift.up a))) = _ at he
    let : MonObj (Profinite.continuousCoefficientRingObj A).obj := inferInstanceAs
      (MonObj (Profinite.continuousCoefficientRingPresheaf A ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}))
    have hm := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj A)
    let F := sheafToPresheaf J Ab.{u + 1}
    change ((Functor.LaxMonoidal.μ F R (Profinite.continuousCoefficientRingObj A) ≫
      F.map (φ ▷ (Profinite.continuousCoefficientRingObj A) ≫ MonObj.mul)).app S).hom
        (((η.app S) (ULift.up a)) ⊗ₜ[ℤ]
          (show ULift.{u + 1} C(S.unop, A) from s)) = _
    rw [F.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc, hm]
    change (show ULift.{u + 1} C(S.unop, A) from
      (φ.hom.app S) ((η.app S) (ULift.up a))) *
        (show ULift.{u + 1} C(S.unop, A) from s) = _
    rw [he]
    rfl
  have hflat (S : Profinite.{u}ᵒᵖ) : Module.Flat A (ULift.{u + 1} C(S.unop, A)) := by
    have : Module.IsTorsionFree A (ULift.{u + 1} C(S.unop, A)) := by
      apply Module.IsTorsionFree.of_smul_eq_zero
      intro a f h
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        have hx : a * f.down x = 0 := congrArg (fun g ↦ g.down x) h
        exact (mul_eq_zero.mp hx).resolve_left ha
    infer_instance
  have hlifts (U : Profinite.{u}) (n : ℕ) (a : Fin n → RR.obj.obj (op U)) :
      ∃ S : Sieve U, S ∈ J U ∧ ∀ V (f : V ⟶ U), S f →
        ∃ c : Fin n → A, ∀ i, ι (op V) (c i) = RR.obj.map f.op (a i) := by
    induction n with
    | zero =>
      refine ⟨⊤, J.top_mem U, ?_⟩
      intro V f hf
      exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
      refine ⟨Presheaf.imageSieve η (a 0) ⊓ S,
        J.intersection_covering (Presheaf.imageSieve_mem J η (a 0)) hS, ?_⟩
      intro V f hf
      obtain ⟨c, hc⟩ := hs V f hf.2
      obtain ⟨c₀, hc₀⟩ := hf.1
      refine ⟨Fin.cons c₀.down c, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ hc j) i
      exact hc₀
  have hN : ObjectProperty.flat N := by
    apply (InternalAbelianSheafModule.flat_iff_sectionModule J R N).mpr
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      RR M).mpr
    intro U n a s hs
    obtain ⟨S, hS, hl⟩ := hlifts U n a
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨c, hc⟩ := hl V f hf
    let s' : Fin n → ULift.{u + 1} C(V, A) := fun i ↦ M.val.map f.op (s i)
    have he : ∑ i, c i • s' i = 0 := by
      have h := congrArg (fun z : M.val.obj (op U) ↦ M.val.restrictₛₗ f.op z) hs
      simp only [map_sum, map_smulₛₗ, PresheafOfModules.restrictₛₗ_apply, map_zero] at h
      change (∑ i, RR.obj.map f.op (a i) • M.val.restrictₛₗ f.op (s i)) = 0 at h
      simpa only [← hc, hsmul, PresheafOfModules.restrictₛₗ_apply, s'] using! h
    have := hflat (op V)
    obtain ⟨l, b, t, hst, hcb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero he
    refine ⟨l, (fun i j ↦ ι (op V) (b i j)), t, ?_, ?_⟩
    · intro i
      simpa only [hsmul] using hst i
    · intro j
      simpa only [hc, map_sum, map_mul, map_zero] using
        congrArg (ι (op V)) (hcb j)
  have ht : PreservesFiniteLimits (tensorLeft N) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).mp hN
  have : PreservesFiniteLimits (Mod.extendScalars φ ⋙ Mod.forget _) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (Mod.extendScalars φ) (Mod.forget _)

private theorem integralCounitExtension_leftExact
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit.{u} (Profinite.continuousCoefficientRingObj.{u} A))) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let R := Profinite.continuousCoefficientRingObj.{u} A
  let h := integralScalarHom.{u} A
  let f := C.map h
  let ε := scalarCounit R
  have : IsCommMonObj (C.obj (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    Functor.isCommMonObj_obj (F := C)
  have hf : IsMonHom f := Functor.map.instIsMonHom (F := C) _ _ h
  have hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ (f ≫ ε)).app S) a = ULift.up (ContinuousMap.const S.unop a.down) := by
    let p : (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
        R.obj :=
      { app S := AddCommGrpCat.ofHom
          { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
            map_zero' := rfl
            map_add' _ _ := rfl }
        naturality _ _ _ := rfl }
    have he : f ≫ ε =
        ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
          _ R).symm p := by
      change (adj.homEquiv _ _).symm h = _
      apply (adj.homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      dsimp only [adj, constantSheafAdj]
      rw [Adjunction.comp_homEquiv]
      erw [Equiv.trans_apply, Equiv.apply_symm_apply]
      change h = 𝟙 _ ≫ p.app (op (Profinite.of PUnit.{u + 1}))
      rw [Category.id_comp]
      rfl
    rw [he, Equiv.apply_symm_apply]
    intros
    rfl
  have : PreservesFiniteLimits (Mod.extendScalars (f ≫ ε)) :=
    integralScalarExtension_leftExact A (f ≫ ε) hφ
  have : (Mod.extendScalars f).IsEquivalence := extension_equivalence f
  have he : inv f ≫ (f ≫ ε) = ε := by simp
  let i : Mod.extendScalars ε ≅
      Mod.extendScalars (inv f) ⋙ Mod.extendScalars (f ≫ ε) :=
    Mod.extendScalarsIsoOfEq he.symm ≪≫ Mod.extendScalarsComp _ _
  have : (Mod.extendScalars (inv f)).IsEquivalence := extension_equivalence (inv f)
  exact preservesFiniteLimits_of_natIso i.symm

/-- Finite constant integral local models have the common Tor interval [-1,0].
Source: integral-models opening equality and the localizing-closure proof, Local models
and Locality paragraphs; Stacks Tags 0651 and 06YY.
(auxiliary; not a blueprint node).

Proof: the scalar ring of integers is a DVR. A finite presentation of a scalar module
has a finite free kernel, since a finitely generated submodule of a finite free module
over a PID is finite free. It therefore has a resolution by finite free modules in
degrees -1 and 0. The constant-to-continuous coefficient extension is flat: its sections
are torsion-free over the DVR, hence flat, and exact sheafification preserves injections.
Exact inverse image to a scheme carries the scalar resolution to a two-term finite
free coefficient resolution. Tensoring this bounded flat resolution with any degree-zero
module has no terms outside [-1,0], hence no cohomology outside that interval. Restrict
to the cover exhibiting the finite constant local model, use its model isomorphisms,
and detect vanishing of each tensor homology sheaf on that cover. This gives the same
interval for every test module globally. Rank-zero models, torsion scalar modules and
empty covers satisfy the same argument; no Noetherian assumption is needed. -/
theorem integral_constant_local_tor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (M : AdicCompletion.Modules l E X)
    (hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X M) :
    DerivedCategory.torAmplitudeIn _ (-1) 0
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  have : IsDiscreteValuationRing A :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.1
  let Λ := DerivedNakayama.integerRing l E
  obtain ⟨U, hU⟩ := (finiteConstantLocalModel_iff_exists_cover Λ M).mp hM
  have hε := integralCounitExtension_leftExact A
  apply tor_of_cover Λ X U
  intro i
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  have := scalarExtension_leftExact Λ hε (U.X i)
  have : IsDomain (ULift.{u + 1} A) :=
    MulEquiv.isDomain A (ULift.ringEquiv (R := A)).toMulEquiv
  have : IsPrincipalIdealRing (ULift.{u + 1} A) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := A)).symm.toRingHom
      (ULift.ringEquiv (R := A)).symm.surjective
  let d := ((CondensedRing.upperStar Λ (U.f i)).mapDerivedCategorySingleFunctor 0).app M
  exact (DerivedCategory.torAmplitudeIn _ (-1) 0).prop_of_iso
    (d ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eP).symm
    (scalar_pid_model_tor Λ (ULift.{u + 1} A)
      (integralScalarHom A) (U.X i) P hP)

end AlgebraicGeometry.ProEtale
