/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.FiniteProjectiveFreeModIdeal
import WeilConjectures.RingTheory.NakayamaNilpotent
import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift

/-!
# Pseudo-coherence across a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 0H76,
lemma-check-pseudo-coherent-modulo-nilpotent
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

open CategoryTheory.Functor in
open scoped TensorProduct in
private theorem kan_postcompose_equivalence
    {C D H H' : Type*} [Category C] [Category D] [Category H] [Category H']
    (Q : C ⥤ D) (F : C ⥤ H) (G : H ⥤ H') [G.IsEquivalence]
    (L : D ⥤ H) (ε : Q ⋙ L ⟶ F) [L.IsRightKanExtension ε] :
    (L ⋙ G).IsRightKanExtension
      ((Functor.associator Q L G).inv ≫ whiskerRight ε G) := by
  let T := Functor.RightExtension.postcompose₂ Q F G
  have : T.IsEquivalence := by
    let i : (whiskeringRight D H H').obj G ⋙ (whiskeringLeft C D H').obj Q ≅
        (whiskeringLeft C D H).obj Q ⋙ (whiskeringRight C H H').obj G :=
      NatIso.ofComponents (fun X => (Functor.associator Q X G).symm) (by
        intro X Y f
        ext x
        simp)
    change (CostructuredArrow.map₂ i.hom (𝟙 (F ⋙ G))).IsEquivalence
    let _ : IsIso (𝟙 (F ⋙ G)) := inferInstance
    apply CostructuredArrow.isEquivalenceMap₂
  refine ⟨⟨?_⟩⟩
  exact CategoryTheory.Limits.IsTerminal.ofIso
    ((CategoryTheory.Limits.IsTerminal.isTerminalIffObj T
      (Functor.RightExtension.mk L ε)).1 (L.isUniversalOfIsRightKanExtension ε))
    (Functor.RightExtension.postcompose₂ObjMkIso G ε)

open CategoryTheory.Functor in
open scoped TensorProduct in
private noncomputable def quotient_scalar_iso
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) :
    ModuleCat.extendScalars.{u, u, max u v} φ ⋙
      ModuleCat.restrictScalars (RingHom.quotientKerEquivOfSurjective hφ).toRingHom ≅
        ModuleCat.extendScalars (Ideal.Quotient.mk (RingHom.ker φ)) := by
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have he : Ideal.Quotient.mk (RingHom.ker φ) = e.symm.toRingHom.comp φ := by
    exact (RingHom.quotientKerEquivOfSurjective_symm_comp hφ).symm
  let adj := (ModuleCat.extendRestrictScalarsAdj φ).comp E.toAdjunction
  exact (adj.ofNatIsoRight (ModuleCat.restrictScalarsComp' φ e.symm.toRingHom
    (Ideal.Quotient.mk (RingHom.ker φ)) he).symm).leftAdjointUniq
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (RingHom.ker φ)))

open CategoryTheory.Functor in
open scoped TensorProduct in
private theorem surjective_of_extendScalars_nilpotent
    {A : Type u} [CommRing A] (I : Ideal A) (hI : IsNilpotent I)
    (M N : ModuleCat.{max u v} A) (f : M ⟶ N)
    (hf : Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)) :
    Function.Surjective f := by
  apply RingTheory.surjective_of_surjective_mod_nilpotent A M N I f.hom
    (by obtain ⟨n, hn⟩ := hI; exact ⟨n + 1, by omega, by
          rw [pow_succ, hn, zero_mul]; rfl⟩)
  intro z
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) z
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eN := TensorProduct.quotTensorEquivQuotSMul N I
  obtain ⟨t, ht⟩ := hf ((1 : A ⧸ I) ⊗ₜ[A] n)
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) (eM t)
  change Submodule.Quotient.mk m = eM t at hm
  have ht' : t = (1 : A ⧸ I) ⊗ₜ[A] m := by
    apply eM.injective
    simpa only [eM, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hm.symm
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  rw [ht'] at ht
  have he := congrArg eN ht
  change eN ((LinearMap.baseChange (A ⧸ I) f.hom) ((1 : A ⧸ I) ⊗ₜ[A] m)) =
    eN ((1 : A ⧸ I) ⊗ₜ[A] n) at he
  simpa only [eN, LinearMap.baseChange_tmul,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.mapQ_apply,
    Submodule.mkQ_apply] using he

open CategoryTheory.Functor in
open scoped TensorProduct in
private theorem finite_free_of_nilpotent_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (hI : IsNilpotent I)
    (P : ModuleCat.{max u v} A) [Module.Projective A P]
    [Module.Free (A ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)]
    [Module.Finite (A ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)] :
    Module.Free A P ∧ Module.Finite A P := by
  classical
  have : Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] P) :=
    ‹Module.Free (A ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)›
  have : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] P) :=
    ‹Module.Finite (A ⧸ I) ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)›
  let ι := Module.Free.ChooseBasisIndex (A ⧸ I) ((A ⧸ I) ⊗[A] P)
  let b := Module.Free.chooseBasis (A ⧸ I) ((A ⧸ I) ⊗[A] P)
  let F := ι →₀ A
  let bF : Module.Basis ι A F := Finsupp.basisSingleOne
  let e : ((A ⧸ I) ⊗[A] F) ≃ₗ[A ⧸ I] ((A ⧸ I) ⊗[A] P) :=
    (bF.baseChange (A ⧸ I)).repr ≪≫ₗ b.repr.symm
  let qP : P →ₗ[A] (A ⧸ I) ⊗[A] P := TensorProduct.mk A (A ⧸ I) P 1
  have hqP : Function.Surjective qP := by
    intro t
    let eqP := TensorProduct.quotTensorEquivQuotSMul P I
    obtain ⟨p, hp⟩ := (I • (⊤ : Submodule A P)).mkQ_surjective (eqP t)
    refine ⟨p, eqP.injective ?_⟩
    change eqP ((1 : A ⧸ I) ⊗ₜ[A] p) = eqP t
    change Submodule.Quotient.mk p = eqP t at hp
    simpa only [qP, eqP, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hp
  let a : F →ₗ[A] (A ⧸ I) ⊗[A] P :=
    e.toLinearMap.restrictScalars A ∘ₗ TensorProduct.mk A (A ⧸ I) F 1
  obtain ⟨f, hf⟩ := Module.projective_lifting_property qP a hqP
  have hfe : f.baseChange (A ⧸ I) = e.toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    apply TensorProduct.ext'
    intro s m
    have hm := DFunLike.congr_fun hf m
    change (1 : (A ⧸ I)) ⊗ₜ[A] f m = e ((1 : (A ⧸ I)) ⊗ₜ[A] m) at hm
    change s ⊗ₜ[A] f m = e (s ⊗ₜ[A] m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← e.map_smul]
      using congrArg (s • ·) hm
  have hsurj : Function.Surjective f :=
    surjective_of_extendScalars_nilpotent I hI (ModuleCat.of A F) P (ModuleCat.ofHom f)
      (by change Function.Surjective (f.baseChange (A ⧸ I)); rw [hfe]; exact e.surjective)
  have : Module.Finite A P := Module.Finite.of_surjective f hsurj
  refine ⟨ModuleCat.free_of_free_extendScalars_mod_ideal I ?_ P, inferInstance⟩
  intro x
  apply (hI.isUnit_quotient_mk_iff).1
  simp [_root_.map_add, Ideal.Quotient.eq_zero_iff_mem.mpr x.property]

open CategoryTheory.Functor in
open scoped TensorProduct in
private noncomputable def ulift_scalar_iso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv.symm : A ≃+* ULift.{v} A).toRingHom ⋙
      (ModuleCat.extendScalars φ ⋙
        ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom) ≅
          ModuleCat.extendScalars φ.ulift := by
  let eA : ULift.{v} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{v} B ≃+* B := ULift.ringEquiv
  let adj := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv eA.symm).toAdjunction.comp
    ((ModuleCat.extendRestrictScalarsAdj φ).comp
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv eB).toAdjunction)
  let r : ModuleCat.restrictScalars.{max u v} φ.ulift ≅
      (ModuleCat.restrictScalars eB.symm.toRingHom ⋙ ModuleCat.restrictScalars φ) ⋙
        ModuleCat.restrictScalars eA.toRingHom :=
    ModuleCat.restrictScalarsComp eA.toRingHom (eB.symm.toRingHom.comp φ) ≪≫
    isoWhiskerRight (ModuleCat.restrictScalarsComp φ eB.symm.toRingHom) _
  exact (adj.ofNatIsoRight r.symm).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj φ.ulift)

open CategoryTheory.Functor in
open scoped TensorProduct in
private theorem counit_isIso_of_boundedAbove_free
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B)
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars φ)
        (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive (.up ℤ) ⋙
          DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Free A (P.X i)) :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) := by
  classical
  let eA : ULift.{v} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{v} B ≃+* B := ULift.ringEquiv
  let SA := ModuleCat.restrictScalars.{max u v} eA.symm.toRingHom
  let TA := ModuleCat.restrictScalars.{max u v} eA.toRingHom
  let TB := ModuleCat.restrictScalars.{max u v} eB.toRingHom
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (ULift.{v} A))
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (ULift.{v} B))
  let SD := SA.mapDerivedCategory
  let TD := TB.mapDerivedCategory
  let F := ModuleCat.extendScalars.{u, u, max u v} φ
  let Fup := ModuleCat.extendScalars.{max u v, max u v, max u v} φ.ulift
  have : F.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  have : Fup.Additive := (ModuleCat.extendRestrictScalarsAdj φ.ulift).left_adjoint_additive
  let Sh := SA.mapHomotopyCategory (.up ℤ)
  have : Sh.IsEquivalence := by
    let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv eA.symm
    let Th := TA.mapHomotopyCategory (.up ℤ)
    let iu : Sh ⋙ Th ≅ 𝟭 _ :=
      Functor.mapHomotopyCategoryCompIso e.unitIso.symm (.up ℤ) ≪≫
        Functor.mapHomotopyCategoryIdIso _ _
    let ic : Th ⋙ Sh ≅ 𝟭 _ :=
      Functor.mapHomotopyCategoryCompIso e.counitIso (.up ℤ) ≪≫
        Functor.mapHomotopyCategoryIdIso _ _
    exact (CategoryTheory.Equivalence.mk Sh Th iu.symm ic).isEquivalence_functor
  let η := (Functor.associator Sh DerivedCategory.Qh L).hom ≫ whiskerLeft Sh ε
  have hKan : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  let _ := hKan
  have hη := (Functor.isRightKanExtension_iff_precomp L Sh ε).1 hKan
  let κ := (Functor.associator DerivedCategory.Qh SD L).inv ≫
    whiskerRight SA.mapDerivedCategoryFactorsh.hom L ≫ η
  have hκ := (Functor.isRightKanExtension_iff_postcomp₁ SD
    SA.mapDerivedCategoryFactorsh η).1 hη
  let _ := hκ
  let χ : ((Sh ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)) ⋙ TD) ≅
      Fup.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Sh (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ TB.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (SA ⋙ F)) (.up ℤ)) _ ≪≫
        Functor.mapHomotopyCategoryCompIso
          (Functor.associator SA F TB ≪≫ ulift_scalar_iso φ)
          (.up ℤ)) _
  let ζ := (Functor.associator DerivedCategory.Qh (SD ⋙ L) TD).inv ≫ whiskerRight κ TD
  let εup := ζ ≫ χ.hom
  have hζ := kan_postcompose_equivalence DerivedCategory.Qh _ TD (SD ⋙ L) κ
  have : ((SD ⋙ L) ⋙ TD).IsLeftDerivedFunctor εup
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} (ULift.{v} A)) (.up ℤ)) := by
    constructor
    exact (Functor.isRightKanExtension_iff_of_iso₂ ζ εup χ (Iso.refl _) (by
      simp [εup])).1 hζ
  let Pup : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ :=
    (TA.mapHomologicalComplex (.up ℤ)).obj P
  have hPb : Pup.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P TA b).2 hb
  have hPfree : ∀ i, Module.Free (ULift.{v} A) (Pup.X i) := by
    intro i
    have := hP i
    let : Module (ULift.{v} A) (P.X i) := (Pup.X i).isModule
    let bP := Module.Free.chooseBasis A (P.X i)
    exact Module.Free.of_basis
      (bP.mapCoeffs eA.symm (by intro c x; change eA (eA.symm c) • x = c • x; simp))
  have hflat : ∀ i, Module.Flat (ULift.{v} A) (Pup.X i) := by
    intro i
    have := hPfree i
    infer_instance
  have hc := ModuleCat.scalarExtensionCounit_isIso_of_kFlat φ.ulift Pup
    (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat Pup
      ⟨b, (Pup.isStrictlyLE_iff b).1 hPb⟩ hflat)
    ((SD ⋙ L) ⋙ TD) εup inferInstance
  have hcomp : IsIso (TD.map (ε.app (Sh.obj ((HomotopyCategory.quotient _ _).obj Pup)))) := by
    simpa only [εup, ζ, κ, η, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff] using hc
  have he : IsIso (ε.app (Sh.obj ((HomotopyCategory.quotient _ _).obj Pup))) := by
    let _ := hcomp
    exact isIso_of_reflects_iso _ TD
  let iC := ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv eA.symm).mapHomologicalComplex
    (.up ℤ)).counitIso.app P
  let iH := (SA.mapHomotopyCategoryFactors (.up ℤ)).app Pup ≪≫
    (HomotopyCategory.quotient _ _).mapIso iC
  exact (NatTrans.isIso_app_iff_of_iso ε iH).1 he

open CategoryTheory.Functor in
open scoped TensorProduct in
private theorem projective_model_with_free_reduction
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars φ)
        (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive (.up ℤ) ⋙
          DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (hC : DerivedCategory.IsPseudoCoherent (L.obj C)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧ (∀ i, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      (∀ i, Module.Free (A ⧸ RingHom.ker φ)
        ((ModuleCat.extendScalars (Ideal.Quotient.mk (RingHom.ker φ))).obj (P.X i)) ∧
        Module.Finite (A ⧸ RingHom.ker φ)
        ((ModuleCat.extendScalars (Ideal.Quotient.mk (RingHom.ker φ))).obj (P.X i))) := by
  classical
  obtain ⟨E, b, hb, hE, ⟨eE⟩⟩ := hC
  let I := RingHom.ker φ
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let H := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (A ⧸ I))
  let D := H.mapDerivedCategory
  let F := ModuleCat.extendScalars.{u, u, max u v} φ
  let F₀ := ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)
  have : F.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  have : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  let θ : (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ D ≅
      F₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ H.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (quotient_scalar_iso φ hφ)
      (.up ℤ)) _
  let η := (Functor.associator DerivedCategory.Qh L D).inv ≫ whiskerRight ε D
  let ε₀ := η ≫ θ.hom
  have hKan : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
  let _ := hKan
  have hKan₀ := kan_postcompose_equivalence DerivedCategory.Qh _ D L ε
  have : (L ⋙ D).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) := by
    constructor
    exact (Functor.isRightKanExtension_iff_of_iso₂ η ε₀ θ (Iso.refl _) (by
      simp [ε₀])).1 hKan₀
  let E₀ : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ :=
    (H.mapHomologicalComplex (.up ℤ)).obj E
  have hE₀ : ∀ i, Module.Free (A ⧸ I) (E₀.X i) ∧
      Module.Finite (A ⧸ I) (E₀.X i) := by
    intro i
    have : Module.Free B (E.X i) := (hE i).1
    have : Module.Finite B (E.X i) := (hE i).2
    let : Module (A ⧸ I) (E.X i) := (E₀.X i).isModule
    let bE := Module.Free.chooseBasis B (E.X i)
    let b₀ : Module.Basis (Module.Free.ChooseBasisIndex B (E.X i)) (A ⧸ I) (E₀.X i) :=
      bE.mapCoeffs e.symm (by intro c x; change e (e.symm c) • x = c • x; simp)
    exact ⟨Module.Free.of_basis b₀, Module.Finite.of_basis b₀⟩
  obtain ⟨P, hPb, hPproj, hPC, ⟨hPE⟩⟩ :=
    CochainComplex.exists_projective_lift_of_nilpotent A I
      (by obtain ⟨n, hn⟩ := hnil; exact ⟨n + 1, by omega, by
            rw [pow_succ, hn, zero_mul]; rfl⟩)
      (L ⋙ D) ε₀ C E₀
      ⟨b, (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff E H b).2 hb⟩
      (fun i => by have := (hE₀ i).1; infer_instance)
      ⟨D.mapIso eE.symm ≪≫ H.mapDerivedCategoryFactors.app E⟩
  refine ⟨P, hPb, hPproj, hPC, fun i => ?_⟩
  let ei : F₀.obj (P.X i) ≅ E₀.X i := (HomologicalComplex.eval _ _ i).mapIso hPE
  have := (hE₀ i).1
  have := (hE₀ i).2
  exact ⟨Module.Free.of_equiv (ei.toLinearEquiv).symm,
    Module.Finite.equiv (ei.toLinearEquiv).symm⟩

namespace DerivedCategory

/-- Pseudo-coherence is detected after derived scalar extension along a surjective ring map
with nilpotent kernel. The functor `L`, with its universal counit `ε`, is the total left
derived functor of termwise extension of scalars; thus `L.obj K'` is precisely the derived
reduction, with no flatness assumption on the quotient.

Source: Stacks Project, More on Algebra, Tag 0H76
(auxiliary; not a blueprint node).

Proof: In the forward direction use a bounded-above finite-free representative. To apply
bounded-above K-flatness with independent ring and module universes, raise both rings by
`ULift`, transport the scalar-extension adjunction and its universal derived counit through
the restriction-of-scalars equivalences, and apply the module K-flat counit theorem.
Reflection of isomorphisms returns the counit calculation to the original rings. Termwise
scalar extension then gives the required bounded-above finite-free representative.

For the reverse direction identify B with A/ker φ and transport the universal derived pair
through this ring equivalence. The nilpotent projective-complex lifting theorem supplies a
bounded-above projective representative P whose reduction is the prescribed finite-free
complex. Lift a finite basis of each reduced term by projectivity of its free source.
Nilpotent Nakayama makes the resulting map surjective, so each term of P is finite.
The finite-projective freeness criterion modulo a Jacobson ideal now applies: every
1 + x with x in the nilpotent ideal is a unit. Hence P is termwise finite free and
represents the original derived object. Empty bases and the zero ring require no exception. -/
theorem isPseudoCoherent_iff_of_surjective_nilpotent_kernel
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars φ)
        (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive (.up ℤ) ⋙
          DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))]
    (K' : DerivedCategory (ModuleCat.{max u v} A)) :
    IsPseudoCoherent (L.obj K') ↔ IsPseudoCoherent K' := by
  classical
  constructor
  · intro h
    obtain ⟨P, ⟨b, hb⟩, hP, hPK, hred⟩ :=
      projective_model_with_free_reduction φ hφ hnil L ε K' h
    refine ⟨P, b, hb, fun i => ?_, hPK⟩
    have := hP i
    have := (hred i).1
    have := (hred i).2
    exact finite_free_of_nilpotent_reduction (RingHom.ker φ) hnil (P.X i)
  · rintro ⟨P, b, hb, hP, ⟨eP⟩⟩
    let : Algebra A B := φ.toAlgebra
    let F := ModuleCat.extendScalars.{u, u, max u v} φ
    have : F.Additive := (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
    let E : CochainComplex (ModuleCat.{max u v} B) ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj P
    have hE : E.IsStrictlyLE b := by
      apply (E.isStrictlyLE_iff b).2
      intro i hi
      exact F.map_isZero (P.isZero_of_isStrictlyLE b i hi)
    have hfree : ∀ i, Module.Free B (E.X i) ∧ Module.Finite B (E.X i) := by
      intro i
      have := (hP i).1
      have := (hP i).2
      change Module.Free B (TensorProduct A B (P.X i)) ∧ Module.Finite B (TensorProduct A B (P.X i))
      exact ⟨inferInstance, inferInstance⟩
    have := counit_isIso_of_boundedAbove_free φ L ε P b hb (fun i => (hP i).1)
    let e : L.obj (Q.obj P) ≅ Q.obj E :=
      (L.mapIso ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app P)).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} B)).app E
    exact ⟨E, b, hE, hfree, ⟨e.symm ≪≫ L.mapIso eP⟩⟩

end DerivedCategory
