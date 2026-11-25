/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Completed.CompletedConstantSquarePushout
import Mathlib.Algebra.Category.Ring.Constructions
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Existence of the ordinary compact-support coefficient comparison

This is the existence part of the ordinary constant/completed scalar comparison.
(blueprint: lem-pur-compact-support-coefficient-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

namespace PurStrictScalar
open scoped ChangeOfRings TensorProduct

-- The sectionwise tensor-balancing argument follows the finite quotient construction.
private theorem sectionBalancing {A B C D : CommRingCat.{u + 1}}
    (f : A ⟶ B) (g : A ⟶ C) (p : B ⟶ D) (q : C ⟶ D)
    (h : IsPushout f g p q) (M : ModuleCat.{u + 1} C) :
    ∃ e : (ModuleCat.extendScalars f.hom).obj
        ((ModuleCat.restrictScalars g.hom).obj M) ≅
      (ModuleCat.restrictScalars p.hom).obj ((ModuleCat.extendScalars q.hom).obj M),
      ∀ (b : B) (m : M), e.hom (b ⊗ₜ[A, f.hom] m) = p b ⊗ₜ[C, q.hom] m := by
  let : Algebra A B := f.hom.toAlgebra
  let : Algebra A C := g.hom.toAlgebra
  let : Algebra B D := p.hom.toAlgebra
  let : Algebra C D := q.hom.toAlgebra
  let : Algebra A D := (q.hom.comp g.hom).toAlgebra
  have hc : p.hom.comp f.hom = q.hom.comp g.hom :=
    congrArg CommRingCat.Hom.hom h.w
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' hc.symm
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp h
  let : Module A M := Module.compHom M g.hom
  have : IsScalarTower A C M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact ⟨(Algebra.IsPushout.cancelBaseChange A B C D M).symm.toModuleIso,
    fun b m ↦ Algebra.IsPushout.cancelBaseChange_symm_tmul A B C D M b m⟩

private theorem tensorBalancingOfSectionPushouts (W : Scheme.{u})
    {A B C D : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (f : A ⟶ B) (q : C ⟶ D)
    (g : (adicLisseForget W).obj A ⟶ (adicLisseForget W).obj C)
    (p : (adicLisseForget W).obj B ⟶ (adicLisseForget W).obj D)
    (h : ∀ U : W.ProEtᵒᵖ, IsPushout (f.hom.app U)
      (CommRingCat.ofHom (show A.obj.obj U →+* C.obj.obj U from (g.hom.app U).hom))
      (CommRingCat.ofHom (show B.obj.obj U →+* D.obj.obj U from (p.hom.app U).hom))
      (q.hom.app U))
    (M : pbcModules W C) :
    ∃ e : (pbcExtend f).obj ((SheafOfModules.restrictScalars g).obj M) ≅
        (SheafOfModules.restrictScalars p).obj ((pbcExtend q).obj M),
      ∀ (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
        e.hom.val.app U
          (pbcTensorSection f ((SheafOfModules.restrictScalars g).obj M) U b m) =
        pbcTensorSection q M U ((p.hom.app U) b) m := by
  let N := (SheafOfModules.restrictScalars g).obj M
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} f N
  let Q := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} q M
  let eU (U : W.ProEtᵒᵖ) :=
    (sectionBalancing (f.hom.app U)
      (CommRingCat.ofHom (show A.obj.obj U →+* C.obj.obj U from (g.hom.app U).hom))
      (CommRingCat.ofHom (show B.obj.obj U →+* D.obj.obj U from (p.hom.app U).hom))
      (q.hom.app U) (h U) (M.val.obj U)).choose
  have heU (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
      (eU U).hom (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m) =
        (show D.obj.obj U from (p.hom.app U) b) ⊗ₜ[C.obj.obj U, (q.hom.app U).hom] m :=
    (sectionBalancing (f.hom.app U)
      (CommRingCat.ofHom (show A.obj.obj U →+* C.obj.obj U from (g.hom.app U).hom))
      (CommRingCat.ofHom (show B.obj.obj U →+* D.obj.obj U from (p.hom.app U).hom))
      (q.hom.app U) (h U) (M.val.obj U)).choose_spec b m
  let ep : P ≅ (PresheafOfModules.restrictScalars p.hom).obj Q :=
    PresheafOfModules.isoMk eU (by
      intro U V v
      ext z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b m =>
        change (eU V).hom (P.map v (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m)) =
          Q.map v ((eU U).hom (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m))
        have hs := (SheafOfModules.exists_changeOfRingsMap f N v).choose_spec b m
        have ht := (SheafOfModules.exists_changeOfRingsMap q M v).choose_spec
          (show D.obj.obj U from (p.hom.app U) b) (show M.val.obj U from m)
        have hp := ConcreteCategory.congr_hom (p.hom.naturality v) b
        exact (congrArg (eU V).hom hs).trans
          ((heU V (B.obj.map v b) (M.val.map v m)).trans
            ((congrArg (fun d : D.obj.obj V ↦
              d ⊗ₜ[C.obj.obj V, (q.hom.app V).hom]
                (show M.val.obj V from M.val.map v m)) hp).trans
              (ht.symm.trans (congrArg (Q.map v) (heU U b m).symm)))))
  let es := (PresheafOfModules.sheafification
      (𝟙 ((adicLisseForget W).obj B).obj)).mapIso ep ≪≫
    SheafOfModules.cancellationRestrictSheafifyIso p Q
  let hf := (pbcExtensionExistence f).choose_spec.choose N
  let hq := (pbcExtensionExistence q).choose_spec.choose M
  let e := eqToIso hf ≪≫ es ≪≫
    (SheafOfModules.restrictScalars p).mapIso (eqToIso hq).symm
  refine ⟨e, ?_⟩
  intro U b m
  have hn := congrArg (fun k ↦ k.app U
    (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m))
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((adicLisseForget W).obj B).obj)).unit.naturality ep.hom)
  have hc := SheafOfModules.cancellationRestrictSheafifyHom_toSheaf p Q
  have hcU := congrArg (fun k ↦ k.hom.app U) hc
  have hcApp (x) : (SheafOfModules.cancellationRestrictSheafifyIso p Q).hom.val.app U x =
      x := congrArg (fun k ↦ k x) hcU
  change ((toSheafify (ProEt.topology W) Q.presheaf).app U)
      ((eU U).hom (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m)) = _ at hn
  have hs : es.hom.val.app U
      ((toSheafify (ProEt.topology W) P.presheaf).app U
        (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m)) =
      (toSheafify (ProEt.topology W) Q.presheaf).app U
        ((show D.obj.obj U from (p.hom.app U) b) ⊗ₜ[C.obj.obj U, (q.hom.app U).hom] m) := by
    change (SheafOfModules.cancellationRestrictSheafifyIso p Q).hom.val.app U
      (((PresheafOfModules.sheafification
        (𝟙 ((adicLisseForget W).obj B).obj)).map ep.hom).val.app U
          ((toSheafify (ProEt.topology W) P.presheaf).app U
            (b ⊗ₜ[A.obj.obj U, (f.hom.app U).hom] m))) = _
    exact (hcApp _).trans (hn.symm.trans (congrArg
      ((toSheafify (ProEt.topology W) Q.presheaf).app U) (heU U b m)))
  have hid (x) : (eqToHom hf).val.app U ((eqToHom hf.symm).val.app U x) = x := by
    change ((eqToIso hf).inv ≫ (eqToIso hf).hom).val.app U x = x
    rw [Iso.inv_hom_id]
    rfl
  unfold pbcTensorSection completedAdicChangeTensor
  change (eqToHom hq.symm).val.app U
      (es.hom.val.app U ((eqToHom hf).val.app U
        ((eqToHom hf.symm).val.app U _))) = _
  exact congrArg ((eqToHom hq.symm).val.app U)
    ((congrArg (es.hom.val.app U) (hid _)).trans hs)

end PurStrictScalar

/-- The ordinary balancing map exists on the constant coefficient model.
Source: Bhatt--Scholze 6.8.2(1), Definition 3.4.10.
(blueprint: lem-pur-compact-support-coefficient-models-ordinary-existence).
Proof: put A = O_E, B = O_F and write R and S for the completed coefficient
sheaves. Choose a finite A-basis b_i of B. Its quotient bases identify S with the
finite free R-module with basis completion(b_i): a finite direct sum commutes with
the inverse limit defining the completed coefficients. Thus the multiplication map
R tensor_A B to S is an isomorphism, sending r tensor b to r * completion(b).
For the fixed R-module sheaf M, associate the tensor products and use this ring
isomorphism to identify M tensor_A B with M tensor_R S. Equivalently, the forward
map is b tensor x to completion(b) tensor x. To invert it, write a local coefficient
s of S uniquely as sum_i r_i * completion(b_i), and send s tensor x to
sum_i b_i tensor (r_i * x). Uniqueness of the coordinates makes this balanced over R;
the multiplication matrices of B in the basis prove B-linearity. The two composites
are the identity on pure tensors. The maps commute with restrictions, so the
presheaf tensor maps induce inverse morphisms after sheafification. Their formula
is the displayed one for every local b and x. This argument constructs each
component only; naturality in M and uniqueness are proved in the parent. -/
theorem compactSupportCoefficientModels_ordinary_exists (W : Scheme.{u})
    [HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1}]
    [(ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ∀ M : scalarReductionSource l E W,
      ∃ β : (pbcExtend (PurStrictScalar.constantMap l E F i W)).obj
          ((PurStrictScalar.constantRestriction l E W).obj M) ≅
        (PurStrictScalar.constantRestriction l F W).obj
          ((pbcExtend (completedCoefficientMap l E F i W)).obj M),
      ∀ (U : W.ProEtᵒᵖ)
        (b : ((PurStrictScalar.constants l F).ring W).obj.obj U) (x : M.val.obj U),
        β.hom.val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  intro M
  exact PurStrictScalar.tensorBalancingOfSectionPushouts W
    (PurStrictScalar.constantMap l E F i W)
    (completedCoefficientMap l E F i W)
    (integralConstantToCompletionOfUniverses l E W)
    (integralConstantToCompletionOfUniverses l F W)
    (fun U ↦ completedConstantSquare_isPushout l E F i W U) M

end WeilConjectures
