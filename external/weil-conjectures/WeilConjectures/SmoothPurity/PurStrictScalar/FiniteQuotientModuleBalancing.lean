/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
import WeilConjectures.SmoothPurity.PurStrictScalar.RamifiedQuotientSectionPushout
import Mathlib.Algebra.Category.Ring.Constructions
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Tensor balancing for one finite quotient module

Source: Stacks Project, Modules on Sites, Tag 03EK, and tensor/quotient cancellation.
(blueprint: lem-pur-finite-quotient-module-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar
open scoped ChangeOfRings TensorProduct

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

attribute [local irreducible] PurCompactSupport.finiteChange PurCompactSupport.projection
  constantMap integralConstantToCompletionOfUniverses PurCompactSupport.finite

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Tensor cancellation for a single module over a positive finite quotient.
No naturality or uniqueness of the witnesses is assumed.

Source: Stacks Project, Modules on Sites, Tag 03EK (tensor/restriction adjunction),
and the quotient tensor calculation in Step 7 of
`lem-pur-compact-support-strict-scalar-mate`.
(blueprint: lem-pur-finite-quotient-module-balancing).

Proof: write A = O_E, B = O_F and r = n+1. The ramification hypothesis gives
(t^r)B = (v^(er)), by taking rth powers of the stated equality of ideals.
Consequently B tensor_A (A/t^r) is B/v^(er), compatibly with both quotient maps.
For a module M over the constant sheaf of A/t^r, the balanced map sends b tensor x
to bar(b) tensor x. Its inverse sends bar(b) tensor x to b tensor x: changing a
lift by an element of t^r B gives zero since t^r annihilates M. Equivalently use
the tensor/quotient universal property, without requiring sectionwise lifts of
arbitrary sheafified sections. These inverse presheaf maps commute with restriction
and descend through module sheafification. The constant-to-completion map followed
by the completed quotient projection is the constant quotient map. Transport the
comparison through the specified ordinary scalar functors using their object
identifications with sheafified tensors. This gives exactly the displayed formula
on every original pure tensor. Only this one module and this one exponent are
involved; no compatibility among independently chosen witnesses is asserted.
For M = 0 or an empty site object the maps are the unique zero-module maps;
r and er are positive, so both quotient projections have the stated indices. -/
theorem finiteQuotientModuleBalancing_exists (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ)
    (M : pbcModules W ((PurCompactSupport.finite l E (n + 1)
      (Nat.le_add_left 1 n)).ring W)) :
    ∃ β : (pbcExtend (constantMap l E F i W)).obj
        ((pbcRestrict (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) W) ⋙
          SheafOfModules.restrictScalars.{u + 1}
            (integralConstantToCompletionOfUniverses l E W)).obj M) ≅
      (pbcRestrict (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W) ⋙
        SheafOfModules.restrictScalars.{u + 1}
            (integralConstantToCompletionOfUniverses l F W)).obj
        ((pbcExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map W)).obj M),
      ∀ (U : W.ProEtᵒᵖ) (b : ((constants l F).ring W).obj.obj U) (x : M.val.obj U),
        β.hom.val.app U
            (pbcTensorSection (constantMap l E F i W)
              ((pbcRestrict (PurCompactSupport.projection l E (n + 1)
                (Nat.le_add_left 1 n) W) ⋙
                SheafOfModules.restrictScalars.{u + 1}
                  (integralConstantToCompletionOfUniverses l E W)).obj M) U b x) =
          pbcTensorSection
            ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n)).map W) M U
            (((PurCompactSupport.projection l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W).hom.app U)
              (((integralConstantToCompletionOfUniverses l F W).hom.app U) b)) x := by
  exact tensorBalancingOfSectionPushouts W (constantMap l E F i W)
    ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)).map W)
    (integralConstantToCompletionOfUniverses l E W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W))
    (integralConstantToCompletionOfUniverses l F W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W))
    (ramifiedQuotient_sectionPushout l E F i W e he hepos n) M

end WeilConjectures.PurStrictScalar
