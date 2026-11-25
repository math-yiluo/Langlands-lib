/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement

/-! # Root-normalized scalar extension in exponent one

Source: coefficient Tate twists, scalar extension of the integral first line;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open CategoryTheory.Limits
open scoped ChangeOfRings

private theorem firstRootDiscreteSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
      (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
    purTwistIntegralCompletionMap S l E ≫ integralCompletedScalarMap l E L ι S =
      β ≫ purTwistIntegralCompletionMap S l L := by
  dsimp only
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  apply limit.hom_ext
  intro n
  have hE := (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n.unop
  have hL := (purTwistIntegralCompletionMap_existsUnique S l L).exists.choose_spec n.unop
  have hα := (integralCompletedScalarMap_existsUnique l E L ι S).exists.choose_spec n.unop
  change purTwistIntegralCompletionMap S l E ≫ _ = _ at hE
  change purTwistIntegralCompletionMap S l L ≫ _ = _ at hL
  change integralCompletedScalarMap l E L ι S ≫ _ = _ at hα
  let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
  have hq : purTwistIntegralQuotient S l E n.unop ≫
      integralScalarQuotientSheafMap l E L ι S n.unop =
        β ≫ purTwistIntegralQuotient S l L n.unop := by
    dsimp [β, purTwistIntegralQuotient, integralScalarQuotientSheafMap]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have h : (purTwistIntegralCompletionMap S l E ≫ integralCompletedScalarMap l E L ι S) ≫
      completedIntegralCommRingProjectionUnrestricted l L S n.unop =
        (β ≫ purTwistIntegralCompletionMap S l L) ≫
          completedIntegralCommRingProjectionUnrestricted l L S n.unop := by
    rw [Category.assoc, hα]
    change purTwistIntegralCompletionMap S l E ≫
      (completedIntegralCommRingProjectionUnrestricted l E S n.unop ≫ _) = _
    rw [← Category.assoc, hE, hq, Category.assoc, hL]
  exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

private theorem firstRootConstantSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
      (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
    purTwistConstantIntegersMap S l E ≫ β = purTwistConstantIntegersMap S l L := by
  dsimp [purTwistConstantIntegersMap]
  rw [← Functor.map_comp]
  congr 1
  ext z
  change ι (purTwistIntegersMap l E z.down : E) = (purTwistIntegersMap l L z.down : L)
  have hE := (purTwistIntegersMap_existsUnique l E).exists.choose_spec z.down
  have hL := (purTwistIntegersMap_existsUnique l L).exists.choose_spec z.down
  change (purTwistIntegersMap l E z.down : E) = _ at hE
  change (purTwistIntegersMap l L z.down : L) = _ at hL
  exact (congrArg ι hE).trans ((ι.commutes (z.down : ℚ_[l])).trans hL.symm)

private theorem firstRootCompletedSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    purTwistCompletedScalarMap S l E ≫ integralCompletedScalarMap l E L ι S =
      purTwistCompletedScalarMap S l L := by
  let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
  have hd := firstRootDiscreteSquare l E S L ι
  have hc := firstRootConstantSquare l E S L ι
  have hconst : purTwistZlCompletionMap S l ≫
      (purTwistCompletedScalarMap S l E ≫ integralCompletedScalarMap l E L ι S) =
        purTwistZlCompletionMap S l ≫ purTwistCompletedScalarMap S l L := by
    rw [← Category.assoc, purTwistCoefficientSquare, Category.assoc, hd,
      ← Category.assoc, hc, purTwistCoefficientSquare]
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  apply limit.hom_ext
  intro n
  obtain ⟨k, q, hq, hE⟩ :=
    (purTwistCompletedScalarMap_existsUnique S l E).exists.choose_spec n.unop
  obtain ⟨m, q', hq', hL⟩ :=
    (purTwistCompletedScalarMap_existsUnique S l L).exists.choose_spec n.unop
  have hα := (integralCompletedScalarMap_existsUnique l E L ι S).exists.choose_spec n.unop
  let Q : purTwistFiniteRing S l k ⟶ integralCoefficientCommRingSheaf l E S n.unop :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (q.comp ULift.ringEquiv.toRingHom)))
  let Q' : purTwistFiniteRing S l m ⟶ integralCoefficientCommRingSheaf l L S n.unop :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (q'.comp ULift.ringEquiv.toRingHom)))
  change purTwistCompletedScalarMap S l E ≫ _ = purTwistZlProjection S l k ≫ Q at hE
  change purTwistCompletedScalarMap S l L ≫ _ = purTwistZlProjection S l m ≫ Q' at hL
  change integralCompletedScalarMap l E L ι S ≫ _ = _ at hα
  have h : (purTwistCompletedScalarMap S l E ≫ integralCompletedScalarMap l E L ι S) ≫
      completedIntegralCommRingProjectionUnrestricted l L S n.unop =
        purTwistCompletedScalarMap S l L ≫
          completedIntegralCommRingProjectionUnrestricted l L S n.unop := by
    rw [Category.assoc, hα]
    change purTwistCompletedScalarMap S l E ≫
      (completedIntegralCommRingProjectionUnrestricted l E S n.unop ≫ _) = _
    rw [← Category.assoc, hE, Category.assoc, hL]
    apply purTwistZlFiniteFactor_ext
    have h := congrArg
      (fun f ↦ f ≫ completedIntegralCommRingProjectionUnrestricted l L S n.unop) hconst
    rw [Category.assoc, Category.assoc, hα] at h
    change purTwistZlCompletionMap S l ≫
      (purTwistCompletedScalarMap S l E ≫
        (completedIntegralCommRingProjectionUnrestricted l E S n.unop ≫ _)) = _ at h
    rw [← Category.assoc (purTwistCompletedScalarMap S l E), hE] at h
    simp only [Category.assoc, hL] at h
    have hk := (purTwistZlCompletionMap_existsUnique S l).exists.choose_spec k
    have hm := (purTwistZlCompletionMap_existsUnique S l).exists.choose_spec m
    change purTwistZlCompletionMap S l ≫ _ = purTwistZlReductionOfUniverses S l k at hk
    change purTwistZlCompletionMap S l ≫ _ = purTwistZlReductionOfUniverses S l m at hm
    rw [← hk, ← hm]
    simpa only [Category.assoc] using h
  exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

private noncomputable def firstRootIntegralIso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistCompletedScalarMap S l E) (purTwistZlModule S l) ≅
        purTwistIntegralModule S l E := by
  have := integralExtensionReverse_isIso S l E
  exact asIso (integralExtensionReverse S l E)

private theorem firstRootIntegralIso_tmul
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (firstRootIntegralIso S l E).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (purTwistCompletedScalarMap S l E)
        (purTwistZlModule S l) U ((purTwistIntegralCompletionMap S l E).hom.app U a) x) =
          purTwistIntegralTensor S l E U a x := by
  change (integralExtensionReverse S l E).val.app U _ = _
  rw [integralExtensionReverse_section]
  apply ((purTwistIntegralAction_existsUnique S l E).exists.choose_spec.2.1
    U a (purTwistIntegralTensor S l E U 1 x)).trans
  exact (SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap S l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)) U a 1 x).trans
      (congrArg (fun z ↦ purTwistIntegralTensor S l E U z x) (mul_one a))

attribute [local irreducible] firstRootIntegralIso

private theorem firstRootHomExt
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (c d : purTwistIntegralModule S l E ⟶
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι S))).obj (purTwistIntegralModule S l L))
    (h : ∀ (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
      (x : (purTwistZlModule S l).val.obj U),
      c.val.app U (purTwistIntegralTensor S l E U a x) =
        d.val.app U (purTwistIntegralTensor S l E U a x)) : c = d := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistIntegralCompletionMap S l E))
  have H : F.map c = F.map d := by
    apply (cancel_epi (integralForgetIso S l E).inv).mp
    apply SheafOfModules.scalarExtension_hom_ext (purTwistConstantIntegersMap S l E)
    intro U a x
    change c.val.app U (purTwistIntegralTensor S l E U a x) =
      d.val.app U (purTwistIntegralTensor S l E U a x)
    exact h U a x
  ext U x
  exact congrArg (fun f ↦ f.val.app U x) H

private noncomputable def firstRootExtensionIso
    (S : Scheme.{u}) {R T : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (α : R ⟶ T)
    {M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (e : M ≅ N) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M ≅
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α N where
  hom := SheafOfModules.changeOfRingsHomOfUniverses α M e.hom
  inv := SheafOfModules.changeOfRingsHomOfUniverses α N e.inv
  hom_inv_id := by
    apply SheafOfModules.scalarExtension_hom_ext α M
    intro U a x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [SheafOfModules.scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      α e.hom U a x,
      SheafOfModules.scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
        α e.inv U a (e.hom.val.app U x)]
    have h : e.inv.val.app U (e.hom.val.app U x) = x :=
      congrArg (fun f ↦ f.val.app U x) e.hom_inv_id
    rw [h]
    rfl
  inv_hom_id := by
    apply SheafOfModules.scalarExtension_hom_ext α N
    intro U a x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [SheafOfModules.scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      α e.inv U a x,
      SheafOfModules.scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
        α e.hom U a (e.inv.val.app U x)]
    have h : e.hom.val.app U (e.inv.val.app U x) = x :=
      congrArg (fun f ↦ f.val.app U x) e.inv_hom_id
    rw [h]
    rfl

private theorem firstRootExtensionIso_hom
    (S : Scheme.{u}) {R T : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (α : R ⟶ T)
    {M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (e : M ≅ N) :
    (firstRootExtensionIso S α e).hom =
      SheafOfModules.changeOfRingsHomOfUniverses α M e.hom := rfl

attribute [local irreducible] firstRootExtensionIso

attribute [local irreducible] SheafOfModules.changeOfRingsHomOfUniverses
  SheafOfModules.scalarExtensionSection

private noncomputable def firstRootTowerIso
    (S : Scheme.{u}) {R A B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (p : R ⟶ A) (α : A ⟶ B)
    (N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)}
    {P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)}
    (e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p N ≅ M)
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (p ≫ α) N ≅ P) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M ≅ P :=
  firstRootExtensionIso S α e.symm ≪≫
    SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} p α N ≪≫ f

private theorem firstRootTowerIso_tmul
    (S : Scheme.{u}) {R A B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (p : R ⟶ A) (α : A ⟶ B)
    (N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)}
    {P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)}
    (e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p N ≅ M)
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (p ≫ α) N ≅ P)
    (U : S.ProEtᵒᵖ) (a : A.obj.obj U) (x : N.val.obj U) :
    (firstRootTowerIso S p α N e f).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M U 1
        (e.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p N U a x))) =
      f.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} (p ≫ α) N U
        (α.hom.app U a) x) := by
  dsimp only [firstRootTowerIso, Iso.trans_hom]
  rw [firstRootExtensionIso_hom]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Iso.symm_hom]
  rw [SheafOfModules.scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
    α e.inv U 1 (e.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      p N U a x))]
  have he : e.inv.val.app U
      (e.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p N U a x)) =
        SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p N U a x :=
    congrArg (fun g ↦ g.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      p N U a x))
      e.hom_inv_id
  rw [he, SheafOfModules.scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1} p α N,
    SheafOfModules.scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
      p α N U 1 a x, one_mul]

attribute [local irreducible] firstRootTowerIso

private noncomputable def firstRootTransportIso
    (S : Scheme.{u}) {R T : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {p q : R ⟶ T} (h : p = q)
    (N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)}
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} q N ≅ P) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p N ≅ P := by
  cases h
  exact f

private theorem firstRootTransportIso_tmul
    (S : Scheme.{u}) {R T : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    {p q : R ⟶ T} (h : p = q)
    (N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    {P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T)}
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} q N ≅ P)
    (U : S.ProEtᵒᵖ) (a : T.obj.obj U) (x : N.val.obj U) :
    (firstRootTransportIso S h N f).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} p N U a x) =
        f.hom.val.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          q N U a x) := by
  cases h
  rfl

attribute [local irreducible] firstRootTransportIso

private noncomputable def firstRootTargetIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistCompletedScalarMap S l E ≫ integralCompletedScalarMap l E L ι S)
        (purTwistZlModule S l) ≅ purTwistIntegralModule S l L :=
  firstRootTransportIso S (firstRootCompletedSquare l E S L ι)
    (purTwistZlModule S l) (firstRootIntegralIso S l L)

private theorem firstRootTargetIso_tmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (U : S.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L S).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (firstRootTargetIso l E S L ι).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (purTwistCompletedScalarMap S l E ≫ integralCompletedScalarMap l E L ι S)
        (purTwistZlModule S l) U a x) =
      (firstRootIntegralIso S l L).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (purTwistCompletedScalarMap S l L)
          (purTwistZlModule S l) U a x) := by
  exact firstRootTransportIso_tmul S (firstRootCompletedSquare l E S L ι)
    (purTwistZlModule S l) (firstRootIntegralIso S l L) U a x

attribute [local irreducible] firstRootTargetIso

private noncomputable def firstRootCoefficientIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (integralCompletedScalarMap l E L ι S) (purTwistIntegralModule S l E) ≅
        purTwistIntegralModule S l L :=
  firstRootTowerIso S (purTwistCompletedScalarMap S l E)
    (integralCompletedScalarMap l E L ι S) (purTwistZlModule S l)
    (firstRootIntegralIso S l E) (firstRootTargetIso l E S L ι)

private theorem firstRootCoefficientIso_tmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
      (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
    (firstRootCoefficientIso l E S L ι).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (integralCompletedScalarMap l E L ι S)
        (purTwistIntegralModule S l E) U 1 (purTwistIntegralTensor S l E U a x)) =
          purTwistIntegralTensor S l L U (β.hom.app U a) x := by
  let α := integralCompletedScalarMap l E L ι S
  let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
  change (firstRootTowerIso S (purTwistCompletedScalarMap S l E) α
    (purTwistZlModule S l) (firstRootIntegralIso S l E)
    (firstRootTargetIso l E S L ι)).hom.val.app U _ = _
  erw [← firstRootIntegralIso_tmul S l E U a x]
  erw [firstRootTowerIso_tmul S (purTwistCompletedScalarMap S l E) α
    (purTwistZlModule S l) (firstRootIntegralIso S l E) (firstRootTargetIso l E S L ι)
    U ((purTwistIntegralCompletionMap S l E).hom.app U a) x]
  erw [firstRootTargetIso_tmul]
  have hd := congrArg (fun f ↦ (f.hom.app U).hom a) (firstRootDiscreteSquare l E S L ι)
  change α.hom.app U ((purTwistIntegralCompletionMap S l E).hom.app U a) =
    (purTwistIntegralCompletionMap S l L).hom.app U (β.hom.app U a) at hd
  erw [hd]
  exact firstRootIntegralIso_tmul S l L U (β.hom.app U a) x

attribute [local irreducible] firstRootCoefficientIso

/-- Extension of the first integral root line is the first target root line.
The root-tensor formula also determines its semilinear adjunct among all maps.
Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-def-sp-tate-twist/def-coefficient-twists-detailed.md, the integral first line;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-pur-first-root-coefficient-scalar-comparison).
Proof: the finite quotient projections identify the completed coefficient map
with the discrete integer inclusion on constants. The two completed Z_l maps
then agree by finite-factor extensionality and their constant restrictions.
Reuse the canonical isomorphism from the completed extension of the common
root-limit module to each integral line, constructed in the integral local-model
proof. Extend the inverse source isomorphism, apply the scalar-tower isomorphism,
transport along the completed coefficient equality, and apply the target
isomorphism. Their pure-tensor formulas give the asserted normalization.
For uniqueness restrict the competing maps to the discrete integer action.
The canonical forgetful isomorphism identifies the source with its original
sheafified tensor presentation. Tensor and sheafification extensionality then
identify the two maps from their values on pure tensors, and equality of the
restricted maps is equality of the original maps. No invertibility of a competing
map or global lifting of sheafified sections is used. The constructions and
universal properties also apply to the empty scheme and the identity inclusion. -/
theorem firstRootCoefficientScalarComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :
    let α := integralCompletedScalarMap l E L ι S
    let β : purTwistIntegralConstant S l E ⟶ purTwistIntegralConstant S l L :=
      (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((integralScalarIntegerInclusion l E L ι).comp ULift.ringEquiv.toRingHom)))
    let res := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
    ∃ b : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        α (purTwistIntegralModule S l E) ≅ purTwistIntegralModule S l L,
      (∀ (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistZlModule S l).val.obj U),
        b.hom.val.app U (SheafOfModules.scalarExtensionSection α
          (purTwistIntegralModule S l E) U 1 (purTwistIntegralTensor S l E U a x)) =
            purTwistIntegralTensor S l L U (β.hom.app U a) x) ∧
      ∀ c : purTwistIntegralModule S l E ⟶ res.obj (purTwistIntegralModule S l L),
        (∀ (U : S.ProEtᵒᵖ) (a : (purTwistIntegralConstant S l E).obj.obj U)
          (x : (purTwistZlModule S l).val.obj U),
          c.val.app U (purTwistIntegralTensor S l E U a x) =
            purTwistIntegralTensor S l L U (β.hom.app U a) x) →
        c = SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α
            (purTwistIntegralModule S l E) ≫
          res.map b.hom := by
  classical
  refine ⟨firstRootCoefficientIso l E S L ι, firstRootCoefficientIso_tmul l E S L ι, ?_⟩
  intro c hc
  apply firstRootHomExt l E S L ι
  intro U a x
  apply (hc U a x).trans
  exact (firstRootCoefficientIso_tmul l E S L ι U a x).symm

end WeilConjectures
