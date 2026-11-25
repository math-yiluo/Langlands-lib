/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Scalar-extension tensor square for module coefficient change

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-extension-equation)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

open SheafOfModules
attribute [local instance] monoidalCategory symmetricCategory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] scalarAssociation SheafOfModules.monoidalCategory
attribute [local irreducible] extensionComparison extensionAdjunction
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification

set_option maxHeartbeats 80000 in
-- Keep dependent scalar-extension presentations explicit during elaboration.
private theorem scalarTensor_hom_ext₂
    {A B : Sheaf J CommRingCat.{w}} (c : A ⟶ B)
    (M N : Modules A) (H : Modules B)
    {f g : (changeOfRings c M ⊗ changeOfRings c N) ⟶ H}
    (h : ∀ W m n, f.val.app W (moduleTmul _ _ W
        (extensionTmul c M W 1 m) (extensionTmul c N W 1 n)) =
      g.val.app W (moduleTmul _ _ W
        (extensionTmul c M W 1 m) (extensionTmul c N W 1 n))) : f = g := by
  let RB := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 RB.obj)
  let S := PresheafOfModules.sheafification (𝟙 RB.obj)
  let E := changeOfRingsPresheaf c M
  let F := changeOfRingsPresheaf c N
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  let E2 := (S.obj E).val ⊗ (S.obj F).val
  have hη (V : PresheafOfModules.{w} RB.obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj))
        (adj.unit.app V) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)]
    change IsIso (S.map (adj.unit.app V))
    dsimp only [S, adj]
    infer_instance
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫
    (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := by
    dsimp only [q]
    infer_instance
  apply ((asIso q).symm.homFromEquiv).injective
  apply (adj.homEquiv (E ⊗ F) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing (RB.obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : (E.obj W) ⊗[RB.obj.obj W] (F.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app (E ⊗ F) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ f)).app W).hom
  let b : (E.obj W) ⊗[RB.obj.obj W] (F.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app (E ⊗ F) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ g)).app W).hom
  apply ModuleCat.hom_ext
  change a = b
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of (RB.obj.obj W) ((F.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
      (TensorProduct.curry a) =
      ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of (RB.obj.obj W) ((F.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
        (TensorProduct.curry b) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry a _ = TensorProduct.curry b _
    have hm : ModuleCat.ofHom (X := F.obj W) (Y := ModuleCat.of (RB.obj.obj W)
        (H.val.obj W)) (TensorProduct.curry a
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W) (Y := ModuleCat.of (RB.obj.obj W)
          (H.val.obj W)) (TensorProduct.curry b
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      change TensorProduct.curry a _ _ = TensorProduct.curry b _ _
      let m' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m
      let n' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n
      have he := congrArg (fun k ↦ k.app W (m' ⊗ₜ[B.obj.obj W] n'))
        (adj.unit.naturality (ηE ⊗ₘ ηF))
      change (adj.unit.app E2).app W (ηE.app W m' ⊗ₜ[B.obj.obj W] ηF.app W n') =
        (S.map (ηE ⊗ₘ ηF)).val.app W
          ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n')) at he
      change f.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W
            ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n')))) =
        g.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W
            ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n'))))
      rw [← he]
      rw [← moduleTmul]
      dsimp only [S, E, F, ηE, ηF, adj, RB, m', n']
      simpa only [extensionTmul, extensionFunctor, SheafOfModules.changeOfRings] using h W m n
    exact congrArg ModuleCat.Hom.hom hm
  exact TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh)

private theorem productElements {A : Type uE} [Category.{vE} A] [HasBinaryProducts A]
    (F : A ⥤ Type w) (X Y : A) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

-- Keep dependent scalar-extension presentations explicit during elaboration.
private theorem tensorPair_map {A : Sheaf J CommRingCat.{w}}
    {M N M' N' : Modules A} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying A).obj M) (y : Z ⟶ (underlying A).obj N)
    (a : M ⟶ M') (b : N ⟶ N') :
    moduleTensorPair x y ≫ (underlying A).map (a ⊗ₘ b) =
      moduleTensorPair (x ≫ (underlying A).map a) (y ≫ (underlying A).map b) := by
  apply Sheaf.hom_ext
  ext U t
  exact moduleTmul_map a b U _ _

attribute [local irreducible] moduleTensorPair generator moduleTmul extensionTmul
attribute [local irreducible] extensionFunctor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Normalize the dependent coefficient sources before rewriting the generator equations.
private theorem insertion_naturality {A B : Sheaf J CommRingCat.{w}} (c : A ⟶ B)
    {M N : Modules A} (a : M ⟶ N) :
    (underlying A).map a ≫ insertion c N =
      insertion c M ≫ (underlying B).map ((extensionFunctor c).map a) := by
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) ((extensionAdjunction c).unit.naturality a)

-- Control conversions through scalar-extension and sheafification presentations.
end CategoryTheory.CochainPullback
