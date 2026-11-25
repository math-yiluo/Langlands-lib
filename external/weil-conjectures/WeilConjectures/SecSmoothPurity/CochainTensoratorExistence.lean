/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.CochainInverseComparison

/-! # Ordinary tensorator for independent site sizes

Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).

The insertion is constructed on sections by the sheafification of `1 ⊗ m`.
Scalar extension and the normalized composite tensorator are constructed below.
The proof uses only tensor preservation of the specified algebraic inverse image.
-/

@[expose] public section

universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct
namespace SheafOfModules.CochainScalarConstruction
set_option autoImplicit false
set_option maxErrors 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
private abbrev ringSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable abbrev restriction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private local instance
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A : Sheaf K CommRingCat.{u}} (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{vC, uC, u} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{vC, uC, u} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{vC, uC, u} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{vC, uC, u} c M ⟶
      changeOfRingsPresheaf.{vC, uC, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{vC, uC, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{vC, uC, u} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    {M N : SheafOfModules.{u} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{vC, uC, u} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A))
    {H H' : SheafOfModules.{u} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

private noncomputable def tensorUnit
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A)) :
    (underlying A).obj M ⟶ (underlying S).obj ((tensorFunctor c).obj M) :=
  (underlying A).map ((tensorAdjunction c).unit.app M)

private theorem tensorUnit_apply
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    (W : Dᵒᵖ) (m : M.val.obj W) :
    (tensorUnit c M).hom.app W m =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).unit.app
        (changeOfRingsPresheaf.{vC, uC, u} c M)).app W
          ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
  change ((tensorAdjunction c).unit.app M).val.app W m = _
  rw [← Adjunction.homEquiv_id, tensorAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem tensorAdjunction_underlying
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : (tensorFunctor c).obj M ⟶ H) :
    (underlying A).map ((tensorAdjunction c).homEquiv M H f) =
      tensorUnit c M ≫ (underlying S).map f := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

section Pure
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- Pure tensors commute with restriction. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private theorem pure_restrict (M N : SheafOfModules.{u} (ringSheaf R))
    {W V : Cᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.map i (pure R M N W m n) =
      pure R M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  let v := m ⊗ₜ[R.obj.obj W] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

/-- The canonical bilinear pairing, as a presheaf morphism.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private noncomputable def pureMap (M N : SheafOfModules.{u} (ringSheaf R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

/-- The linear pairing on sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private noncomputable def pureBilin (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ) :
    M.val.obj W →ₗ[R.obj.obj W] N.val.obj W →ₗ[R.obj.obj W]
      ((monoidalCategory R).tensorObj M N).val.obj W :=
  TensorProduct.curry ((pureMap R M N).app W).hom

/-- A map from a tensor is determined by pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node).
Proof: use the module sheafification adjunction, then sectionwise tensor generation. -/
private theorem pure_hom_ext (M N H : SheafOfModules.{u} (ringSheaf R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ W m n, f.val.app W (pure R M N W m n) =
      g.val.app W (pure R M N W m n)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : SheafOfModules.{u} (ringSheaf R))
    {T T' : SheafOfModules.{u} (ringSheaf R)} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (A.val ◁ f.val) := by
  have h :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheaf R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : SheafOfModules.{u} (ringSheaf R)}
    (f : A' ⟶ A) (T : SheafOfModules.{u} (ringSheaf R)) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ▷ T.val) := by
  have h :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheaf R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification F' G').hom =
      (tensorObjIsoSheafification F G).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf pairing into the sheaf tensor is natural in both modules.
Source: Stacks Project, Modules on Sites, Tag 03EK
(auxiliary; not a blueprint node). -/
private theorem pureMap_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    pureMap R F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ pureMap R F' G' := by
  let := monoidalCategory R
  have h : (tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg Hom.val h
  change (tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val ≫
      (tensorObjIsoSheafification F' G').inv.val at hval
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit
  have hn := η.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ η.app (F'.val ⊗ G'.val) =
    η.app (F.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val at hn
  unfold pureMap
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

/-- Tensor morphisms act componentwise on pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
private theorem pure_map {M M' N N' : SheafOfModules.{u} (ringSheaf R)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W (pure R M N W m n) =
      pure R M' N' W (f.val.app W m) (g.val.app W n) := by
  exact congrArg (fun k ↦ k.app W (m ⊗ₜ[R.obj.obj W] n)) (pureMap_natural R f g)
end Pure

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)

private noncomputable def rawContraction
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    (changeOfRingsPresheaf.{vC, uC, u} c M).obj W ⊗[B.obj.obj W]
      (changeOfRingsPresheaf.{vC, uC, u} c N).obj W →ₗ[B.obj.obj W]
        (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N)).obj W := by
  letI := (c.hom.app W).hom.toAlgebra
  exact ((ModuleCat.extendScalars (c.hom.app W).hom).map
    ((pureMap A M N).app W)).hom.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        (A.obj.obj W) (B.obj.obj W) (M.val.obj W) (N.val.obj W)).symm.toLinearMap

private theorem rawContraction_tmul
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ)
    (s t : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    rawContraction c M N W
      ((s ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
        (t ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
      (s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n := by
  let := (c.hom.app W).hom.toAlgebra
  change ((ModuleCat.extendScalars (c.hom.app W).hom).map
    ((pureMap A M N).app W)).hom
      ((TensorProduct.AlgebraTensorModule.distribBaseChange
        (A.obj.obj W) (B.obj.obj W) (M.val.obj W) (N.val.obj W)).symm
          ((s ⊗ₜ[A.obj.obj W] m) ⊗ₜ[B.obj.obj W] (t ⊗ₜ[A.obj.obj W] n))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

private noncomputable def rawPairing
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    (changeOfRingsPresheaf.{vC, uC, u} c M).obj W →ₗ[B.obj.obj W]
      (changeOfRingsPresheaf.{vC, uC, u} c N).obj W →ₗ[B.obj.obj W]
        (changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N)).val.obj W :=
  TensorProduct.curry
    ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
      (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N))).app W).hom.comp
        (rawContraction c M N W))

private theorem rawPairing_tmul
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ)
    (s t : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    rawPairing c M N W
      (s ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
      (t ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) =
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
      (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N))).app W
        ((s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n)) := by
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
    (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N))).app W
      (rawContraction c M N W _) = _)
  exact congrArg _ (rawContraction_tmul c M N W s t m n)

private theorem rawPairing_restrict
    (M N : SheafOfModules.{u} (ringSheaf A)) {W V : Cᵒᵖ} (i : W ⟶ V)
    (x : (changeOfRingsPresheaf.{vC, uC, u} c M).obj W)
    (y : (changeOfRingsPresheaf.{vC, uC, u} c N).obj W) :
    rawPairing c M N V ((changeOfRingsPresheaf.{vC, uC, u} c M).map i x)
      ((changeOfRingsPresheaf.{vC, uC, u} c N).map i y) =
    (changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N)).val.map i
      (rawPairing c M N W x y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s m =>
    change B.obj.obj W at s
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t n =>
      change B.obj.obj W at t
      rw [tensorRestriction_tmul, tensorRestriction_tmul, rawPairing_tmul c,
        rawPairing_tmul c]
      have h := PresheafOfModules.naturality_apply
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
          (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N)))
        i ((s * t) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] pure A M N W m n)
      have hm := tensorRestriction_tmul c ((monoidalCategory A).tensorObj M N) i
        (s * t) (pure A M N W m n)
      rw [map_mul, pure_restrict] at hm
      exact (congrArg
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
          (changeOfRingsPresheaf.{vC, uC, u} c ((monoidalCategory A).tensorObj M N))).app V)
        hm).symm.trans h

/-- Existence part of the sheaf tensor universal property.
(auxiliary; not a blueprint node)
The sectionwise tensor maps are assembled into a presheaf morphism and uniquely factored
through module sheafification; this is exactly the existence construction in the source proof. -/
private theorem tensor_bilinear_exists {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃ φ : (monoidalCategory R).tensorObj F G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  let := monoidalCategory R
  let q : F.val ⊗ G.val ⟶ H.val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (F.val ⊗ G.val).obj U)
        (Y := H.val.obj U) (TensorProduct.lift (β U))
      naturality := by
        intro U V f
        ext t
        change TensorProduct.lift (β V) ((F.val ⊗ G.val).map f t) =
          H.val.map f (TensorProduct.lift (β U) t)
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)
          exact hβ f x y
        | add t s ht hs => simp only [map_add, ht, hs] }
  let adj := PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  let a := (adj.homEquiv (F.val ⊗ G.val) H).symm q
  refine ⟨(tensorObjIsoSheafification.{vC, uC, u} F G).hom ≫ a, ?_⟩
  intro U x y
  have h := (adj.homEquiv (F.val ⊗ G.val) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ (t.app U) (x ⊗ₜ[R.obj.obj U] y)) h
  change a.val.app U (((adj.unit.app (F.val ⊗ G.val)).app U)
    (x ⊗ₜ[R.obj.obj U] y)) = β U x y at hh
  change a.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))) = _
  have hi := congrArg (fun t : (PresheafOfModules.sheafification.{u, vC, u, uC}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).obj
        (F.val ⊗ G.val) ⟶ _ ↦ t.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))
    (tensorObjIsoSheafification.{vC, uC, u} F G).inv_hom_id
  change (tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y))) = _ at hi
  rw [hi]
  exact hh

private noncomputable def forwardPairing
    (M N : SheafOfModules.{u} (ringSheaf A)) (W : Cᵒᵖ) :
    M.val.obj W →ₗ[A.obj.obj W] N.val.obj W →ₗ[A.obj.obj W]
      ((restriction c).obj ((monoidalCategory B).tensorObj
        (changeOfRings.{vC, uC, u} c M) (changeOfRings.{vC, uC, u} c N))).val.obj W :=
  LinearMap.mk₂ (A.obj.obj W)
    (fun m n ↦ pure B _ _ W (show (changeOfRings c M).val.obj W from
            ((tensorAdjunction c).unit.app M).val.app W m)
      (show (changeOfRings c N).val.obj W from
            ((tensorAdjunction c).unit.app N).val.app W n))
    (by
      intro m m' n
      rw [map_add]
      exact (pureBilin B _ _ W).map_add₂ _ _ _)
    (by
      intro r m n
      rw [map_smul]
      change pure B (changeOfRings c M) (changeOfRings c N) W
        ((c.hom.app W r) • (show (changeOfRings c M).val.obj W from
            ((tensorAdjunction c).unit.app M).val.app W m))
        (show (changeOfRings c N).val.obj W from
            ((tensorAdjunction c).unit.app N).val.app W n) =
        (c.hom.app W r) • pure B (changeOfRings c M) (changeOfRings c N) W
          (show (changeOfRings c M).val.obj W from
            ((tensorAdjunction c).unit.app M).val.app W m)
          (show (changeOfRings c N).val.obj W from
            ((tensorAdjunction c).unit.app N).val.app W n)
      exact (pureBilin B _ _ W).map_smul₂ _ _ _)
    (by
      intro m n n'
      rw [map_add]
      exact ((pureBilin B _ _ W) _).map_add _ _)
    (by
      intro r m n
      rw [map_smul]
      change pure B (changeOfRings c M) (changeOfRings c N) W
        (show (changeOfRings c M).val.obj W from
            ((tensorAdjunction c).unit.app M).val.app W m)
        ((c.hom.app W r) • (show (changeOfRings c N).val.obj W from
            ((tensorAdjunction c).unit.app N).val.app W n)) =
        (c.hom.app W r) • pure B (changeOfRings c M) (changeOfRings c N) W
          (show (changeOfRings c M).val.obj W from
            ((tensorAdjunction c).unit.app M).val.app W m)
          (show (changeOfRings c N).val.obj W from
            ((tensorAdjunction c).unit.app N).val.app W n)
      exact ((pureBilin B _ _ W) _).map_smul _ _)

private theorem forwardPairing_restrict
    (M N : SheafOfModules.{u} (ringSheaf A)) {W V : Cᵒᵖ} (i : W ⟶ V)
    (m : M.val.obj W) (n : N.val.obj W) :
    forwardPairing c M N V (M.val.map i m) (N.val.map i n) =
      ((monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
        (changeOfRings.{vC, uC, u} c N)).val.map i
        (forwardPairing c M N W m n) := by
  change pure B _ _ V (((tensorAdjunction c).unit.app M).val.app V (M.val.map i m))
      (((tensorAdjunction c).unit.app N).val.app V (N.val.map i n)) =
    ((monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
      (changeOfRings.{vC, uC, u} c N)).val.map i
      (pure B _ _ W _ _)
  have hm := PresheafOfModules.naturality_apply ((tensorAdjunction c).unit.app M).val i m
  have hn := PresheafOfModules.naturality_apply ((tensorAdjunction c).unit.app N).val i n
  exact (congrArg₂ (pure B _ _ V) hm hn).trans (pure_restrict B _ _ i _ _).symm

private theorem exists_forward
    (M N : SheafOfModules.{u} (ringSheaf A)) :
    ∃ f : changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N) ⟶
        (monoidalCategory B).tensorObj
          (changeOfRings.{vC, uC, u} c M) (changeOfRings.{vC, uC, u} c N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), f.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
  let H := (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
    (changeOfRings.{vC, uC, u} c N)
  obtain ⟨a, ha⟩ := tensor_bilinear_exists A M N ((restriction c).obj H)
    (forwardPairing c M N) (forwardPairing_restrict c M N)
  let f := ((tensorAdjunction c).homEquiv _ H).symm a
  refine ⟨f, ?_⟩
  intro W m n
  have hf := ((tensorAdjunction c).homEquiv _ H).apply_symm_apply a
  have he := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H f
  change (underlying A).map ((tensorAdjunction c).homEquiv _ H f) =
    tensorUnit c _ ≫ (underlying B).map f at he
  rw [hf] at he
  exact (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) he).symm.trans (ha W m n)

-- Comparing both module-sheafification adjunctions involves nested tensor maps.
private theorem presheafTensorDescent
    (E F : PresheafOfModules.{u} (ringSheaf B).obj)
    (H : SheafOfModules.{u} (ringSheaf B)) (β : E ⊗ F ⟶ H.val) :
    ∃ g : (monoidalCategory B).tensorObj
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)).obj E)
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)).obj F) ⟶ H,
      ∀ W (x : E.obj W) (y : F.obj W),
        g.val.app W (pure B _ _ W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf B).obj)).unit.app E).app W x)
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf B).obj)).unit.app F).app W y)) =
        β.app W (x ⊗ₜ[B.obj.obj W] y) := by
  let := monoidalCategory B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)
  let S := PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  have hη (G : PresheafOfModules.{u} (ringSheaf B).obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj))
        (adj.unit.app G) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)]
    change IsIso (S.map (adj.unit.app G))
    have hc : IsIso (adj.counit.app (S.obj G)) := inferInstance
    have hh : IsIso (S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G)) := by
      have ht := adj.left_triangle_components G
      change S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G) = 𝟙 _ at ht
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (S.obj G))
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫ (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := inferInstance
  let a := (adj.homEquiv (E ⊗ F) H).symm β
  let g := inv q ≫ a
  have hqa : q ≫ g = a := by
    dsimp only [g]
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  refine ⟨g, ?_⟩
  intro W x y
  have hn := adj.unit.naturality (ηE ⊗ₘ ηF)
  have he := congrArg (fun k ↦ (k.app W) (x ⊗ₜ[B.obj.obj W] y)) hn
  change (adj.unit.app ((S.obj E).val ⊗ (S.obj F).val)).app W
      (ηE.app W x ⊗ₜ[B.obj.obj W] ηF.app W y) =
    (S.map (ηE ⊗ₘ ηF)).val.app W
      ((adj.unit.app (E ⊗ F)).app W (x ⊗ₜ[B.obj.obj W] y)) at he
  have hp : pure B (S.obj E) (S.obj F) W (ηE.app W x) (ηF.app W y) =
      q.val.app W ((adj.unit.app (E ⊗ F)).app W (x ⊗ₜ[B.obj.obj W] y)) :=
    congrArg ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W) he
  have ha := (adj.homEquiv (E ⊗ F) H).apply_symm_apply β
  rw [Adjunction.homEquiv_unit] at ha
  change g.val.app W (pure B (S.obj E) (S.obj F) W (ηE.app W x) (ηF.app W y)) = _
  rw [hp]
  exact (congrArg (fun k ↦ k.val.app W
    ((adj.unit.app (E ⊗ F)).app W (x ⊗ₜ[B.obj.obj W] y))) hqa).trans
      (congrArg (fun k ↦ (k.app W) (x ⊗ₜ[B.obj.obj W] y)) ha)

private theorem exists_backward
    (M N : SheafOfModules.{u} (ringSheaf A)) :
    ∃ f : (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
        (changeOfRings.{vC, uC, u} c N) ⟶
        changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), f.val.app W
        (pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n)) =
      (tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W (pure A M N W m n) := by
  let E := changeOfRingsPresheaf.{vC, uC, u} c M
  let F := changeOfRingsPresheaf.{vC, uC, u} c N
  let H := changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N)
  let β : E ⊗ F ⟶ H.val :=
    { app := fun W ↦ ModuleCat.ofHom (X := (E ⊗ F).obj W)
        (Y := H.val.obj W) (TensorProduct.lift (rawPairing c M N W))
      naturality := by
        intro W V i
        ext x
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y => exact rawPairing_restrict c M N i x y }
  obtain ⟨f, hf⟩ := presheafTensorDescent (B := B) E F H β
  refine ⟨f, ?_⟩
  intro W m n
  erw [tensorUnit_apply, tensorUnit_apply]
  refine (hf W _ _).trans ?_
  change rawPairing c M N W
    ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
    ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = _
  refine (rawPairing_tmul c M N W 1 1 m n).trans ?_
  rw [one_mul]
  exact (tensorUnit_apply c _ W (pure A M N W m n)).symm

private noncomputable def ins (M : SheafOfModules.{u} (ringSheaf A))
    (W : Cᵒᵖ) (m : M.val.obj W) : (changeOfRings.{vC, uC, u} c M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)).unit.app
    (changeOfRingsPresheaf.{vC, uC, u} c M)).app W
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))
-- Expand the two scalar extensions through the sheafification adjunction.
private theorem scalar_tensor_ext
    (M N : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf B))
    {f g : (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
      (changeOfRings.{vC, uC, u} c N) ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W (pure B _ _ W (ins c M W m) (ins c N W n)) =
      g.val.app W (pure B _ _ W (ins c M W m) (ins c N W n))) : f = g := by
  let := monoidalCategory B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)
  let S := PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj)
  let E := changeOfRingsPresheaf.{vC, uC, u} c M
  let F := changeOfRingsPresheaf.{vC, uC, u} c N
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  have hη (G : PresheafOfModules.{u} (ringSheaf B).obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj)) (adj.unit.app G) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)]
    change IsIso (S.map (adj.unit.app G))
    have hc : IsIso (adj.counit.app (S.obj G)) := inferInstance
    have hh : IsIso (S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G)) := by
      have ht := adj.left_triangle_components G
      change S.map (adj.unit.app G) ≫ adj.counit.app (S.obj G) = 𝟙 _ at ht
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (S.obj G))
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf B).obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (ringSheaf B).obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫ (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := inferInstance
  apply (cancel_epi q).mp
  apply (adj.homEquiv (E ⊗ F) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing ((ringSheaf B).obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : (E.obj W) ⊗[(ringSheaf B).obj.obj W] (F.obj W) →ₗ[(ringSheaf B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (ringSheaf B) ⋙ PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          (q ≫ f)).app W).hom
  let b : (E.obj W) ⊗[(ringSheaf B).obj.obj W] (F.obj W) →ₗ[(ringSheaf B).obj.obj W]
      H.val.obj W := ((adj.unit.app (E ⊗ F) ≫
        (forget (ringSheaf B) ⋙ PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          (q ≫ g)).app W).hom
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of ((ringSheaf B).obj.obj W)
        ((F.obj W) →ₗ[(ringSheaf B).obj.obj W] H.val.obj W))
        (TensorProduct.curry a) = ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of ((ringSheaf B).obj.obj W)
        ((F.obj W) →ₗ[(ringSheaf B).obj.obj W] H.val.obj W))
          (TensorProduct.curry b) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry a _ = TensorProduct.curry b _
    have hm : ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
        (TensorProduct.curry a ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W) (Y := H.val.obj W)
          (TensorProduct.curry b ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      have hn := adj.unit.naturality (ηE ⊗ₘ ηF)
      have he := congrArg (fun k ↦ (k.app W)
        (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) hn
      change (adj.unit.app ((S.obj E).val ⊗ (S.obj F).val)).app W
          (ηE.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
            ⊗ₜ[B.obj.obj W]
            ηF.app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
        (S.map (ηE ⊗ₘ ηF)).val.app W
          ((adj.unit.app (E ⊗ F)).app W
            (((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m) ⊗ₜ[B.obj.obj W]
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n))) at he
      change f.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _))) =
        g.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W ((adj.unit.app (E ⊗ F)).app W _)))
      exact (congrArg (fun v ↦ f.val.app W
        ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he.symm).trans
          ((h W m n).trans (congrArg (fun v ↦ g.val.app W
            ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W v)) he))
    exact congrArg ModuleCat.Hom.hom hm
  exact ModuleCat.hom_ext (TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh))

private theorem extendedTensor_hom_ext
    (M N : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf B))
    {f g : changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N) ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
        (pure A M N W m n)) =
      g.val.app W ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
        (pure A M N W m n))) : f = g := by
  apply ((tensorAdjunction c).homEquiv _ H).injective
  apply pure_hom_ext A M N ((restriction c).obj H)
  intro W m n
  have hf := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H f
  have hg := tensorAdjunction_underlying c ((monoidalCategory A).tensorObj M N) H g
  exact (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) hf).trans
    ((h W m n).trans (congrArg (fun k ↦ k.hom.app W (pure A M N W m n)) hg).symm)

/-- Scalar extension preserves the sheaf tensor product and its normalized pairing.
Source: Stacks Project, Modules on Sites, Tag 03EL, first and last equalities;
Tag 0GMW for descent through module sheafification.
(auxiliary; not a blueprint node).

Proof: Extend the bilinear pairing of the two scalar-extension units to obtain the
forward map. For the inverse use the sectionwise formula
(s tensor m) tensor (t tensor n) mapped to st tensor (m tensor n), and extend this
bilinear map through both sheafifications. The tensor universal property supplies
the inverse map. Both composites are identities on the generating original pure
tensors; uniqueness of bilinear extension and of sheafification proves the identities.
The same generators establish simultaneous naturality. The formula holds by construction.
No flatness or nonzero-ring hypothesis is used. -/
private theorem exists_scalarTensorComparison :
    ∃ e : ∀ M N : SheafOfModules.{u} (ringSheaf A),
        changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N) ≅
          (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
            (changeOfRings.{vC, uC, u} c N),
      (∀ {M M' N N' : SheafOfModules.{u} (ringSheaf A)} (f : M ⟶ M') (g : N ⟶ N'),
        (tensorFunctor c).map ((monoidalCategory A).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory B).tensorHom
            ((tensorFunctor c).map f) ((tensorFunctor c).map g)) ∧
      ∀ M N W m n, (e M N).hom.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
  classical
  have hs M N : ∃ e : changeOfRings.{vC, uC, u} c ((monoidalCategory A).tensorObj M N) ≅
      (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} c M)
        (changeOfRings.{vC, uC, u} c N),
      ∀ (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W), e.hom.val.app W
        ((tensorUnit c ((monoidalCategory A).tensorObj M N)).hom.app W
          (pure A M N W m n)) =
        pure B _ _ W ((tensorUnit c M).hom.app W m) ((tensorUnit c N).hom.app W n) := by
    obtain ⟨f, hf⟩ := exists_forward c M N
    obtain ⟨g, hg⟩ := exists_backward c M N
    refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
    · apply extendedTensor_hom_ext c M N
      intro W m n
      change g.val.app W (f.val.app W _) = _
      exact (congrArg (g.val.app W) (hf W m n)).trans (hg W m n)
    · apply scalar_tensor_ext c M N
      intro W m n
      change f.val.app W (g.val.app W _) = _
      have hm := tensorUnit_apply c M W m
      have hn := tensorUnit_apply c N W n
      change (tensorUnit c M).hom.app W m = ins c M W m at hm
      change (tensorUnit c N).hom.app W n = ins c N W n at hn
      rw [← hm, ← hn]
      exact (congrArg (f.val.app W) (hg W m n)).trans (hf W m n)
  choose e he using hs
  refine ⟨e, ?_, he⟩
  intro M M' N N' f g
  apply extendedTensor_hom_ext c M N
  intro W m n
  have hu (P Q : SheafOfModules.{u} (ringSheaf A)) (a : P ⟶ Q) (x : P.val.obj W) :
      ((tensorFunctor c).map a).val.app W ((tensorUnit c P).hom.app W x) =
        (tensorUnit c Q).hom.app W (a.val.app W x) := by
    exact (congrArg (fun k ↦ k.val.app W x) ((tensorAdjunction c).unit.naturality a)).symm
  change (e M' N').hom.val.app W
      (((tensorFunctor c).map ((monoidalCategory A).tensorHom f g)).val.app W _) =
    ((monoidalCategory B).tensorHom ((tensorFunctor c).map f)
      ((tensorFunctor c).map g)).val.app W ((e M N).hom.val.app W _)
  rw [hu, pure_map, he, he, pure_map, hu, hu]

end SheafOfModules.CochainScalarConstruction

namespace SheafOfModules.CochainTensorComparison
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

/-- Scalar-extension insertion on every section, followed by the presentation cast.
Source: Stacks Project, Modules on Sites, Tag 03CY.
(auxiliary; not a blueprint node). -/
noncomputable def scalarInsertion : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂
  CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M)) := by
  intro M
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
      (changeOfRingsPresheaf c (I.modules.obj M))
  let q : ((toSheaf ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj RI) ⋙
      sheafCompose JD (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj S) ⋙
        sheafCompose JD (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (changeOfRings c (I.modules.obj M))) :=
    ⟨{ app := fun W ↦ ↾fun m ↦ η.app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m)
       naturality := by
         intro W V a
         ext m
         have hn := PresheafOfModules.naturality_apply η a
           ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m)
         have hr := Classical.choose_spec (exists_changeOfRingsMap c (I.modules.obj M) a)
           (1 : S.obj.obj W) m
         rw [map_one] at hr
         change η.app V
           ((1 : S.obj.obj V) ⊗ₜ[RI.obj.obj V, (c.hom.app V).hom]
             ((I.modules.obj M).val.map a m)) =
           (changeOfRings c (I.modules.obj M)).val.map a
             (η.app W ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
         erw [← hr]
         exact hn }⟩
  exact q ≫ (toSheaf ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj S) ⋙
    sheafCompose JD (CategoryTheory.forget AddCommGrpCat.{u})).map (eqToHom (hobj M).symm)

/-- A natural tensor isomorphism exists for the constructed scalar insertion.
Source: Stacks Project, Modules on Sites, Tag 03EL, its three tensor identities.
(auxiliary; not a blueprint node).

Proof: form the RI-module direct image on uPush of underlying sheaves. Its
addition and scalar action are induced by the product comparison of uPush and
the adjoint of I.ringUnderlying. Transpose maps along adj. The equations
I.moduleAdd and I.moduleSMul, tested on the universal pairs and triples of
operands, show that transposition restricts to mutually inverse bijections
of linear maps and of balanced bilinear maps. Apply the sheaf-tensor universal
property on the two sides of this bijection. Yoneda gives an isomorphism from
I(M tensor N) to I(M) tensor I(N); evaluation on pure pairings gives its
formula for every test sheaf Z. Naturality of transposition gives simultaneous
naturality in M and N. This argument uses products and Hom bijections only,
so it does not identify either site's object or morphism universe with u.

For scalar extension, the sectionwise maps s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n), and (s tensor m) tensor (t tensor n)
to st tensor (m tensor n), are balanced and compatible with restrictions.
Extend them by the sheafification universal property. Tensor induction shows
that their composites are identities. Composing this scalar isomorphism with
the preceding inverse-image isomorphism gives the tensorator. Conjugate by
hobj; hmap and the two naturality equations give its naturality for L.
Evaluating both comparisons at inverse images of generalized pure tensors
gives exactly the displayed equation with the constructed scalarInsertion.
This result asserts neither existence of the insertion nor uniqueness of the
comparison, which are proved separately by the importing module. -/
theorem normalizedTensorator_exists
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm) :
    ∃ mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N),
      (∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)) ∧
      ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        scalarInsertion R S RI uInv I c L hobj ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ scalarInsertion R S RI uInv I c L hobj
              M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ scalarInsertion R S RI uInv I c L hobj
                N).hom.app W t)) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory RI
  let := monoidalCategory S
  obtain ⟨eI, hnI, hpI⟩ := CochainInversePairing.exists_inverseImageTensorComparison R RI uInv I
    uPush adj
  obtain ⟨eS, hnS, hpS⟩ := CochainScalarConstruction.exists_scalarTensorComparison c
  let T := CochainScalarConstruction.tensorFunctor c
  let ε : L ≅ I.modules ⋙ T := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  let ei : tensor _ ⋙ I.modules ≅ I.modules.prod I.modules ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ eI MN.1 MN.2) (fun f ↦ hnI f.1 f.2)
  let es : tensor _ ⋙ T ≅ T.prod T ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ eS MN.1 MN.2) (fun f ↦ hnS f.1 f.2)
  let μ : tensor _ ⋙ L ≅ L.prod L ⋙ tensor _ :=
    Functor.isoWhiskerLeft (tensor _) ε ≪≫
      Functor.isoWhiskerRight ei T ≪≫
      Functor.isoWhiskerLeft (I.modules.prod I.modules) es ≪≫
      (Functor.isoWhiskerRight (NatIso.prod ε ε) (tensor _)).symm
  refine ⟨fun M N ↦ μ.app (M, N), ?_, ?_⟩
  · intro M M' N N' f g
    exact μ.hom.naturality (show (M, N) ⟶ (M', N') from (f, g))
  · intro M N Z x y z hz W t
    let a := ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
    let b := ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)
    let d := ((uInv.map z ≫ I.moduleUnderlying.inv.app (M ⊗ N)).hom.app W t)
    have hi : (eI M N).hom.val.app W d = CochainScalarConstruction.pure RI _ _ W a b :=
      hpI M N Z x y z hz W t
    have hu : (T.map (eI M N).hom).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d) =
        (CochainScalarConstruction.tensorUnit c (I.modules.obj M ⊗ I.modules.obj N)).hom.app W
          ((eI M N).hom.val.app W d) :=
      (congrArg (fun f ↦ f.val.app W d)
        ((CochainScalarConstruction.tensorAdjunction c).unit.naturality (eI M N).hom)).symm
    have he (P : SheafOfModules.{u} (CochainScalarConstruction.ringSheaf R))
        (v : (T.obj (I.modules.obj P)).val.obj W) :
        (ε.hom.app P).val.app W ((ε.inv.app P).val.app W v) = v := by
      exact congrArg (fun f : T.obj (I.modules.obj P) ⟶ T.obj (I.modules.obj P) ↦
        f.val.app W v) (ε.inv_hom_id_app P)
    change (((T.map (eI M N).hom ≫ (eS (I.modules.obj M) (I.modules.obj N)).hom) ≫
      (ε.inv.app M ⊗ₘ ε.inv.app N)).val.app W)
      ((ε.hom.app (M ⊗ N)).val.app W
        ((ε.inv.app (M ⊗ N)).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d))) =
      CochainScalarConstruction.pure S _ _ W
        ((ε.inv.app M).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W a))
        ((ε.inv.app N).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj N)).hom.app W b))
    rw [he]
    change (ε.inv.app M ⊗ₘ ε.inv.app N).val.app W
      ((eS (I.modules.obj M) (I.modules.obj N)).hom.val.app W
        ((T.map (eI M N).hom).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj (M ⊗ N))).hom.app W d))) = _
    rw [hu, hi]
    exact (congrArg ((ε.inv.app M ⊗ₘ ε.inv.app N).val.app W)
      (hpS (I.modules.obj M) (I.modules.obj N) W a b)).trans
        (CochainScalarConstruction.pure_map S (ε.inv.app M) (ε.inv.app N) W _ _)

end SheafOfModules.CochainTensorComparison
