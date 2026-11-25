/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Module.Shrink

/-! # The explicit presheaf of compatible local module sections

Source: Stacks Project, Sheaves, Tags 00AL (first proof) and 00AM.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf)
-/

@[expose] public section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Local sections on every subopen of a cover member inside `V`.
Source: Stacks, Tag 00AL, first proof, with intersection sections expanded by restriction.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
abbrev OpenModuleFamily (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (V : Opens X) :=
  ∀ (i : I) (W : Opens X) (hi : W ≤ U i) (_ : W ≤ V),
    (Fi i).val.obj (op (Over.mk (homOfLE hi)))

/-- A local family respects restrictions and the given overlap maps.
Source: Stacks, Tags 00AL and 00AM, compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
def OpenModuleFamilyCoherent (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (V : Opens X) (a : OpenModuleFamily X I U Fi V) : Prop :=
  (∀ (i : I) (W Z : Opens X) (hi : W ≤ U i) (hWV : W ≤ V) (hZW : Z ≤ W),
    (Fi i).val.map (Over.homMk (homOfLE hZW)).op (a i W hi hWV) =
      a i Z (hZW.trans hi) (hZW.trans hWV)) ∧
  (∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V),
    (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) (a i W hi hWV) =
      a j W hj hWV)

/-- Evaluate a global section through a local projection after restricting it.
Source: Stacks, Tag 00AL, projection of the compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
noncomputable abbrev openModuleFamilyEval
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (H : SheafOfModules.{max u v} (moduleRings X))
    (π : ∀ i : I, H.over (U i) ⟶ Fi i) (V : Opens X)
    (s : H.val.obj (op V)) : OpenModuleFamily X I U Fi V :=
  fun i _W hi hWV => (π i).val.app (op (Over.mk (homOfLE hi)))
    (H.val.map (homOfLE hWV).op s)

section Construction

variable (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
  (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
  (φij : ∀ i j : I,
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
    (SheafOfModules.overMap (moduleRings X)
      (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))

/-- A component viewed as a module over sections on V, by restriction of scalars. -/
noncomputable abbrev openModuleFamilyComponent (V : Opens X) (i : I) (W : Opens X)
    (hi : W ≤ U i) (hWV : W ≤ V) :=
  (ModuleCat.restrictScalars ((moduleRings X).obj.map (homOfLE hWV).op).hom).obj
    ((Fi i).val.obj (op (Over.mk (homOfLE hi))))

/-- Reindex proof-bound components by an ordinary type, to transport Pi instances. -/
def openModuleFamilyEquiv (V : Opens X) :
    OpenModuleFamily X I U Fi V ≃
      (∀ t : Σ i : I, {W : Opens X // W ≤ U i ∧ W ≤ V},
        openModuleFamilyComponent X I U Fi V t.1 t.2.1 t.2.2.1 t.2.2.2) where
  toFun a t := a t.1 t.2.1 t.2.2.1 t.2.2.2
  invFun a i W hi hWV := a ⟨i, W, hi, hWV⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance openModuleFamilyAddCommGroup (V : Opens X) :
    AddCommGroup (OpenModuleFamily X I U Fi V) :=
  (openModuleFamilyEquiv X I U Fi V).addCommGroup

noncomputable instance openModuleFamilyModule (V : Opens X) :
    Module ((moduleRings X).obj.obj (op V)) (OpenModuleFamily X I U Fi V) :=
  (openModuleFamilyEquiv X I U Fi V).addEquiv.module _

/-- The explicit submodule cut out by all restriction and overlap equations. -/
noncomputable def coherentOpenModuleSubmodule (V : Opens X) :
    Submodule ((moduleRings X).obj.obj (op V)) (OpenModuleFamily X I U Fi V) where
  carrier := {a | OpenModuleFamilyCoherent X I U Fi φij V a}
  zero_mem' := by
    constructor
    · intros; exact map_zero _
    · intros; exact map_zero _
  add_mem' := by
    intro a b ha hb
    constructor
    · intro i W Z hi hWV hZW
      change (Fi i).val.map _ (a i W hi hWV + b i W hi hWV) = _
      rw [map_add, ha.1, hb.1]
      rfl
    · intro i j W hi hj hWV
      change (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj))))
        (a i W hi hWV + b i W hi hWV) = _
      rw [map_add, ha.2, hb.2]
      rfl
  smul_mem' := by
    intro r a ha
    constructor
    · intro i W Z hi hWV hZW
      change (Fi i).val.map _
        ((moduleRings X).obj.map (homOfLE hWV).op r • a i W hi hWV) = _
      rw [PresheafOfModules.map_smul, ha.1]
      change ((moduleRings X).obj.map (homOfLE hZW).op
        ((moduleRings X).obj.map (homOfLE hWV).op r)) • _ = _
      rw [← RingCat.comp_apply, ← Functor.map_comp]
      rfl
    · intro i j W hi hj hWV
      change (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj))))
        ((moduleRings X).obj.map (homOfLE hWV).op r • a i W hi hWV) = _
      rw [map_smul, ha.2]
      rfl

/-- Restrict a coherent family by forgetting components outside the smaller open. -/
def coherentOpenModuleRestrict {V W : Opens X} (h : W ≤ V)
    (a : coherentOpenModuleSubmodule X I U Fi φij V) :
    coherentOpenModuleSubmodule X I U Fi φij W :=
  ⟨fun i Z hi hZW => a.1 i Z hi (hZW.trans h),
    ⟨fun i Z T hi hZW hTZ => a.2.1 i Z T hi (hZW.trans h) hTZ,
      fun i j Z hi hj hZW => a.2.2 i j Z hi hj (hZW.trans h)⟩⟩

/-- The compatible-family presheaf, before shrinking its section types. 
(blueprint: def-weil-pbc-module-compatible-family-presheaf)
-/
noncomputable def coherentOpenModulePresheaf :
    PresheafOfModules.{max u v w} (moduleRings X).obj where
  obj V := ModuleCat.of _ (coherentOpenModuleSubmodule X I U Fi φij V.unop)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((moduleRings X).obj.map f).hom).obj
      (ModuleCat.of _ (coherentOpenModuleSubmodule X I U Fi φij W.unop)))
    { toFun := coherentOpenModuleRestrict X I U Fi φij (leOfHom f.unop)
      map_add' := by intros; rfl
      map_smul' := by
        intro r a
        apply Subtype.ext
        funext i Z hi hZW
        change ((moduleRings X).obj.map (homOfLE (hZW.trans (leOfHom f.unop))).op r)
          • a.1 i Z hi _ =
          ((moduleRings X).obj.map (homOfLE hZW).op ((moduleRings X).obj.map f r))
          • a.1 i Z hi _
        rw [← RingCat.comp_apply, ← Functor.map_comp]
        rfl }
  map_id V := by ext a; rfl
  map_comp f g := by ext a; rfl

variable [∀ V : Opens X, Small.{max u v} (coherentOpenModuleSubmodule X I U Fi φij V)]

/-- The canonical linear equivalence from shrunk sections to coherent families. -/
noncomputable abbrev coherentOpenModuleShrinkEquiv (V : Opens X) :=
  Shrink.linearEquiv ((moduleRings X).obj.obj (op V))
    (coherentOpenModuleSubmodule X I U Fi φij V)

/-- Shrink the explicit compatible-family presheaf, transporting all restriction maps. -/
noncomputable def smallCoherentOpenModulePresheaf :
    PresheafOfModules.{max u v} (moduleRings X).obj where
  obj V := ModuleCat.of _ (Shrink.{max u v}
    (coherentOpenModuleSubmodule X I U Fi φij V.unop))
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((moduleRings X).obj.map f).hom).obj
      (ModuleCat.of _ (Shrink.{max u v}
        (coherentOpenModuleSubmodule X I U Fi φij W.unop))))
    { toFun := fun a => (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop).symm
        ((coherentOpenModulePresheaf X I U Fi φij).map f
          (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop a))
      map_add' := by intros; simp
      map_smul' := by
        intro r a
        change (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop).symm
          ((coherentOpenModulePresheaf X I U Fi φij).map f
            (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop (r • a))) = _
        rw [map_smul, PresheafOfModules.map_smul, map_smul]
        rfl }
  map_id V := by
    ext a
    change (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop).symm
      ((coherentOpenModulePresheaf X I U Fi φij).map (𝟙 V)
        (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop a)) = a
    simp
  map_comp {V W Z} f g := by
    ext a
    change (coherentOpenModuleShrinkEquiv X I U Fi φij Z.unop).symm
      ((coherentOpenModulePresheaf X I U Fi φij).map (f ≫ g)
        (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop a)) =
      (coherentOpenModuleShrinkEquiv X I U Fi φij Z.unop).symm
        ((coherentOpenModulePresheaf X I U Fi φij).map g
          (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop
            ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop).symm
              ((coherentOpenModulePresheaf X I U Fi φij).map f
                (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop a)))))
    rw [PresheafOfModules.map_comp_apply, LinearEquiv.apply_symm_apply]

/-- Shrinking commutes with restriction, as an equality of explicit families. -/
theorem smallCoherentOpenModulePresheaf_map_equiv {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (a : (smallCoherentOpenModulePresheaf X I U Fi φij).obj V) :
    coherentOpenModuleShrinkEquiv X I U Fi φij W.unop
      ((smallCoherentOpenModulePresheaf X I U Fi φij).map f a) =
      (coherentOpenModulePresheaf X I U Fi φij).map f
        (coherentOpenModuleShrinkEquiv X I U Fi φij V.unop a) := by
  change (coherentOpenModuleShrinkEquiv X I U Fi φij W.unop)
    ((coherentOpenModuleShrinkEquiv X I U Fi φij W.unop).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

end Construction

end AlgebraicGeometry
