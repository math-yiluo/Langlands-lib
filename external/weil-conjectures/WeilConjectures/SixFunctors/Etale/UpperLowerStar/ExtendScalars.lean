/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Extension of scalars from abelian groups for étale sheaves

For a commutative ring `Λ`, extension of scalars `A ↦ Λ ⊗_ℤ A`
(`ModuleCat.extendScalarsAddCommGrp`) is left adjoint to the forgetful functor from `Λ`-modules
to abelian groups. Applied to étale sheaves, followed by sheafification, it gives the functor
`F ↦ Λ ⊗_ℤ F` from étale sheaves of abelian groups to étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.extendScalars`), left adjoint to the forgetful functor. Both
commute with pullback (`AlgebraicGeometry.Etale.upperStarExtendScalarsIso`) and send constant
sheaves to constant sheaves (`AlgebraicGeometry.Etale.constantSheafCompExtendScalarsIso`), as
the corresponding statements for the right adjoints are clear. If `n` kills `Λ`, extension of
scalars sends `ℤ/n` to `Λ` (`ModuleCat.extendScalarsAddCommGrpZModIso`).

## Main definitions

- `ModuleCat.extendScalarsAddCommGrp`: the functor `A ↦ Λ ⊗_ℤ A`.
- `AlgebraicGeometry.Etale.extendScalars`: its sheafified version on étale sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Extension of scalars from abelian groups to `Λ`-modules, `A ↦ Λ ⊗_ℤ A`. -/
noncomputable def extendScalarsAddCommGrp : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} Λ :=
  (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.extendScalars.{0, u + 1, u + 1} (Int.castRingHom Λ)

/-- Extension of scalars from abelian groups is left adjoint to the forgetful functor. -/
noncomputable def extendScalarsAddCommGrpAdj :
    extendScalarsAddCommGrp Λ ⊣ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.symm.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} (Int.castRingHom Λ))).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

instance : (extendScalarsAddCommGrp Λ).IsLeftAdjoint :=
  (extendScalarsAddCommGrpAdj Λ).isLeftAdjoint

/-- Homomorphisms out of `ℤ/n` into an abelian group killed by `n` are its elements, through
evaluation at `1`. -/
noncomputable def _root_.AddCommGrpCat.zmodHomEquiv {n : ℕ} (A : AddCommGrpCat.{u + 1})
    (hA : ∀ a : A, n • a = 0) :
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) ⟶ A) ≃ A where
  toFun f := f.hom (ULift.up 1)
  invFun a := AddCommGrpCat.ofHom ((ZMod.lift n ⟨zmultiplesHom _ a, by simp [hA]⟩).comp
    AddEquiv.ulift.toAddMonoidHom)
  left_inv f := by
    ext ⟨b⟩
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective b
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply]
    change ZMod.lift n _ (k : ZMod n) = _
    rw [ZMod.lift_coe]
    simp only [zmultiplesHom_apply]
    rw [← map_zsmul]
    congr 1
    apply ULift.ext
    simp
  right_inv a := by
    have h1 : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := Int.cast_one.symm
    dsimp only
    simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply]
    erw [h1, ZMod.lift_coe]
    simp

variable {Λ} in
/-- If `n` kills `Λ`, extension of scalars sends `ℤ/n` to `Λ`: both corepresent the functor
`M ↦ M` on `Λ`-modules, every `Λ`-module being killed by `n`. -/
noncomputable def extendScalarsAddCommGrpZModIso {n : ℕ} (hn : (n : Λ) = 0) :
    (extendScalarsAddCommGrp Λ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≅
      ModuleCat.of Λ Λ := by
  have hM (M : ModuleCat.{u + 1} Λ) :
      ∀ a : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M, n • a = 0 := by
    intro a
    exact (show n • (show M from a) = 0 by rw [← Nat.cast_smul_eq_nsmul Λ, hn, zero_smul])
  let e (M : ModuleCat.{u + 1} Λ) :
      ((extendScalarsAddCommGrp Λ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ M) ≃
        (ModuleCat.of Λ Λ ⟶ M) :=
    ((extendScalarsAddCommGrpAdj Λ).homEquiv _ _).trans
      ((AddCommGrpCat.zmodHomEquiv _ (hM M)).trans
        { toFun m := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M m)
          invFun f := f.hom 1
          left_inv m := by simp
          right_inv f := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext_ring
            simp })
  refine (Coyoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun M ↦ (e M).toIso) ?_)).unop.symm
  intro M M' g
  ext f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map, yoneda_map_app,
    TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    Equiv.toIso_hom_hom_apply, hom_comp, LinearMap.coe_comp, Function.comp_apply, e,
    AddCommGrpCat.zmodHomEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

end ModuleCat

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) {Y : Scheme.{u}}

/-- Extension of scalars `F ↦ Λ ⊗_ℤ F` from étale sheaves of abelian groups to étale sheaves of
`Λ`-modules: extension of scalars on sections followed by sheafification. -/
noncomputable def extendScalars :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalarsAddCommGrp Λ)

/-- Extension of scalars on étale sheaves is left adjoint to the forgetful functor. -/
noncomputable def extendScalarsAdjunction :
    extendScalars Λ X ⊣
      sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Sheaf.adjunction _ (ModuleCat.extendScalarsAddCommGrpAdj Λ)

instance : (extendScalars Λ X).IsLeftAdjoint :=
  (extendScalarsAdjunction Λ X).isLeftAdjoint

instance : (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add {_ _ _ _} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

instance : (extendScalars Λ X).Additive :=
  (extendScalarsAdjunction Λ X).left_adjoint_additive

variable {X}

/-- Extension of scalars commutes with pullback, `f^*(Λ ⊗ F) ≅ Λ ⊗ f^* F`: both functors are left
adjoint to `G ↦ f_* G` viewed as a sheaf of abelian groups. -/
noncomputable def upperStarExtendScalarsIso (f : X ⟶ Y) :
    extendScalars Λ Y ⋙ (f)^*[ModuleCat.{u + 1} Λ] ≅
      (f)^*[AddCommGrpCat.{u + 1}] ⋙ extendScalars Λ X :=
  ((extendScalarsAdjunction Λ Y).comp (upperStarLowerStarAdjunction _ f)).leftAdjointUniq
    (((upperStarLowerStarAdjunction _ f).comp (extendScalarsAdjunction Λ X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

variable (X)

/-- Extension of scalars sends constant sheaves to constant sheaves: both functors are left
adjoint to taking global sections viewed as an abelian group. -/
noncomputable def constantSheafCompExtendScalarsIso :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ extendScalars Λ X ≅
      ModuleCat.extendScalarsAddCommGrp Λ ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).comp
    (extendScalarsAdjunction Λ X)).leftAdjointUniq
    (((ModuleCat.extendScalarsAddCommGrpAdj Λ).comp
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

variable {Λ} in
/-- If `n` kills `Λ`, extension of scalars sends the constant sheaf `ℤ/n` to the constant sheaf
`Λ`, the unit of the étale sheaves of `Λ`-modules. -/
noncomputable def extendScalarsConstantZModIso {n : ℕ} (hn : (n : Λ) = 0) :
    (extendScalars Λ X).obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) :=
  (constantSheafCompExtendScalarsIso Λ X).app _ ≪≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (ModuleCat.extendScalarsAddCommGrpZModIso hn)

end AlgebraicGeometry.Etale
