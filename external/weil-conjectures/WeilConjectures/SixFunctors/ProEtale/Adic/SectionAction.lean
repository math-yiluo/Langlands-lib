/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# The action of `ℚ̄_ℓ,X` on the sections of an `ℓ`-adic sheaf

Let `F` be a sheaf of `ℚ̄_ℓ,X`-modules on `X_proét` (`AlgebraicGeometry.ProEtale.AdicSheaf`). Its
action `ℚ̄_ℓ,X ⊗ F ⟶ F` is a morphism out of the sheafified tensor product; restricted along the
comparison with the objectwise tensor product it gives, for every object `U`, a bilinear action
`a • x` of the locally finite functions `a ∈ ℚ̄_ℓ,X(U)` on the sections `x ∈ F(U)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionAct`). It is associative and unital, compatible
with restriction and with morphisms of `ℚ̄_ℓ,X`-modules.

A global section `s` of `F` defines the morphism `ℚ̄_ℓ,X ⟶ F`, `a ↦ a • s`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sectionHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- The action `a • x` of a locally finite function `a ∈ ℚ̄_ℓ,X(U)` on a section `x ∈ F(U)` of a
sheaf of `ℚ̄_ℓ,X`-modules: the action `ℚ̄_ℓ,X ⊗ F ⟶ F` restricted along the comparison with the
objectwise tensor product. -/
noncomputable def sectionAct (F : AdicSheaf l X) {U : X.ProEtᵒᵖ}
    (a : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) : F.X.obj.obj U :=
  (Mod.act F.X).hom.app U
    ((μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
      (adicConstantSheaf l X) F.X).app U (a ⊗ₜ x))

variable (F : AdicSheaf l X) {U : X.ProEtᵒᵖ}

lemma sectionAct_add (a : (adicConstantSheaf l X).obj.obj U) (x y : F.X.obj.obj U) :
    sectionAct F a (x + y) = sectionAct F a x + sectionAct F a y := by
  simp only [sectionAct, TensorProduct.tmul_add, map_add]

lemma add_sectionAct (a b : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    sectionAct F (a + b) x = sectionAct F a x + sectionAct F b x := by
  simp only [sectionAct, TensorProduct.add_tmul, map_add]

lemma sectionAct_zero (a : (adicConstantSheaf l X).obj.obj U) :
    sectionAct F a 0 = 0 := by
  simp only [sectionAct, TensorProduct.tmul_zero, map_zero]

lemma zero_sectionAct (x : F.X.obj.obj U) :
    sectionAct F 0 x = 0 := by
  simp only [sectionAct, TensorProduct.zero_tmul, map_zero]

lemma sectionAct_smul (c : ULift.{u + 1} (PadicAlgCl l))
    (a : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    sectionAct F a (c • x) = c • sectionAct F a x := by
  simp only [sectionAct, TensorProduct.tmul_smul, map_smul]

lemma smul_sectionAct (c : ULift.{u + 1} (PadicAlgCl l))
    (a : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    sectionAct F (c • a) x = c • sectionAct F a x := by
  rw [sectionAct, sectionAct, ← TensorProduct.smul_tmul', map_smul, map_smul]

/-- The action on sections is compatible with restriction. -/
lemma map_sectionAct {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    F.X.obj.map f (sectionAct F a x) =
      sectionAct F ((adicConstantSheaf l X).obj.map f a) (F.X.obj.map f x) := by
  have h1 := NatTrans.naturality_apply (Mod.act F.X).hom f
    ((μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
      (adicConstantSheaf l X) F.X).app U (a ⊗ₜ x))
  have h2 := NatTrans.naturality_apply
    (μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
      (adicConstantSheaf l X) F.X) f (a ⊗ₜ x)
  rw [sectionAct, ← h1]
  erw [← h2]
  rfl

/-- The action on sections is compatible with morphisms of `ℚ̄_ℓ,X`-modules. -/
lemma hom_sectionAct {F G : AdicSheaf l X} (φ : F ⟶ G)
    (a : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    φ.hom.hom.app U (sectionAct F a x) = sectionAct G a (φ.hom.hom.app U x) := by
  have h := congrArg (fun g ↦ (μ (sheafToPresheaf (Scheme.ProEt.topology X)
    (WeilCoefficients.{u} l)) (adicConstantSheaf l X) F.X ≫
      (sheafToPresheaf _ _).map g).app U (a ⊗ₜ x)) (Mod.act_hom φ)
  simp only [Functor.map_comp, ← μ_natural_right_assoc] at h
  exact h

end AlgebraicGeometry.ProEtale.AdicSheaf

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} (F : AdicSheaf l X) {U : X.ProEtᵒᵖ}

open scoped Obj

/-- The action on sections is associative: `(a * b) • x = a • (b • x)`. -/
lemma mul_sectionAct (a b : (adicConstantSheaf l X).obj.obj U) (x : F.X.obj.obj U) :
    sectionAct F (ULift.up (a.down * b.down)) x = sectionAct F a (sectionAct F b x) := by
  let := (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).modObjObj
    (A := adicConstantSheaf l X) F.X
  have h := congrArg (fun g ↦ g.app U ((a ⊗ₜ b) ⊗ₜ x))
    (Mod.mul_act (A := (sheafToPresheaf _ _).obj (adicConstantSheaf l X))
      ((sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj F.X))
  rw [Functor.obj.μ_def, adicConstantSheaf_μ_comp_map_mul'] at h
  exact h

/-- Constant functions act through the `ℚ̄_ℓ`-vector space structure of the sections. -/
lemma algebraMap_sectionAct (c : ULift.{u + 1} (PadicAlgCl l)) (x : F.X.obj.obj U) :
    sectionAct F (ULift.up (algebraMap _ _ c.down)) x = c • x := by
  let := (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).modObjObj
    (A := adicConstantSheaf l X) F.X
  have h := congrArg (fun g ↦ g.app U (c ⊗ₜ x))
    (Mod.one_act (A := (sheafToPresheaf _ _).obj (adicConstantSheaf l X))
      ((sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj F.X))
  rw [Functor.obj.η_def, adicConstantSheaf_ε_comp_map_one'] at h
  exact h

/-- The constant function `1` acts trivially. -/
lemma one_sectionAct (x : F.X.obj.obj U) :
    sectionAct F (ULift.up 1) x = x := by
  have h := algebraMap_sectionAct F (ULift.up 1) x
  rw [map_one] at h
  exact h.trans (one_smul _ x)

lemma toProEtTop_comp {U V : X.ProEt} (f : V ⟶ U) :
    f ≫ toProEtTop U = toProEtTop V := by
  refine MorphismProperty.Over.Hom.ext ?_
  exact MorphismProperty.Over.w f

/-- The restriction `s|_U` of a global section `s` of `F` to an object `U`. -/
noncomputable abbrev restrictTop (s : F.X.obj.obj (op (proEtTop X))) (U : X.ProEtᵒᵖ) :
    F.X.obj.obj U :=
  F.X.obj.map (toProEtTop U.unop).op s

lemma map_restrictTop (s : F.X.obj.obj (op (proEtTop X))) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    F.X.obj.map f (restrictTop F s U) = restrictTop F s V := by
  rw [restrictTop, restrictTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rw [← toProEtTop_comp f.unop]
  rfl

/-- The morphism of sheaves `ℚ̄_ℓ,X ⟶ F`, `a ↦ a • s`, attached to a global section `s`. -/
noncomputable def sectionSheafHom (s : F.X.obj.obj (op (proEtTop X))) :
    adicConstantSheaf l X ⟶ F.X :=
  ⟨{ app U := ModuleCat.ofHom
      { toFun a := sectionAct F a (restrictTop F s U)
        map_add' a b := add_sectionAct F a b _
        map_smul' c a := smul_sectionAct F c a _ }
     naturality U V f := by
       ext a
       change sectionAct F ((adicConstantSheaf l X).obj.map f a) (restrictTop F s V) =
         F.X.obj.map f (sectionAct F a (restrictTop F s U))
       rw [map_sectionAct, map_restrictTop] }⟩

lemma sectionSheafHom_app (s : F.X.obj.obj (op (proEtTop X))) (U : X.ProEtᵒᵖ)
    (a : (adicConstantSheaf l X).obj.obj U) :
    (sectionSheafHom F s).hom.app U a = sectionAct F a (restrictTop F s U) :=
  rfl

lemma sectionSheafHom_linear (s : F.X.obj.obj (op (proEtTop X))) :
    Mod.act (unit l X).X ≫ sectionSheafHom F s =
      adicConstantSheaf l X ◁ sectionSheafHom F s ≫ Mod.act F.X := by
  change (MonObj.mul : adicConstantSheaf l X ⊗ adicConstantSheaf l X ⟶ _) ≫ _ = _
  apply Sheaf.tensor_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc, ← Category.assoc,
    adicConstantSheaf_μ_comp_map_mul']
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  change sectionAct F _ _ = sectionAct F a (sectionAct F b _)
  rw [← mul_sectionAct]
  rfl

/-- The morphism of `ℚ̄_ℓ,X`-modules `ℚ̄_ℓ,X ⟶ F`, `a ↦ a • s`, attached to a global section
`s` of `F`. -/
noncomputable def sectionHom (s : F.X.obj.obj (op (proEtTop X))) : unit l X ⟶ F :=
  Mod.homMk (sectionSheafHom F s) (sectionSheafHom_linear F s)

lemma sectionHom_hom_app (s : F.X.obj.obj (op (proEtTop X))) (U : X.ProEtᵒᵖ)
    (a : (adicConstantSheaf l X).obj.obj U) :
    (sectionHom F s).hom.hom.app U a = sectionAct F a (restrictTop F s U) :=
  rfl

lemma sum_sectionAct {ι : Type*} (t : Finset ι) (a : ι → (adicConstantSheaf l X).obj.obj U)
    (x : F.X.obj.obj U) :
    sectionAct F (∑ i ∈ t, a i) x = ∑ i ∈ t, sectionAct F (a i) x :=
  map_sum (AddMonoidHom.mk' (fun a ↦ sectionAct F a x) fun a b ↦ add_sectionAct F a b x) a t

lemma sectionAct_sum {ι : Type*} (t : Finset ι) (a : (adicConstantSheaf l X).obj.obj U)
    (x : ι → F.X.obj.obj U) :
    sectionAct F a (∑ i ∈ t, x i) = ∑ i ∈ t, sectionAct F a (x i) :=
  map_sum (AddMonoidHom.mk' (fun x ↦ sectionAct F a x) fun x y ↦ sectionAct_add F a x y) x t

end AlgebraicGeometry.ProEtale.AdicSheaf
