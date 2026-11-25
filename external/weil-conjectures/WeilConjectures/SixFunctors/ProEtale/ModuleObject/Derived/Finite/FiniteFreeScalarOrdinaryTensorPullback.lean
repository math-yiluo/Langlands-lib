/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import all WeilConjectures.AlgebraicGeometry.InternalScalarOrdinaryTensorPullModel

/-! # Ordinary inverse scalar tensor square

Source: the ordinary balanced tensor pullback square, in the inverse comparison direction.
(blueprint: new-sfb-finite-free-scalar-ordinary-tensor-pullback)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

private lemma inverse_square {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {P Q : A} {R S : B} (e : P ≅ Q) (d : R ≅ S)
    (q : F.obj P ⟶ R) (v : F.obj Q ⟶ S)
    (h : q ≫ d.hom = F.map e.hom ≫ v) :
    F.map e.inv ≫ q = v ≫ d.inv := by
  apply (cancel_mono d.hom).1
  rw [Category.assoc, h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id,
    Category.id_comp, Category.assoc, d.inv_hom_id, Category.comp_id]

/-- The inverse balanced tensor identification commutes with ordinary pullback.

Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.5.9(5), and the blueprint
scalar-six formal properties.
(blueprint: new-sfb-finite-free-scalar-ordinary-tensor-pullback)

Proof. The forward balanced tensor square is residueOrdinaryTensorPull_module.
Its transported pullback tensorator equals the native tensorator by native_pull_oplax.
Compose this square on the left with pullback of the inverse Y-comparison and on the
right with the inverse X-comparison. The two inverse/hom pairs cancel. This argument
uses no flatness hypothesis, so it also covers the zero module and the zero ring. -/
theorem finiteFreeScalar_ordinaryTensor_pullback
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    let F := CondensedRing.upperStar Λ f
    let : F.OplaxMonoidal := (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
    F.map ((Mod.extendComapTensorIso (coefficientMap φ Y)).inv.app M) ≫
      (comapUpperStarIso φ f).inv.app ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≫
      (Mod.comap (coefficientMap φ X)).map ((pullIso φ f).inv.app M) =
    Functor.OplaxMonoidal.δ F
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) M ≫
      (residueOrdinaryRestrictedRegularPullIso Λ A φ f).hom ▷ F.obj M ≫
      (Mod.extendComapTensorIso (coefficientMap φ X)).inv.app (F.obj M) := by
  dsimp only
  let F := CondensedRing.upperStar Λ f
  let : F.OplaxMonoidal := (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  have h := residueOrdinaryTensorPull_module Λ A φ f M
  dsimp only at h
  rw [← QuotientChange.native_pull_oplax Λ f] at h
  exact inverse_square F
    ((Mod.extendComapTensorIso (coefficientMap φ Y)).app M)
    ((Mod.extendComapTensorIso (coefficientMap φ X)).app (F.obj M))
    ((comapUpperStarIso φ f).inv.app ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≫
      (Mod.comap (coefficientMap φ X)).map ((pullIso φ f).inv.app M))
    (Functor.OplaxMonoidal.δ F
        ((Mod.comap (coefficientMap φ Y)).obj (Mod.regular (condensedRingObj A Y))) M ≫
      (residueOrdinaryRestrictedRegularPullIso Λ A φ f).hom ▷ F.obj M)
    (by simpa only [Iso.app_hom, Category.assoc] using h)

end AlgebraicGeometry.ProEtale.CondensedRing
