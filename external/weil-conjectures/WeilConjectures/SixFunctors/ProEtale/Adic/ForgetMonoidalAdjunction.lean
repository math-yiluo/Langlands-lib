/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLaxMonoidal

/-!
# The free module on an abelian group, as a monoidal left adjoint

For a commutative ring `R`, the functor `M ↦ R ⊗[ℤ] M` from abelian groups to `R`-modules
(`ModuleCat.extendScalarsAb`) is left adjoint to the forgetful functor
(`ModuleCat.extendScalarsAbAdj`). The forgetful functor being lax monoidal
(`ModuleCat.laxMonoidalForget₂Ab`), the left adjoint is oplax monoidal, and its comparison maps
are the isomorphisms `R ⊗[ℤ] (M ⊗[ℤ] N) ≅ (R ⊗[ℤ] M) ⊗[R] (R ⊗[ℤ] N)` and `R ⊗[ℤ] ℤ ≅ R`, so it
is strong monoidal (`ModuleCat.extendScalarsAbMonoidal`), and the adjunction is monoidal.
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable (R : Type v) [CommRing R]

/-- The free `R`-module `R ⊗[ℤ] M` on an abelian group `M`. -/
@[simps obj map]
noncomputable def extendScalarsAb : Ab.{v} ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (R ⊗[ℤ] M)
  map f := ModuleCat.ofHom (LinearMap.baseChange R f.hom.toIntLinearMap)
  map_id _ := ModuleCat.hom_ext (AlgebraTensorModule.ext fun _ _ ↦ rfl)
  map_comp _ _ := ModuleCat.hom_ext (AlgebraTensorModule.ext fun _ _ ↦ rfl)

/-- The bijection `(R ⊗[ℤ] M →ₗ[R] N) ≃ (M →+ N)` of the free-forgetful adjunction. -/
noncomputable def extendScalarsAbHomEquiv (M : Ab.{v}) (N : ModuleCat.{v} R) :
    ((extendScalarsAb R).obj M ⟶ N) ≃ (M ⟶ (forget₂ (ModuleCat.{v} R) Ab.{v}).obj N) where
  toFun f := AddCommGrpCat.ofHom
    ((f.hom.restrictScalars ℤ).toAddMonoidHom.comp (TensorProduct.mk ℤ R M 1).toAddMonoidHom)
  invFun g := ModuleCat.ofHom (LinearMap.liftBaseChange R g.hom.toIntLinearMap)
  left_inv f := ModuleCat.hom_ext (AlgebraTensorModule.ext fun r m ↦
    (f.hom.map_smul r (1 ⊗ₜ m)).symm.trans (congrArg f.hom (by rw [smul_tmul', smul_eq_mul,
      mul_one])))
  right_inv g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m ↦ one_smul R (α := N) (g.hom m))

/-- The free `R`-module functor `M ↦ R ⊗[ℤ] M` is left adjoint to the forgetful functor. -/
noncomputable def extendScalarsAbAdj :
    extendScalarsAb R ⊣ forget₂ (ModuleCat.{v} R) Ab.{v} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extendScalarsAbHomEquiv R
      homEquiv_naturality_left_symm _ _ :=
        ModuleCat.hom_ext (AlgebraTensorModule.ext fun _ _ ↦ rfl)
      homEquiv_naturality_right _ _ := rfl }

open Functor.OplaxMonoidal

/-- The oplax monoidal structure on the free `R`-module functor, as the left adjoint of the lax
monoidal forgetful functor. -/
noncomputable abbrev extendScalarsAbOplaxMonoidal : (extendScalarsAb R).OplaxMonoidal :=
  (extendScalarsAbAdj R).leftAdjointOplaxMonoidal

/-- The comparison `δ` of the free `R`-module functor is the isomorphism
`R ⊗[ℤ] (M ⊗[ℤ] N) ≅ (R ⊗[ℤ] M) ⊗[R] (R ⊗[ℤ] N)`. -/
lemma extendScalarsAb_δ_eq (M N : Ab.{v}) :
    letI := extendScalarsAbOplaxMonoidal R
    δ (extendScalarsAb R) M N =
      (AlgebraTensorModule.distribBaseChange ℤ R M N).toModuleIso.hom := by
  let := extendScalarsAbOplaxMonoidal R
  refine ModuleCat.hom_ext (AlgebraTensorModule.curry_injective (LinearMap.ext fun r ↦
    TensorProduct.ext' fun m n ↦ ?_))
  exact (smul_tmul' (R := R) r ((1 : R) ⊗ₜ[ℤ] m : R ⊗[ℤ] M) ((1 : R) ⊗ₜ[ℤ] n : R ⊗[ℤ] N)).trans
    (congrArg (· ⊗ₜ[R] ((1 : R) ⊗ₜ[ℤ] n : R ⊗[ℤ] N))
      ((smul_tmul' r (1 : R) m).trans (congrArg (· ⊗ₜ[ℤ] m) (mul_one r))))

/-- The comparison `η` of the free `R`-module functor is the isomorphism `R ⊗[ℤ] ℤ ≅ R`. -/
lemma extendScalarsAb_η_eq :
    letI := extendScalarsAbOplaxMonoidal R
    η (extendScalarsAb R) =
      ((AlgebraTensorModule.congr (LinearEquiv.refl R R) ULift.moduleEquiv) ≪≫ₗ
        AlgebraTensorModule.rid ℤ R R).toModuleIso.hom := by
  let := extendScalarsAbOplaxMonoidal R
  refine ModuleCat.hom_ext (AlgebraTensorModule.ext fun r n ↦ ?_)
  exact (smul_comm r (ULift.down n) (1 : R)).trans (congrArg (ULift.down n • ·) (mul_one r))

/-- The free `R`-module functor `M ↦ R ⊗[ℤ] M` is strong monoidal: the comparison maps of its
oplax monoidal structure as a left adjoint are isomorphisms. -/
noncomputable instance extendScalarsAbMonoidal : (extendScalarsAb R).Monoidal :=
  letI := extendScalarsAbOplaxMonoidal R
  have (M N : Ab.{v}) : IsIso (δ (extendScalarsAb R) M N) := by
    rw [extendScalarsAb_δ_eq]
    infer_instance
  have : IsIso (η (extendScalarsAb R)) := by
    rw [extendScalarsAb_η_eq]
    infer_instance
  .ofOplaxMonoidal _

/-- The free-forgetful adjunction between abelian groups and `R`-modules is monoidal. -/
instance isMonoidal_extendScalarsAbAdj : (extendScalarsAbAdj R).IsMonoidal :=
  inferInstanceAs (letI := extendScalarsAbOplaxMonoidal R; (extendScalarsAbAdj R).IsMonoidal)

/-- The forgetful functor `ModuleCat R ⥤ Ab` is lax braided. -/
noncomputable instance laxBraidedForget₂Ab : (forget₂ (ModuleCat.{v} R) Ab.{v}).LaxBraided where
  braided _ _ := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

end ModuleCat
