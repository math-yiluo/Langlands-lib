/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidueIdeal
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ResidueTorTest

/-!
# Testing Tor amplitude on finitely generated constant sheaves

Let `Λ` be a commutative ring and `K ∈ D(X_ét, Λ)`. If `K ⊗ᴸ M_X` has homology in `[a, b]` for
every finitely generated `Λ`-module `M`, then `K` has Tor amplitude in `[a, b]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_of_forall_finite_constantSheaf`).

Represent `K` by a K-flat complex `P` of flat sheaves. Exactness of `P ⊗ F` is checked on the
stalks at the geometric points `x̄`, where it is the exactness of `P_x̄ ⊗ F_x̄`. As `P_x̄` is a
complex of flat modules, this follows from the exactness of `P_x̄ ⊗ M` for the finitely generated
submodules `M` of `F_x̄` (`LinearMap.exact_rTensor_of_forall_finite`), and `P_x̄ ⊗ M` is the stalk
of `P ⊗ M_X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Let `P` be a complex of flat étale sheaves of `Λ`-modules. If `P ⊗ M_X` is exact in degree
`q` for every finitely generated `Λ`-module `M`, then so is `P ⊗ F` for every sheaf `F`: on the
stalks this is `LinearMap.exact_rTensor_of_forall_finite`. -/
lemma exactAt_tensorRight_of_forall_finite_constantSheaf
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n)) (q : ℤ)
    (h : ∀ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M →
      (((tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).ExactAt q)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q := by
  refine exactAt_of_forall_exactAt_sheafFiber _ q fun s ↦ ?_
  let Φ := X.uliftPointSmallEtale s
  let Ps := (Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : Module.Flat Λ (Ps.X (q + 1)) :=
    (ModuleCat.flat_iff_flat _).1 (Φ.flat_sheafFiber_obj (hP _))
  have hd : (Ps.d q (q + 1)).hom ∘ₗ (Ps.d (q - 1) q).hom = 0 := by
    rw [← ModuleCat.hom_comp, Ps.d_comp_d, ModuleCat.hom_zero]
  refine (((_root_.DerivedCategory.exactAt_tensorRight_iff Ps _ q).2 ?_).of_iso
    (sheafFiberMapHomologicalComplexTensorRightIso s P F).symm)
  refine LinearMap.exact_rTensor_of_forall_finite _ _ hd fun N hN ↦ ?_
  let M := ModuleCat.of Λ N
  have hM : (((tensorRight (Φ.sheafFiber.obj ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj M))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        Ps).ExactAt q :=
    (show ((Φ.sheafFiber.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).ExactAt q from
      (h M hN).map Φ.sheafFiber).of_iso (sheafFiberMapHomologicalComplexTensorRightIso s P _)
  rw [_root_.DerivedCategory.exactAt_tensorRight_iff] at hM
  exact LinearMap.exact_rTensor_of_linearEquiv _ _ hd
    (Φ.sheafFiberConstantSheafIso M).toLinearEquiv hM

/-- **Tor amplitude is tested on finitely generated constant sheaves.** Let `K ∈ D(X_ét, Λ)` be
such that `K ⊗ᴸ M_X` has homology concentrated in `[a, b]` for every finitely generated
`Λ`-module `M`. Then `K` has Tor amplitude in `[a, b]`. -/
theorem torAmplitudeIn_of_forall_finite_constantSheaf {a b : ℤ}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M →
      _root_.DerivedCategory.TensorSingleConcentratedIn _ a b K
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    _root_.DerivedCategory.torAmplitudeIn (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) a b
      K := by
  obtain ⟨P, hPk, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_kFlat_flat_iso K
  rw [_root_.DerivedCategory.torAmplitudeIn_iff_forall_exactAt hPk e]
  exact fun F q hq ↦ exactAt_tensorRight_of_forall_finite_constantSheaf P hP q
    (fun M hM ↦ (_root_.DerivedCategory.homologyConcentratedIn_tensor_iff_exactAt hPk e _ a b).1
      (h M hM) q hq) F

end Etale

end AlgebraicGeometry
