/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Integral.IntegralHomReductionComparison
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
/-! # The actual Koszul swap between tensor representatives
Source: Stacks Tags 06YU and 0FPQ.
(blueprint: def-sfb-integral-hom-tensor-representative-swap)
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
variable {X : AlgebraicGeometry.Scheme.{u}}
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
/-- The native complex braiding, with the presentation's two tensor spellings.
Source: Stacks 0FPQ (blueprint: def-sfb-integral-hom-tensor-representative-swap). -/
noncomputable def tensorRepresentativeSwap
    (P Q : CochainComplex (Modules.{u, u} X R) ℤ) :
    ((totalTensor.{u, u} X R).obj P).obj Q ≅ homReductionTotal R Q P := by
  exact CategoryTheory.BraidedCategory.braiding P Q

/-- The swap has the usual Koszul formula on the actual tensor generators.
Source: Stacks 0FPQ. Proof: specialize the proved complex-constraint formula.
(blueprint: def-sfb-integral-hom-tensor-representative-swap) -/
theorem tensorRepresentativeSwap_pure
    (P Q : CochainComplex (Modules.{u, u} X R) ℤ)
    (i j k : ℤ) (hij : i + j = k) (hji : j + i = k)
    (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    (((tensorRepresentativeSwap R P Q).hom.f k).val.app U)
        (coefficientTensorGenerator.{u, u + 1, u}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j k hij U x y) =
      (i * j).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) R Q P j i k hji U y x := by
  exact (CategoryTheory.RingedDerivedNative.complexConstraints.{u + 1, u, u}
    (AlgebraicGeometry.Scheme.ProEt.topology X) R).symmetry P Q i j k hij hji U x y
end WeilConjectures.IntegralHom
