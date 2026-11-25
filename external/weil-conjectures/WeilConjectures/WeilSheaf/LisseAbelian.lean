/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.WeilSheaf.LisseFiltration

/-!
# The abelian category of lisse Weil sheaves

Lisse Weil sheaves on a `k₀`-scheme `X` locally of finite type contain zero and are closed under
kernels, cokernels and finite products in the abelian category of Weil sheaves, so they form an
abelian full subcategory whose inclusion is exact. In particular a short complex of lisse Weil
sheaves is short exact in the category of lisse Weil sheaves if and only if it is short exact as
a complex of Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

instance : ObjectProperty.IsClosedUnderIsomorphisms (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) where
  of_iso e hF := hF.of_iso e

instance : ObjectProperty.ContainsZero (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) where
  exists_zero := ⟨0, isZero_zero _, isLisse_of_isZero (isZero_zero _)⟩

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

instance : ObjectProperty.IsClosedUnderKernels (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsLisse.kernel_cokernel hX hY f).1.of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)

instance : ObjectProperty.IsClosedUnderCokernels (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsLisse.kernel_cokernel hX hY f).2.of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)

instance : ObjectProperty.IsClosedUnderFiniteProducts (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) :=
  have : ObjectProperty.IsClosedUnderBinaryProducts (fun F : WeilSheaf k₀ l X ↦ F.IsLisse) :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      exact (IsLisse.biprod (hF ⟨.left⟩) (hF ⟨.right⟩)).of_iso
        ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm))
  .mk'

end AlgebraicGeometry.WeilSheaf
