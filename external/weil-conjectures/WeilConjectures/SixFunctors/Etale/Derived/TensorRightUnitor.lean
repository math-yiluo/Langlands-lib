/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The right unitor of the derived tensor product as a natural isomorphism

The right unitor `K ⊗ᴸ Λ_X ≅ K` of the derived tensor product
(`AlgebraicGeometry.Etale.derivedTensorRightUnitor`), as a natural isomorphism
`- ⊗ᴸ Λ_X ≅ 𝟭` (`AlgebraicGeometry.Etale.derivedTensorRightUnitorNatIso`).

It is stated for an arbitrary coefficient category: at a concrete one such as `ModuleCat Λ`,
the kernel check of the naturality proof unfolds the monoidal structure of the derived category
and times out, while specializing this general isomorphism is cheap.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

namespace Etale

/-- The right unitor `K ⊗ᴸ Λ_X ≅ K` of the derived tensor product, as a natural isomorphism
`- ⊗ᴸ Λ_X ≅ 𝟭`. -/
noncomputable def derivedTensorRightUnitorNatIso :
    (derivedTensor A X).flip.obj (𝟙_ _) ≅
      𝟭 (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  NatIso.ofComponents (derivedTensorRightUnitor A X) fun f ↦ rightUnitor_naturality f

end Etale

end AlgebraicGeometry
