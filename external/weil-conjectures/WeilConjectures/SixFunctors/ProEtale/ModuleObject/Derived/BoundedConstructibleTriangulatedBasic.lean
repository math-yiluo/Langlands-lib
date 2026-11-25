/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift

/-!
# The six functors on bounded constructible complexes are triangulated

Let `Λ` be a coefficient ring of Deligne's finiteness theorems. For a scheme `X` separated and of
finite type over a field `k`, the underlying topological space of `X` is noetherian
(`AlgebraicGeometry.noetherianSpace_left_of_locallyOfFiniteType`), so the bounded constructible
complexes form a triangulated subcategory of `D(Mod_{Λ_X})`
(`ProEtale.isTriangulated_boundedConstructible`) and `Dᵇc(X)⟦Λ⟧` is pretriangulated. This file
shows that the restricted functors `Lf^*`, `Rf_*`, `j_!` and `Rf_!` on these categories are
triangulated, and, for the `ℓ`-adic coefficient rings, so are `K ⊗ᴸ -`, `- ⊗ᴸ K` and
`RHom(K, -)`.

`Lf^*`, `Rf_*`, `j_!` and `K ⊗ᴸ -` are induced by the triangulated functors of the ambient
derived categories; `Rf_!` is the composite `j_! ⋙ Rp_*` along a compactification; and
`RHom(K, -)` is the right adjoint of `K ⊗ᴸ -`
(`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`). The commutation of `RHom(K, -)` with
the shifts is the one for which the tensor-hom adjunction
`ProEtale.CondensedRing.boundedConstructibleTensorIhomAdjunction` commutes with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The underlying space of a scheme of finite type over a field is noetherian. -/
instance noetherianSpace_left_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    TopologicalSpace.NoetherianSpace X.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  infer_instance

namespace ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

instance isTriangulated_boundedConstructibleUpperStar (f : X ⟶ Y) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).IsTriangulated := by
  delta boundedConstructibleUpperStar
  infer_instance

instance isTriangulated_boundedConstructibleLowerStar (f : X ⟶ Y) :
    (boundedConstructibleLowerStar ℓ f).IsTriangulated := by
  delta boundedConstructibleLowerStar
  infer_instance

instance isTriangulated_boundedConstructibleLowerStarOfIsProper (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ f).IsTriangulated := by
  delta boundedConstructibleLowerStarOfIsProper
  infer_instance

instance isTriangulated_boundedConstructibleOpenImmersionLowerShriek {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        j).IsTriangulated := by
  delta boundedConstructibleOpenImmersionLowerShriek
  infer_instance

instance isTriangulated_boundedConstructibleLowerShriekOfCompactification {f : X ⟶ Y}
    (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification ℓ c).IsTriangulated := by
  delta boundedConstructibleLowerShriekOfCompactification
  infer_instance

instance isTriangulated_boundedConstructibleLowerShriek (f : X ⟶ Y) :
    (boundedConstructibleLowerShriek ℓ f).IsTriangulated := by
  delta boundedConstructibleLowerShriek
  infer_instance

section Tensor

variable {ℓ}

instance isTriangulated_boundedConstructible_tensorRight (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).flip.obj K).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (ObjectProperty.tensorRightIsoLift _ K) ℤ
  exact Functor.isTriangulated_of_iso (ObjectProperty.tensorRightIsoLift _ K)

instance isTriangulated_boundedConstructible_tensorLeft (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
    ℓ⟧) :
    ((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (ObjectProperty.tensorLeftIsoLift _ K) ℤ
  exact Functor.isTriangulated_of_iso (ObjectProperty.tensorLeftIsoLift _ K)

/-- The tensor-hom adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, with left adjoint written as
`(curriedTensor _).obj K`. -/
noncomputable def boundedConstructibleTensorIhomAdjunction (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K ⊣ ihom K :=
  ihom.adjunction K

/-- The derived internal hom `RHom(K, -)` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commutes with the shifts: the
commutation
of the right adjoint of `K ⊗ᴸ -`. -/
noncomputable instance commShift_boundedConstructible_ihom (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom K).CommShift ℤ :=
  (boundedConstructibleTensorIhomAdjunction K).rightAdjointCommShift ℤ

instance commShift_boundedConstructibleTensorIhomAdjunction (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensorIhomAdjunction K).CommShift ℤ :=
  (boundedConstructibleTensorIhomAdjunction K).commShift_of_leftAdjoint ℤ

instance isTriangulated_boundedConstructible_ihom (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom K).IsTriangulated :=
  (boundedConstructibleTensorIhomAdjunction K).isTriangulated_rightAdjoint

end Tensor

end ProEtale.CondensedRing

end AlgebraicGeometry
