/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ExceptionalTensorMap
public import WeilConjectures.PoincareDuality.ProjectionFormulaMonoidal
public import WeilConjectures.TraceFormula.PurityTensorMapShift

/-!

# The purity map on dualizable objects

For any morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the purity map
`γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K` (`ProEtale.CondensedRing.upperShriekUnitTensorMap`) is an
isomorphism when `K` is dualizable
(`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_isDualizable`), the projection
formula being a module structure over `Lf^*`; and its invertibility only depends on `K` up to
isomorphism (`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_iso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The purity map is an isomorphism on dualizable objects**: for any `f` and a dualizable `K`,
`γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K` is an isomorphism, the projection formula being a module
structure over `Lf^*`. -/
theorem isIso_upperShriekUnitTensorMap_of_isDualizable (f : X ⟶ Y)
    {K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hK : IsDualizable K) :
    IsIso (upperShriekUnitTensorMap ℓ f K) := by
  obtain ⟨_⟩ := hK
  let := BraidedCategory.exactPairing_swap K Kᘁ
  exact Adjunction.isIso_exceptionalTensorMap
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f)
    (boundedConstructibleExceptionalProjection_unit ℓ f)
    (boundedConstructibleExceptionalProjection_tensor ℓ f) Kᘁ K

/-- The invertibility of the purity map `γ_{f,K}` only depends on `K` up to isomorphism. -/
lemma isIso_upperShriekUnitTensorMap_of_iso (f : X ⟶ Y)
    {K K' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : K ≅ K')
    [IsIso (upperShriekUnitTensorMap ℓ f K')] : IsIso (upperShriekUnitTensorMap ℓ f K) := by
  have hn := upperShriekUnitTensorMap_naturality ℓ f e.hom
  have : IsIso (upperShriekUnitTensorMap ℓ f K ≫
      (boundedConstructibleUpperShriek ℓ f).map e.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((boundedConstructibleUpperShriek ℓ f).map e.hom)

end AlgebraicGeometry.ProEtale.CondensedRing
