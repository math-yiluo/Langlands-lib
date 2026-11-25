/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ExceptionalTensorMapBaseChange
public import WeilConjectures.PoincareDuality.ProjectionFormulaBaseChange
public import WeilConjectures.TraceFormula.PurityTensorMap

/-!

# The purity map under base change

For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type, the pullback along `g'` of the purity map
`γ_{f,K} : Lf^* K ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! K`, followed by the exceptional base change map
`Lg'^* Rf^! K ⟶ Rf'^! Lg^* K`, is the purity map `γ_{f', Lg^* K}` precomposed with the exceptional
base change map at the unit `Lg'^* Rf^! ℚ̄_ℓ ⟶ Rf'^! ℚ̄_ℓ`
(`ProEtale.CondensedRing.map_upperShriekUnitTensorMap_comp_upperShriekBaseChange`; blueprint
`proposition-exceptional-inverse-image-smooth-morphism`, compatibility of (G11) with (G12), and
`proposition-compatibility-purity-base-change` (2)). This is a formal consequence of the
compatibility of the projection formula with base change
(`ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection`).

Consequently, if the purity maps of `f` and `f'` are isomorphisms and the exceptional base change
map is an isomorphism at the unit, it is an isomorphism everywhere
(`ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_isIso_unit`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The purity map is compatible with base change** (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`, compatibility of (G11) with (G12);
`proposition-compatibility-purity-base-change` (2)): for a cartesian square, the pullback along `g'`
of the purity map `γ_{f,K}` followed by the exceptional base change map is the tensor structure of
`Lg'^*`, the pullback comparison `Lg'^* Lf^* ≅ Lf'^* Lg^*`, the exceptional base change map at the
unit (followed by `Lg^* ℚ̄_ℓ ≅ ℚ̄_ℓ`), and the purity map `γ_{f', Lg^* K}`. -/
theorem map_upperShriekUnitTensorMap_comp_upperShriekBaseChange (sq : IsPullback g' f' f g)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
        (upperShriekUnitTensorMap ℓ f K) ≫ upperShriekBaseChange ℓ sq K =
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ≫
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq).inv.app K ▷ _) ≫
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K) ◁
          (upperShriekBaseChange ℓ sq (𝟙_ _) ≫
            (boundedConstructibleUpperShriek ℓ f').map
              (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)))) ≫
        upperShriekUnitTensorMap ℓ f'
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj K) :=
  -- the coefficient ring is written explicitly: leaving it to unification produces different
  -- (propositionally equal) instances, and comparing the two statements then times out
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have h := ProjectionBaseChange.map_tensorMap_comp_baseChange
    (boundedConstructibleUpperShriekAdjunction ℓ f')
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq)
    (boundedConstructibleExceptionalProjection ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f')
    (pfBaseChange_boundedConstructibleExceptionalProjection ℓ sq)
    (fun A B ↦ boundedConstructibleUpperStar_map_braiding_hom_δ
      ℓ g' A B) K
    (upperShriekUnitTensorMap ℓ f K) (Equiv.symm_apply_apply _ _)
    (upperShriekUnitTensorMap ℓ f' _) (Equiv.symm_apply_apply _ _)
    (upperShriekBaseChange ℓ sq K) (Equiv.symm_apply_apply _ _)
    (upperShriekBaseChange ℓ sq (𝟙_ _)) (Equiv.symm_apply_apply _ _)
  h

/-- **Base change of `Rf^!` from base change at the unit** (blueprint
`proposition-compatibility-purity-base-change`, "tensor map" step,
`proposition-compatibility-purity-base-change` (2)): if the purity maps `γ_{f,K}` and
`γ_{f', Lg^* K}` are isomorphisms and the exceptional base change map is an isomorphism at the unit,
then the exceptional base change map `Lg'^* Rf^! K ⟶ Rf'^! Lg^* K` is an isomorphism. -/
theorem isIso_upperShriekBaseChange_of_isIso_unit (sq : IsPullback g' f' f g)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso (upperShriekUnitTensorMap ℓ f K)]
    [IsIso (upperShriekUnitTensorMap ℓ f' ((boundedConstructibleUpperStar _ ℓ g).obj K))]
    [IsIso (upperShriekBaseChange ℓ sq (𝟙_ _))] :
    IsIso (upperShriekBaseChange ℓ sq K) := by
  have h := map_upperShriekUnitTensorMap_comp_upperShriekBaseChange ℓ sq K
  have : IsIso ((boundedConstructibleUpperStar _ ℓ g').map (upperShriekUnitTensorMap ℓ f K) ≫
      upperShriekBaseChange ℓ sq K) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((boundedConstructibleUpperStar _ ℓ g').map (upperShriekUnitTensorMap ℓ f K)) _

end AlgebraicGeometry.ProEtale.CondensedRing
