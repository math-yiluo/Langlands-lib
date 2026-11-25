/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.ProjectionFormulaComposition
public import WeilConjectures.PoincareDuality.ProjectionFormulaProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence

/-!

# Coherence of the exceptional projection morphism

For a proper morphism `f`, the exceptional projection morphism
`PF^!_{f,T,M} : Rf_! T ⊗ᴸ M ⟶ Rf_! (T ⊗ᴸ Lf^* M)` is the projection morphism of the adjunction
`Lf^* ⊣ Rf_!` (the adjunction `Lf^* ⊣ Rf_*` transported along `Rf_! ≅ Rf_*`): its adjoint is
`Lf^* (Rf_! T ⊗ᴸ M) ≅ Lf^* Rf_! T ⊗ᴸ Lf^* M ⟶ T ⊗ᴸ Lf^* M`, the counit tensored with
`Lf^* M`.

## Main statements

- `ProEtale.CondensedRing.upperStar_map_exceptionalProjection_comp_counit`: the clause
  "identification with the direct-image projection formula through `Rf_! ≅ Rf_*` for proper `f`"
  of blueprint `prop-sf-pf-coherence` (section `chap-The-six-operations-on-Dbctf`).
- `ProEtale.CondensedRing.exceptionalProjection_comp`: the clause "the associativity pentagon
  for composable `f`, `g`, compatible with the composition law" of `prop-sf-pf-coherence`.
- `ProEtale.CondensedRing.exceptionalProjection_id`: the clause "the identity for `f = id`" of
  `prop-sf-pf-coherence`.

They are proved in `WeilConjectures.PoincareDuality.ProjectionFormulaProper` (the first and the
last) and `WeilConjectures.PoincareDuality.ProjectionFormulaComposition` (composition).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The exceptional projection morphism of a proper morphism is the projection morphism of
`Lf^* ⊣ Rf_!`** (blueprint `prop-sf-pf-coherence`, the identification with the direct-image
projection formula through `Rf_! ≅ Rf_*` for proper `f`): the adjoint of `PF^!_{f,T,M}` for
`Lf^* ⊣ Rf_!` is the counit at `T` tensored with `Lf^* M`, read through the tensor structure of
`Lf^*`. -/
theorem upperStar_map_exceptionalProjection_comp_counit (f : X ⟶ Y) [IsProper f.left]
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ f).map
        (boundedConstructibleExceptionalProjectionMorphism ℓ f T M) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app
        (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M) =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ f)
        ((boundedConstructibleLowerShriek ℓ f).obj T) M ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app T ▷
        (boundedConstructibleUpperStar _ ℓ f).obj M :=
  Adjunction.map_comp_ofNatIsoRight_counit (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).symm _
    (boundedConstructibleExceptionalProjectionMorphism_comp_lowerShriekIsoLowerStar ℓ f T M)

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- **The exceptional projection morphism is compatible with composition** (blueprint
`prop-sf-pf-coherence`, the associativity pentagon for composable `f`, `g`, compatible with the
composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`). -/
theorem exceptionalProjection_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (f ≫ g) T M ≫
        (boundedConstructibleLowerShriek ℓ (f ≫ g)).map
          (T ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app M) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app T ▷ M ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ g
          ((boundedConstructibleLowerShriek ℓ f).obj T) M ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ f T
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app
          (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) :=
  boundedConstructibleExceptionalProjectionMorphism_comp_whiskerLeft ℓ f g T M

variable (X) in
/-- **The exceptional projection morphism of the identity is the identity** (blueprint
`prop-sf-pf-coherence`, the identity for `f = id`), read through the identity isomorphisms
`R(𝟙)_! ≅ R(𝟙)_* ≅ 𝟭` and `L(𝟙)^* ≅ 𝟭`. -/
theorem exceptionalProjection_id (T M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (𝟙 X) T M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X)).hom.app _ ≫
        (boundedConstructibleLowerStarId ℓ X).hom.app _ ≫
        T ◁ (boundedConstructibleUpperStarId _ ℓ X).hom.app M =
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X)).hom.app T ≫
        (boundedConstructibleLowerStarId ℓ X).hom.app T) ▷ M := by
  have h := boundedConstructibleExceptionalProjectionMorphism_comp_lowerShriekIsoLowerStar ℓ (𝟙 X)
    T M
  have h' := Adjunction.projectionMorphism_comp_conjugate_id
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    (boundedConstructibleUpperStarId _ ℓ X)
    (fun X' Y' ↦ boundedConstructibleUpperStarId_hom_app_tensor_δ ℓ X X' Y') T M
  rw [reassoc_of% h, boundedConstructibleLowerStarId, reassoc_of% h', ← whiskerLeft_comp,
    Iso.inv_hom_id_app, comp_whiskerRight]
  simp

end AlgebraicGeometry.ProEtale.CondensedRing
