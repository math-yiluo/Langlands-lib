/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs

/-!
# The projection formula for proper morphisms on bounded constructible `ℚ̄_ℓ`-sheaves

For a proper morphism `p : X ⟶ Y` of separated `k`-schemes of finite type, the projection
morphism `Rp_* A ⊗ᴸ B ⟶ Rp_* (A ⊗ᴸ Lp^* B)` of the adjunction `Lp^* ⊣ Rp_*` on bounded
constructible `ℚ̄_ℓ`-sheaves (`CategoryTheory.Adjunction.projectionMorphism`) is an isomorphism.
The adjunction and the monoidal structure of `Lp^*` on `Dᵇc` are the restrictions of those of the
ambient derived categories, so the projection morphism is the restriction of the projection map
of the ambient derived categories
(`CategoryTheory.Adjunction.ι_map_projectionMorphism_restrictFullyFaithful`), which is an
isomorphism on bounded constructible complexes by blueprint
`proposition-proper-direct-image-constructible-complexes`
(`ProEtale.CondensedRing.properDirectImage_baseChange_projectionFormula_padicAlgClRingObj`).

## Main statements

- `ProEtale.CondensedRing.isIso_projectionMorphism_boundedConstructible_padicAlgCl`: the
  projection formula for proper morphisms on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The projection formula for proper morphisms** on bounded constructible `ℚ̄_ℓ`-sheaves: for
`p` proper, the projection morphism `Rp_* A ⊗ᴸ B ⟶ Rp_* (A ⊗ᴸ Lp^* B)` of `Lp^* ⊣ Rp_*` is an
isomorphism. -/
instance isIso_projectionMorphism_boundedConstructible_padicAlgCl (p : X ⟶ Y) [IsProper p.left]
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      p).projectionMorphism A B) := by
  have h := Adjunction.ι_map_projectionMorphism_restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ p K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ p K) A B
  have : IsIso ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      p.left).projectionMorphism A.obj B.obj) :=
    (properDirectImage_baseChange_projectionFormula_padicAlgClRingObj ℓ (X' := X) (Y' := Y)
      p).2.2 A.obj B.obj
      A.property B.property
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        p).projectionMorphism A B)) := by
    erw [h]
    infer_instance
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

end AlgebraicGeometry.ProEtale.CondensedRing
