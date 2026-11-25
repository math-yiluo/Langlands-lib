/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
import WeilConjectures.TraceFormula.OrdinaryKunnethGlobal

/-!
# The ordinary Künneth formula for global sections over a field

For a cartesian square `P = X ×_K Y` of separated `K`-schemes of finite type and bounded
constructible `ℚ̄_ℓ`-complexes `A` on `X` and `B` on `Y`, the ordinary Künneth map
`RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(P, Lp₁^* A ⊗ Lp₂^* B)` (`ProEtale.CondensedRing.lowerStarKunnethMap'`
of the two squares over `Spec K`) is an isomorphism
(`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback`; blueprint
`lemma-kunneth-one-identity-factor--1`, for `fᵢ : Xᵢ ⟶ Spec K`).

The proof is `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback_point` of
`WeilConjectures.TraceFormula.OrdinaryKunnethGlobal`, for the morphisms of `Over (Spec K)`
defined by the square. That module is imported privately: it imports the six functors on `Dᵇc`,
whose instances would change the elaboration of statements on the ambient derived categories in
the importing modules.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable {K : Type u} [Field K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  {X Y P : Over (Spec (.of K))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **The ordinary Künneth formula for global sections over a field** (blueprint
`lemma-kunneth-one-identity-factor--1`, for `fᵢ : Xᵢ ⟶ Spec K`; SGA 4½, [Th. finitude], Cor. 1.11):
for a cartesian square `P = X ×_K Y` of separated `K`-schemes of finite type and bounded
constructible `A`, `B`, the Künneth map `RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(X ×_K Y, A ⊠ B)` is an
isomorphism. -/
theorem isIso_lowerStarKunnethMap'_of_isPullback (p₁ : P.left ⟶ X.left)
    (p₂ : P.left ⟶ Y.left)
    (w₁ : p₁ ≫ X.hom = P.hom ≫ 𝟙 _) (w₂ : p₂ ≫ Y.hom = P.hom ≫ 𝟙 _)
    (h : IsPullback p₁ p₂ X.hom Y.hom)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) A)
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) B) :
    IsIso (lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ)
      (⟨w₁⟩ : CommSq p₁ P.hom X.hom (𝟙 _)) (⟨w₂⟩ : CommSq p₂ P.hom Y.hom (𝟙 _)) A B) := by
  exact_mod_proofs isIso_lowerStarKunnethMap'_of_isPullback_point ℓ
    (p₁ := (Over.homMk p₁ (w₁.trans (Category.comp_id _)) : P ⟶ X))
    (p₂ := (Over.homMk p₂ (w₂.trans (Category.comp_id _)) : P ⟶ Y)) h
    (q := (Over.homMk P.hom (Category.comp_id _) : P ⟶ point K))
    (a := (Over.homMk X.hom (Category.comp_id _) : X ⟶ point K))
    (b := (Over.homMk Y.hom (Category.comp_id _) : Y ⟶ point K))
    (Over.OverMorphism.ext w₁.symm) (Over.OverMorphism.ext w₂.symm) ⟨w₁⟩ ⟨w₂⟩ ⟨A, hA⟩ ⟨B, hB⟩

end AlgebraicGeometry.ProEtale.CondensedRing
