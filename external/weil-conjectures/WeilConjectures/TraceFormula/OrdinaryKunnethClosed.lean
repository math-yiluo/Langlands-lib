/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceFormula.OrdinaryKunnethClosedComposite

/-!

# The ordinary Künneth map and proper pushforward in the first factor

Let `j : U ⟶ Y` be an open immersion and `g : Z ⟶ X` a proper morphism of separated `k`-schemes
of finite type. For `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` and `B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, if the Künneth map
`κ_Z(N, B) : N ⊠ Rj_* B ⟶ R(𝟙 × j)_* (N ⊠ B)` (`ProEtale.CondensedRing.openKunnethMap`) is an
isomorphism, so is `κ_X(Rg_* N, B)`
(`ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isProper`).

## Proof

The second factor of the Künneth map has invertible transpose (generic base change,
`ProEtale.CondensedRing.isIso_exchangeRight_prodMapUpperStarSndIso`), so `κ_X(M, B)` is an
isomorphism if and only if the left projection morphism
`Lp_X^* M ⊗ R(𝟙 × j)_* Lp_U^* B ⟶ R(𝟙 × j)_* (L(𝟙 × j)^* Lp_X^* M ⊗ Lp_U^* B)` is
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism`).
These left projection morphisms are compared
(`ProEtale.CondensedRing.isIso_leftProjectionMorphism_prodMap_lowerStar`) through the Künneth map
of `q = g × j : Z ⨯ U ⟶ X ⨯ Y`, the transpose along `Lq^* ⊣ Rq_*` of
```
Lq^* (Lp_X^* Rg_* N ⊗ Lp_Y^* Rj_* B) ⟶ Lq^* Lp_X^* Rg_* N ⊗ Lq^* Lp_Y^* Rj_* B ⟶ Lp_Z^* N ⊗ Lp_U^* B
```
built from the transported counits (`ProEtale.CondensedRing.prodUpperStarCounit`), decomposed
along the two factorizations of `q`:

* `q = (g × 𝟙_U) ≫ (𝟙_X × j)`: by `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq` it is the
  left projection morphism of `𝟙_X × j` at `(Lp_X^* Rg_* N, Lp_U^* B)` up to proper and generic
  base change morphisms and the proper projection formula for `g × 𝟙_U`
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_of_isIso`);
* `q = (𝟙_Z × j) ≫ (g × 𝟙_Y)`: by the mirrored decomposition
  `CategoryTheory.Adjunction.homEquiv_δ_tensorHom_eq_right` it is `R(g × 𝟙_Y)_*` of the left
  projection morphism of `𝟙_Z × j` at `(Lp_Z^* N, Lp_U^* B)` up to the same kind of isomorphisms
  (`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso_right`).

## Implementation notes

The Künneth maps are only compared through abstract lemmas instantiated by unification: terms
obtained by unfolding definitions contain auxiliary proof constants and `eqToHom`s, and comparing
them with separately elaborated terms makes the elaborator and the kernel unfold large terms.

The abstract decompositions of the Künneth map of a composite and the comparison along
`(𝟙_Z × j) ≫ (g × 𝟙_Y)` are in the module
`OrdinaryKunnethClosedComposite` (split for compile time).

## Main statements

- `ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isProper`
- `ProEtale.CondensedRing.isIso_openKunnethMap_lowerStar_of_isClosedImmersion`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

-- the tensor products are elaborated through the monoidal category instance, as in
-- `WeilConjectures.TraceFormula.OrdinaryKunneth`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable {X Y U Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

-- the instantiation of the abstract lemmas involves large terms
/-- **Left projection morphisms along `𝟙 × j` and proper pushforward in the first factor**: for
a proper `g : Z ⟶ X`, if the left projection morphism of `L(𝟙_Z × j)^* ⊣ R(𝟙_Z × j)_*` at
`(Lp_Z^* N, Lp_U^* B)` is an isomorphism, so is the one of `L(𝟙_X × j)^* ⊣ R(𝟙_X × j)_*` at
`(Lp_X^* Rg_* N, Lp_U^* B)`. Both are compared with the Künneth map of `g × j` along its two
factorizations; the remaining comparison maps are proper and generic base change morphisms and
proper projection morphisms. -/
lemma isIso_leftProjectionMorphism_prodMap_lowerStar (g : Z ⟶ X) [IsProper g.left] (j : U ⟶ Y)
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 Z) j)).leftProjectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : Z ⨯ Y ⟶ Z)).obj N)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : Z ⨯ U ⟶ U)).obj B))) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (prod.map (𝟙 X) j)).leftProjectionMorphism
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.fst : X ⨯ Y ⟶ X)).obj
          ((boundedConstructibleLowerStar ℓ g).obj N))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj B)) := by
  have := isProper_prodMap_id (W := U) g
  have hq : prod.map g (𝟙 U) ≫ prod.map (𝟙 X) j = prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y) := by
    simp
  have hp₁ : (prod.fst : Z ⨯ U ⟶ Z) = prod.map (𝟙 Z) j ≫ prod.fst := by simp
  have hp₂ : prod.map g (𝟙 U) ≫ prod.snd = (prod.snd : Z ⨯ U ⟶ U) := by simp
  have w₁ : (prod.map g (𝟙 U) ≫ prod.map (𝟙 X) j) ≫ prod.fst = prod.fst ≫ g := by simp
  have w₂ : (prod.map g (𝟙 U) ≫ prod.map (𝟙 X) j) ≫ prod.snd =
      (prod.map g (𝟙 U) ≫ prod.snd) ≫ j := by simp
  have w₁' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.fst =
      (prod.map (𝟙 Z) j ≫ prod.fst) ≫ g := by simp
  have w₂' : (prod.map (𝟙 Z) j ≫ prod.map g (𝟙 Y)) ≫ prod.snd = prod.snd ≫ j := by simp
  have hfst : prod.map (𝟙 X) j ≫ prod.fst = prod.fst := by simp
  have sqU : IsPullback (prod.fst : Z ⨯ U ⟶ Z) (prod.map g (𝟙 U)) g
      (prod.map (𝟙 X) j ≫ prod.fst) := by
    rw [hfst]
    exact IsPullback.of_prod_fst_with_id g U
  -- the Künneth map of `g × j` along `(𝟙 × j) ≫ (g × 𝟙)` is an isomorphism
  have hZ := isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_prodMap_id_comp ℓ g j N B w₁' w₂' h
  have hX := (isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_congr ℓ hq hp₁ hp₂ w₁ w₂ w₁' w₂'
    N B).mpr hZ
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map g (𝟙 U))).homEquiv _ _
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map g (𝟙 U)) (prod.map (𝟙 X) j)).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ prod.fst).obj
            ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
        prodUpperStarCounit ℓ w₁ N)) := by
    rw [upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₁ sqU.w.symm N,
      Adjunction.homEquiv_naturality_left]
    have := isIso_homEquiv_prodUpperStarCounit ℓ sqU N
    infer_instance
  have : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction
      ℓ (prod.map (𝟙 X) j)).homEquiv _ _
      (prodUpperStarCounit ℓ (prod.map_snd (𝟙 X) j) B)) := by
    exact isIso_homEquiv_prodUpperStarCounit_of_eq_snd ℓ j rfl _ B
  exact (Adjunction.isIso_homEquiv_δ_tensorHom_iff_of_isIso
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map g (𝟙 U)))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.map (𝟙 X) j)) _
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ _ _)
    (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ _ _) _ _
    (prodUpperStarCounit ℓ (prod.map_snd (𝟙 X) j) B)
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map g (𝟙 U)) prod.snd).inv.app B)
    (upperStarComp_inv_app_comp_prodUpperStarCounit_left ℓ w₂ (prod.map_snd (𝟙 X) j) B)).mp hX

/-- **The ordinary Künneth map and proper pushforward in the first factor**: for a proper
morphism `g : Z ⟶ X`, an open immersion `j : U ⟶ Y`, `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` and
`B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, if the Künneth map `κ_Z(N, B)` is an isomorphism, so is `κ_X(Rg_* N, B)`.
Both are, up to isomorphisms, left projection morphisms along `𝟙 × j`
(`CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism`), which
are compared by `isIso_leftProjectionMorphism_prodMap_lowerStar`. -/
theorem isIso_openKunnethMap_lowerStar_of_isProper (g : Z ⟶ X) [IsProper g.left] (j : U ⟶ Y)
    [IsOpenImmersion j.left] (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (openKunnethMap ℓ (X := Z) j N B)) :
    IsIso (openKunnethMap ℓ (X := X) j
      ((boundedConstructibleLowerStar ℓ g).obj N) B) := by
  unfold openKunnethMap at h ⊢
  rw [Adjunction.kunnethNatTrans_app] at h ⊢
  refine (Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism _ _
    inferInstance _ ?_).mpr (isIso_leftProjectionMorphism_prodMap_lowerStar ℓ g j N B
      ((Adjunction.isIso_homEquiv_δ_tensorHom_iff_isIso_leftProjectionMorphism _ _
        inferInstance _ ?_).mp h))
  · exact isIso_homEquiv_openKunnethSecondFactor ℓ j B
  · exact isIso_homEquiv_openKunnethSecondFactor ℓ j B

/-- **The ordinary Künneth map and closed pushforward in the first factor**: for a closed
immersion `g : Z ⟶ X`, an open immersion `j : U ⟶ Y`, `N ∈ Dᵇc(Z)⟦ℚ̲̄_ℓ⟧` and
`B ∈ Dᵇc(U)⟦ℚ̲̄_ℓ⟧`, if `κ_Z(N, B)` is an isomorphism, so is `κ_X(Rg_* N, B)`
(`isIso_openKunnethMap_lowerStar_of_isProper`). -/
theorem isIso_openKunnethMap_lowerStar_of_isClosedImmersion {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : Z ⟶ X) [IsClosedImmersion g.left] (j : U ⟶ Y) [IsOpenImmersion j.left]
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (openKunnethMap ℓ (X := Z) j N B)) :
    IsIso (openKunnethMap ℓ (X := X) j
      ((boundedConstructibleLowerStar ℓ g).obj N) B) :=
  isIso_openKunnethMap_lowerStar_of_isProper ℓ g j N B h

end AlgebraicGeometry.ProEtale.CondensedRing
