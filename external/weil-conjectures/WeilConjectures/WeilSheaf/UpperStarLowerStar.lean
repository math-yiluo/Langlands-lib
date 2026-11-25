/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The counit `j^* j_* ≅ 𝟭` of Weil sheaves along an open immersion

Along an open immersion `j`, the counit of the adjunction `j^* ⊣ j_*` of pro-étale Weil sheaves
and of Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`,
`AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction`) is invertible, so `j^* j_* F ≅ F`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompUpperStarIso` and
  `AlgebraicGeometry.WeilSheaf.lowerStarCompUpperStarIso`: the counit `j^* j_* ≅ 𝟭`.
- `AlgebraicGeometry.WeilSheaf.upperStarDirectImageIso`: `j^* j_* F ≅ F`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion φ]

variable (k₀ l) in
/-- Along an open immersion `j`, the counit `j^* j_* ⟶ 𝟭` of pro-étale Weil sheaves is an
isomorphism. -/
noncomputable def ProEtaleWeilSheaf.lowerStarCompUpperStarIso :
    ProEtaleWeilSheaf.lowerStar k₀ l φ ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ ≅ 𝟭 _ :=
  asIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The restriction of the direct image to the open**: for an open immersion `j : U ↪ X`, the
counit `j^* j_* ⟶ 𝟭` of Weil sheaves is an isomorphism. -/
noncomputable def lowerStarCompUpperStarIso :
    WeilSheaf.lowerStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.upperStar φ ≅ 𝟭 _ :=
  asIso (upperStarLowerStarAdjunction φ).counit

/-- **The restriction of the direct image to the open**: `j^* j_* F ≅ F` for an open immersion
`j : U ↪ X` and a Weil sheaf `F` on `U`. -/
noncomputable def upperStarDirectImageIso (F : WeilSheaf k₀ l X) :
    (WeilSheaf.upperStar φ).obj ((WeilSheaf.lowerStar φ).obj F) ≅ F :=
  (lowerStarCompUpperStarIso φ).app F

end WeilSheaf

end AlgebraicGeometry
