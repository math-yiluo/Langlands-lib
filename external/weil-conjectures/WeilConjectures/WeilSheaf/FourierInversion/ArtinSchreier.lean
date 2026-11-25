/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierFunctions
public import WeilConjectures.WeilSheaf.ArtinSchreierMul
public import WeilConjectures.WeilSheaf.ArtinSchreierNeg
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# Fourier inversion: Artin–Schreier sheaves of functions

Multiplicativity of the Artin–Schreier sheaves `ℒ_{ψ,a}` (blueprint
`lemma-artin-schreier-character-sheaf--2`, `lemma-artin-schreier-character-sheaf`) and their
compatibility with pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `lemma-artin-schreier-character-sheaf--2` / `lemma-artin-schreier-character-sheaf`:
`ℒ_{ψ⁻¹,a} ≅ ℒ_{ψ,-a}`. -/
theorem nonempty_iso_artinSchreierOf_inv (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    Nonempty (artinSchreierOf ψ⁻¹ a ≅ artinSchreierOf ψ (-a)) := by
  rw [artinSchreierOf_eq, artinSchreierOf_eq, artinSchreier, artinSchreier,
    WeilSheaf.image_artinSchreierIdempotent_eq ψ⁻¹, WeilSheaf.image_artinSchreierIdempotent_eq ψ]
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_upperStar_smul_image_inv ψ 1
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_obj_of_iso (affineLine.homOfSection k₀ a)
    (affineLine.smul k₀ (-1)) (affineLine.homOfSection k₀ (-a))
    (affineLine.homOfSection_comp_smul_neg_one a) e
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj
    (affineLine.homOfSection k₀ (-a)) (affineLine.smul k₀ 1) (affineLine.homOfSection k₀ (-a))
    (by rw [affineLine.smul_one, Category.comp_id])
    (@image _ _ _ _ (WeilSheaf.artinSchreierIdempotent ψ)
      (WeilSheaf.hasImage_artinSchreierIdempotent ψ))
  exact ⟨e₁ ≪≫ e₂.symm⟩

/-- Blueprint `lemma-artin-schreier-character-sheaf` (`ℒ_{ψ,0}` is the constant sheaf, the
Artin–Schreier cover of the zero function being the trivial torsor): `ℒ_{ψ,0} ≅ ℚ̄_ℓ`. -/
theorem nonempty_iso_artinSchreierOf_zero (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreierOf ψ (0 : Γ(X, ⊤)) ≅ WeilSheaf.adicConstant k₀ l X) := by
  rw [artinSchreierOf_eq, artinSchreier, WeilSheaf.image_artinSchreierIdempotent_eq]
  exact WeilSheaf.nonempty_iso_upperStar_upperStar_of_comp_artinSchreierMap _ _
    (affineLine.homOfSection k₀ (0 : Γ(X, ⊤)))
    (by rw [affineLine.smul_one, Category.comp_id])
    (by rw [affineLine.homOfSection_comp_artinSchreierMap]; simp [Fintype.card_ne_zero])
    _ (WeilSheaf.upperStarArtinSchreierMapImageIso ψ)

/-- Pullback of Artin–Schreier sheaves of functions: `φ^* ℒ_{ψ,a} ≅ ℒ_{ψ,φ^* a}`, from
`φ ≫ a = φ^* a` as morphisms to `𝔸¹` and the composition of pullbacks of Weil sheaves. -/
theorem nonempty_iso_upperStar_artinSchreierOf {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    Nonempty ((WeilSheaf.upperStar φ).obj (artinSchreierOf ψ a) ≅
      artinSchreierOf ψ (φ.appTop a)) := by
  rw [artinSchreierOf_eq, artinSchreierOf_eq]
  exact WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj φ _ _
    (affineLine.comp_homOfSection φ a) _

end AlgebraicGeometry
