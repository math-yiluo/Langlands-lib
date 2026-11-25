/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomTransport
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison

/-!
# Iterated internal homs out of a lisse sheaf

For a lisse sheaf `a` of `ℚ̄_ℓ`-modules and arbitrary `H`, `L`, `K`, the comparison
`𝓗om(𝓗om(𝓗om(a, H), L), K) ⟶ 𝓗om(a, 𝓗om(𝓗om(H, L), K))`
(`CategoryTheory.Mod.ihomIhomComparison`) is an isomorphism
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_ihomIhomComparison`): isomorphisms are local
for the pro-étale topology, the comparison is compatible with pullback along weakly étale
morphisms (`CategoryTheory.Mod.map_ihomIhomComparison_comp_trHom`), and it is an isomorphism for
free modules of finite rank (`CategoryTheory.Mod.isIso_ihomIhomComparison_free`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

/-- The pullback along a weakly étale morphism of `ihomIhomComparison` is an isomorphism if
`ihomIhomComparison` of the pullbacks is. -/
lemma isIso_adicUpperStar_map_ihomIhomComparison {Y Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    (a H L K : AdicSheaf l Y)
    [IsIso (Mod.ihomIhomComparison ((g)^*ᵃ[l].obj a) ((g)^*ᵃ[l].obj H) ((g)^*ᵃ[l].obj L)
      ((g)^*ᵃ[l].obj K))] :
    IsIso ((g)^*ᵃ[l].map (Mod.ihomIhomComparison a H L K)) := by
  exact Mod.isIso_map_ihomIhomComparison (ρ := adicUpperStarRingHom l g)
    (c := fun M N ↦ adicUpperStarIhomComparison l g M N)
    (uncurryHom_adicUpperStarIhomComparison g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
    (Iso.refl ((g)^*ᵃ[l].obj a)) (Iso.refl ((g)^*ᵃ[l].obj H)) (Iso.refl ((g)^*ᵃ[l].obj L))
    (Iso.refl ((g)^*ᵃ[l].obj K))

/-- **Iterated internal homs out of a lisse sheaf.** For `a` lisse, the comparison
`𝓗om(𝓗om(𝓗om(a, H), L), K) ⟶ 𝓗om(a, 𝓗om(𝓗om(H, L), K))` is an isomorphism. -/
theorem IsAdicLisseSheaf.isIso_ihomIhomComparison {Y : Scheme.{u}} {a : AdicSheaf l Y}
    (ha : IsAdicLisseSheaf a) (H L K : AdicSheaf l Y) :
    IsIso (Mod.ihomIhomComparison a H L K) := by
  obtain ⟨R, hR, hRM⟩ := ha
  obtain ⟨κ, V, v, rfl⟩ := R.exists_eq_ofArrows
  have hv (k : κ) : WeaklyEtale (v k) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk k)
  refine AdicSheaf.isIso_of_isIso_upperStar v hR _ fun k ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := hRM (v k) (.mk k)
  have : IsIso (Mod.ihomIhomComparison ((v k)^*ᵃ[l].obj a) ((v k)^*ᵃ[l].obj H)
      ((v k)^*ᵃ[l].obj L) ((v k)^*ᵃ[l].obj K)) :=
    Mod.isIso_ihomIhomComparison_of_iso _ _ _ e
  exact isIso_adicUpperStar_map_ihomIhomComparison (v k) a H L K

end AlgebraicGeometry.ProEtale
