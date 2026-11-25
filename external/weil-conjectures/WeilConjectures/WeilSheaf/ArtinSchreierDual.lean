/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierMul

/-!
# The dual of an Artin–Schreier sheaf

The dual of the Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line is the Artin–Schreier
sheaf `ℒ_{ψ⁻¹(a x)}` of the inverse character
(`AlgebraicGeometry.nonempty_iso_dual_artinSchreier`): this is the clause
`(ℒ_{ψ,f})^{-1} ≅ ℒ_{ψ,-f} ≅ ℒ_{ψ^{-1},f}` of the isotypic decomposition of the Artin–Schreier
pushforward, for `f = a x`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The dual of an Artin–Schreier sheaf.** The dual of the linear Artin–Schreier sheaf
`ℒ_{ψ(a x)}` on `𝔸¹_{k₀}` is the Artin–Schreier sheaf `ℒ_{ψ⁻¹(a x)}`: this is the clause
`(ℒ_{ψ,f})^{-1} ≅ ℒ_{ψ,-f} ≅ ℒ_{ψ^{-1},f}` for `f = a x`, the inverse of the rank-one sheaf
`ℒ_{ψ,f}` being its dual. (blueprint: `lemma-artin-schreier-character-sheaf`, subsection
`lemma-artin-schreier-character-sheaf` of `chap-The-Fourier-transform`)

On the Artin–Schreier covering of `(x, x)`, a `k₀²`-torsor, `ℒ_{ψ(a x)}` and `ℒ_{ψ⁻¹(a x)}` are
isotypic components of `π_* ℚ̄_ℓ` for inverse characters, so that
`AlgebraicGeometry.nonempty_iso_ihom_adicConstant_artinSchreierPlane` applies. -/
theorem nonempty_iso_dual_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty ((artinSchreier ψ a).dual (isLisse_artinSchreier ψ a) ≅ artinSchreier ψ⁻¹ a) := by
  set t : Γ(affineLine k₀, ⊤) := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  set f : planeIndex → Γ(affineLine k₀, ⊤) := fun i ↦ ![t, t] i.down with hf
  have hg : affineLine.smul k₀ a = planeLinearFunction k₀ f (fun i ↦ ![a, 0] i.down) := by
    rw [hf, planeLinearFunction_pair, ← Category.id_comp (affineLine.smul k₀ a),
      ← affineLine.homOfSection_coord, affineLine.homOfSection_comp_smul]
    simp [t]
  obtain ⟨e₁⟩ := nonempty_iso_artinSchreier_obj ψ a hg
  obtain ⟨e₂⟩ := nonempty_iso_artinSchreier_obj ψ⁻¹ a hg
  have h (g : planeIndex → k₀) : ψ⁻¹ (∑ i, ![a, 0] i.down * g i) *
      ψ (∑ i, ![a, 0] i.down * g i) = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  obtain ⟨e⟩ := nonempty_iso_ihom_adicConstant_artinSchreierPlane f ψ⁻¹ ψ
    (fun i ↦ ![a, 0] i.down) (fun i ↦ ![a, 0] i.down) h
  refine ⟨ObjectProperty.isoMk _ ?_⟩
  rw [WeilSheaf.dual_obj_eq_ihom]
  exact ProEtaleWeilSheaf.ihomMapIsoLeft e₁.symm _ ≪≫ e.symm ≪≫ e₂.symm

end AlgebraicGeometry
