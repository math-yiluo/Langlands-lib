/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFiberFiniteEtale
public import WeilConjectures.CategoryTheory.TrivialCovering
public import WeilConjectures.SixFunctors.ProEtale.Adic.SplitCovering
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Weil sheaves on finite étale schemes

Let `Z₀` be a finite reduced scheme over the finite field `k₀`. Its geometric fibre is a finite
disjoint union of copies of `Spec k̄`
(`AlgebraicGeometry.exists_isIso_sigmaDesc_geometricFiber_of_isFinite`), hence:

- every Weil sheaf on `Z₀` is lisse;
- for a base change `π : Z₀ ×_{k₀} Y₀ ⟶ Y₀` of `Z₀ ⟶ Spec k₀`, which becomes a trivial covering
  after base change to `k̄`, the pushforward along `π` of a lisse Weil sheaf is lisse.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isLisse_of_isFinite_of_isReduced`.
- `AlgebraicGeometry.WeilSheaf.isLisse_lowerStar_of_isPullback`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Weil sheaves on a finite reduced scheme are lisse**: the geometric fibre of a finite
reduced `k₀`-scheme is a finite disjoint union of copies of `Spec k̄`, on which every
constructible sheaf is lisse. -/
theorem isLisse_of_isFinite_of_isReduced {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z] (E : WeilSheaf k₀ l Z) :
    E.IsLisse := by
  obtain ⟨n, t, -, hiso⟩ :=
    exists_isIso_sigmaDesc_geometricFiber_of_isFinite (Z ↘ Spec (CommRingCat.of k₀))
  exact ProEtale.IsAdicConstructibleSheaf.isAdicLisseSheaf_of_isIso_sigmaDesc t E.property

/-- **Pushforward along a finite étale base change preserves lisse sheaves.** Let `Z₀` be a
finite reduced `k₀`-scheme and `π : X₀ ⟶ Y₀` the base change of `Z₀ ⟶ Spec k₀` along
`Y₀ ⟶ Spec k₀`. After base change to `k̄`, `π` becomes the projection `∐ Ȳ ⟶ Ȳ` from a finite
disjoint union of copies of `Ȳ`, the base change of `∐ Spec k̄ ≅ Z̄ ⟶ Spec k̄`, so the pushforward
along `π` of a lisse Weil sheaf is a finite direct sum of lisse sheaves. -/
theorem isLisse_lowerStar_of_isPullback {Z X Y : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [IsFinite (Z ↘ Spec (CommRingCat.of k₀))] [IsReduced Z]
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    {q : X ⟶ Z} {π : X ⟶ Y} [π.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact π]
    [QuasiSeparated π] [LocallyOfFiniteType π]
    (hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀)) (Y ↘ Spec (CommRingCat.of k₀)))
    (G : WeilSheaf k₀ l X) (hG : G.IsLisse) : ((WeilSheaf.lowerStar π).obj G).IsLisse := by
  obtain ⟨n, t, ht, hiso⟩ :=
    exists_isIso_sigmaDesc_geometricFiber_of_isFinite (Z ↘ Spec (CommRingCat.of k₀))
  have hπ : π ≫ Y ↘ Spec (CommRingCat.of k₀) = X ↘ Spec (CommRingCat.of k₀) :=
    comp_over π _
  have hq : q ≫ Z ↘ Spec (CommRingCat.of k₀) = X ↘ Spec (CommRingCat.of k₀) := hP.w.trans hπ
  have : IsFinite π := MorphismProperty.of_isPullback hP inferInstance
  have hP' : IsPullback (Scheme.Hom.geometricFiberMap q hq) (Scheme.Hom.geometricFiberMap π hπ)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure := by
    refine IsPullback.of_right (h₁₂ := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (h₂₂ := (Scheme.specAlgebraicClosure k₀).hom) (v₁₃ := Z ↘ Spec (CommRingCat.of k₀))
      ?_ (by simp) (IsPullback.of_hasPullback _ _)
    rw [Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Scheme.Hom.geometricFiber_condition]
    exact (Scheme.Hom.isPullback_geometricFiberMap π hπ).flip.paste_horiz hP
  have := FinitaryPreExtensive.isIso_sigmaDesc_isPullback_lift hP' t ht
  exact ProEtale.IsAdicLisseSheaf.adicLowerStar_of_isIso_sigmaDesc
    (fun k ↦ hP'.lift ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫ t k)
      (𝟙 _) (by simp [ht]))
    (Scheme.Hom.geometricFiberMap π hπ) (fun k ↦ hP'.lift_snd _ _ _) hG

end AlgebraicGeometry.WeilSheaf
