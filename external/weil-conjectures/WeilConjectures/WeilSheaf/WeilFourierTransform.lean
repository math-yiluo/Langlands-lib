/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs

/-!
# Fourier transforms on constructible Weil complexes

Source: blueprint main-20261015, `sec-fourier-transform/sk-def-ft/def-fd-transform.md`
(blueprint: sec-Fourier-inversion).

The ordinary étale transform does not have Weil complexes as its domain. This interface
uses the existing Weil operations to give the same formula for a pairing of any rank.
The kernel `𝒦_ψ = b^* ℒ_ψ` is the existing Artin--Schreier sheaf of a function,
`AlgebraicGeometry.artinSchreierOf`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The Fourier--Deligne transform `p₂! (p₁* K ⊗ Kψ)[r]` on Weil complexes, where the
kernel `Kψ = b^* ℒ_ψ` is the Artin--Schreier sheaf `artinSchreierOf ψ b` of the function `b`.
The product's structure map and its projection-over instances express the same finite-field
model on all three schemes. For a vector bundle and its dual, `b` is their evaluation pairing
and `r` their rank. The definition also makes sense for an arbitrary pairing and shift.
Source: blueprint main-20261015, `sk-def-ft/def-fd-transform.md`
(blueprint: sec-Fourier-inversion). -/
noncomputable def WeilComplex.fourierTransformOfPairing
    {S V V' : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [V'.Over (Spec (CommRingCat.of k₀))] (π : V ⟶ S) (π' : V' ⟶ S)
    [(pullback π π').Over (Spec (CommRingCat.of k₀))]
    [(pullback.fst π π').IsOver (Spec (CommRingCat.of k₀))]
    [(pullback.snd π π').IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (pullback π π' ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (pullback.snd π π')] [LocallyOfFiniteType (pullback.snd π π')]
    [QuasiCompact (pullback.snd π π')]
    [LocallyOfFiniteType (V' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (V' ↘ Spec (CommRingCat.of k₀))]
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    WeilComplex k₀ l V ⥤ WeilComplex k₀ l V' :=
  WeilComplex.upperStar (pullback.fst π π') ⋙
    WeilComplex.tensorLisse (artinSchreierOf ψ b) (isLisse_artinSchreierOf ψ b) ⋙
    WeilComplex.derivedLowerShriek k₀ l (pullback.snd π π') ⋙ shiftFunctor _ r

/-- The Fourier transform of affine space, using its actual standard evaluation pairing
and the shift by its rank, on constructible Weil complexes.
Source: blueprint main-20261015, `sk-def-ft/def-fd-transform.md`
(blueprint: sec-Fourier-inversion). -/
noncomputable def WeilComplex.affineFourierTransform (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) ⥤
      WeilComplex k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) :=
  let π := AffineSpace n (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)
  letI : LocallyOfFiniteType (pullback.fst π π) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  letI : LocallyOfFiniteType (pullback.snd π π) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : IsSeparated (pullback.snd π π) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : QuasiCompact (pullback.snd π π) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : (pullback.fst π π).IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨pullback.condition (f := π) (g := π)⟩
  letI : (pullback.snd π π).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  letI : LocallyOfFiniteType (pullback π π ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd π π ≫ π))
  WeilComplex.fourierTransformOfPairing π π ψ
    (AffineSpace.stdPairing n (Spec (CommRingCat.of k₀))) (Fintype.card n)

end AlgebraicGeometry
