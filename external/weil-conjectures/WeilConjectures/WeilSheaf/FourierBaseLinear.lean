/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisseComm
public import WeilConjectures.WeilSheaf.FourierInversion.KernelComposition

/-!
# The Fourier–Deligne transform is linear over the base

For a lisse Weil sheaf `N` on the base `Spec k₀`, with pullbacks `p^* N` to the affine line and
`p'^* N` to the dual line, the Fourier–Deligne transform of Weil complexes satisfies

`FT_ψ(K ⊗ p^* N) ≅ FT_ψ(K) ⊗ p'^* N`

naturally in `K` (blueprint `proposition-base-change-fourier-inversion--2`;
`AlgebraicGeometry.nonempty_iso_tensorLisse_upperStar_comp_fourierTransform`). On the Fourier
square `p ∘ pr₁ = p' ∘ pr₂`, so `pr₁^*(K ⊗ p^* N) ≅ pr₁^* K ⊗ pr₂^* p'^* N`; tensoring with the
kernel commutes with tensoring with `pr₂^* p'^* N`, and the projection formula for `pr₂` moves
`p'^* N` out of the compact-support direct image. The case of the Tate twists `N = ℚ̄_ℓ(m)` is
`AlgebraicGeometry.nonempty_iso_fourierTransform_tateTwist`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

set_option linter.unusedSimpArgs false in
omit [Finite k₀] in
/-- The structure morphism of the affine line lies over `Spec k₀`, which lies over itself through
`Spec` of the identity. -/
instance affineLine.isOver_over :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by simp [specOverSpec_over, Algebra.algebraMap_self]⟩

set_option hygiene false in
/-- The structure morphism `p : 𝔸¹ ⟶ Spec k₀`. -/
local notation "p" => affineLine k₀ ↘ Spec (CommRingCat.of k₀)

set_option hygiene false in
/-- The pullback `p^* N` of the lisse Weil sheaf `N` on the base. -/
local notation "P" => (WeilSheaf.upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj N

/-- **The Fourier–Deligne transform is linear over the base** (blueprint
`proposition-base-change-fourier-inversion--2`): for a lisse Weil sheaf `N` on `Spec k₀`, pulled
back to the affine line along `p : 𝔸¹ ⟶ Spec k₀` (on both sides, the line and its dual being the
same scheme),

`FT_ψ(K ⊗ p^* N) ≅ FT_ψ(K) ⊗ p^* N`

naturally in the Weil complex `K`. -/
theorem nonempty_iso_tensorLisse_upperStar_comp_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (N : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (hN : N.IsLisse) :
    Nonempty (WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj N)
        (hN.upperStar _) ⋙ fourierTransform ψ ≅
      fourierTransform ψ ⋙ WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj N)
        (hN.upperStar _)) := by
  have hP : WeilSheaf.IsLisse P := hN.upperStar _
  -- `p ∘ pr₁ = p ∘ pr₂` on the Fourier square
  have hc : affinePlane.fst k₀ ≫ p = affinePlane.snd k₀ ≫ p := pullback.condition
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj (affinePlane.fst k₀) p
    (affinePlane.snd k₀ ≫ p) hc N
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj (affinePlane.snd k₀) p
    (affinePlane.snd k₀ ≫ p) rfl N
  have hQ : ((WeilSheaf.upperStar (affinePlane.snd k₀)).obj P).IsLisse := hP.upperStar _
  obtain ⟨eA⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar (affinePlane.fst k₀) P hP
  have hP₁ : ((WeilSheaf.upperStar (affinePlane.fst k₀)).obj P).IsLisse := hP.upperStar _
  have hN₂ : ((WeilSheaf.upperStar (affinePlane.snd k₀ ≫ p)).obj N).IsLisse := hN.upperStar _
  obtain ⟨eQ₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso e₁ hP₁ hN₂
  obtain ⟨eQ₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso e₂ hQ hN₂
  have eQ : WeilComplex.tensorLisse _ hP₁ ≅ WeilComplex.tensorLisse _ hQ := eQ₁ ≪≫ eQ₂.symm
  obtain ⟨eC⟩ := WeilComplex.nonempty_iso_tensorLisse_comm
    ((WeilSheaf.upperStar (affinePlane.snd k₀)).obj P) (fourierKernel (l := l) ψ) hQ
    (isLisse_fourierKernel ψ)
  obtain ⟨eP⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse (k₀ := k₀)
    (affinePlane.snd k₀) P hP
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let Tk := WeilComplex.tensorLisse (fourierKernel (l := l) ψ) (isLisse_fourierKernel ψ)
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let S₁ := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)
  let TP := WeilComplex.tensorLisse P hP
  let TQ := WeilComplex.tensorLisse ((WeilSheaf.upperStar (affinePlane.snd k₀)).obj P) hQ
  have e₀ : TP ⋙ fourierTransform ψ ≅ TP ⋙ A ⋙ Tk ⋙ C ⋙ S₁ := Iso.refl _
  have e₀' : fourierTransform ψ ⋙ TP ≅ A ⋙ Tk ⋙ C ⋙ S₁ ⋙ TP := Iso.refl _
  exact ⟨e₀ ≪≫ (Functor.associator TP A _).symm ≪≫
    Functor.isoWhiskerRight eA (Tk ⋙ C ⋙ S₁) ≪≫ Functor.associator A _ _ ≪≫
    Functor.isoWhiskerLeft A
      (Functor.isoWhiskerRight eQ (Tk ⋙ C ⋙ S₁) ≪≫ (Functor.associator TQ Tk _).symm ≪≫
        Functor.isoWhiskerRight eC (C ⋙ S₁) ≪≫ Functor.associator Tk TQ _ ≪≫
        Functor.isoWhiskerLeft Tk ((Functor.associator TQ C S₁).symm ≪≫
          Functor.isoWhiskerRight eP.symm S₁ ≪≫ Functor.associator C TP S₁ ≪≫
          Functor.isoWhiskerLeft C (TP.commShiftIso (1 : ℤ)).symm)) ≪≫
    e₀'.symm⟩

end AlgebraicGeometry
