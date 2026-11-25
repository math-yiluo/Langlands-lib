/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.KernelComposition
public import WeilConjectures.WeilSheaf.FourierInversion.Composite

/-!
# The fibres of the Fourier–Deligne transform are fibre integrals

Let `g : T ⟶ 𝔸¹` be a point of the dual affine line with values in a `k₀`-scheme `T` (for
instance `T = Spec 𝔽_{qⁿ}`), and let `V_T = 𝔸² ×_{pr₂, 𝔸¹, g} T` be the fibre of the second
projection over it, with projections `g' : V_T ⟶ 𝔸²` and `π' : V_T ⟶ T`. The pullback of the
Fourier–Deligne transform to `T` is the compactly supported cohomology of the fibre
(blueprint `proposition-base-change-fourier-inversion--3`):

`g^* FT_ψ(K) ≅ Rπ'₀!(K|_{V_T} ⊗ ℒ_ψ(⟨x, g⟩))[1]`,

naturally in the Weil complex `K`, where `K|_{V_T}` is the pullback along `g' ≫ pr₁` and
`⟨x, g⟩ = g'^*(x ξ)` is the pairing with the point
(`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_upperStar`). It is compact-support base
change along `g`, together with the restriction of the kernel `μ^* ℒ_ψ` along `g'`, which is the
Artin–Schreier sheaf of the base-changed function.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The fibres of the Fourier transform are fibre integrals** (blueprint
`proposition-base-change-fourier-inversion--3`). For a point `g : T ⟶ 𝔸¹` of the dual line and the
fibre `V_T` of `pr₂ : 𝔸² ⟶ 𝔸¹` over it (a cartesian square `g' : V_T ⟶ 𝔸²`,
`π' : V_T ⟶ T`),

`g^* FT_ψ(K) ≅ Rπ'₀!((g' ≫ pr₁)^* K ⊗ ℒ_ψ(g'^*(x ξ)))[1]`

naturally in the Weil complex `K`: compact-support base change along `g`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`), the compatibility
of pullback with the tensor product by a lisse sheaf, and `g'^* ℒ_ψ(x ξ) ≅ ℒ_ψ(g'^*(x ξ))`. -/
theorem nonempty_iso_fourierTransform_comp_upperStar (ψ : AddChar k₀ (PadicAlgCl l))
    {T V : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k₀))]
    (g : T ⟶ affineLine k₀) (g' : V ⟶ affinePlane k₀) (π' : V ⟶ T)
    (sq : IsPullback g' π' (affinePlane.snd k₀) g)
    [g.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
    [π'.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated π'] [LocallyOfFiniteType π'] [QuasiCompact π']
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (fourierTransform (l := l) ψ ⋙ WeilComplex.upperStar g ≅
      WeilComplex.upperStar (g' ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ (g'.appTop
          ((affinePlane.fst k₀).appTop (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit) *
            (affinePlane.snd k₀).appTop
              (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit))))
          (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l π' ⋙ shiftFunctor _ (1 : ℤ)) := by
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  obtain ⟨BC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affinePlane.snd k₀) g π' g' sq
  obtain ⟨TL⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar g'
    (fourierKernel (l := l) ψ) (isLisse_fourierKernel ψ)
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  obtain ⟨eG⟩ := nonempty_iso_upperStar_artinSchreierOf g' ψ m
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar g').mapIso eF' ≪≫ eG) ((isLisse_fourierKernel ψ).upperStar _)
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eA⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) g'
    (affinePlane.fst k₀)
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let Tk := WeilComplex.tensorLisse (fourierKernel (l := l) ψ) (isLisse_fourierKernel ψ)
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let S₁ := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)
  let G := WeilComplex.upperStar (k₀ := k₀) (l := l) g
  let G' := WeilComplex.upperStar (k₀ := k₀) (l := l) g'
  let C' := WeilComplex.derivedLowerShriek k₀ l π'
  let S₁' := shiftFunctor (WeilComplex k₀ l T) (1 : ℤ)
  have e₀ : fourierTransform (l := l) ψ ⋙ G ≅ A ⋙ Tk ⋙ C ⋙ S₁ ⋙ G := Iso.refl _
  exact ⟨e₀ ≪≫
    Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tk (Functor.isoWhiskerLeft C
      (G.commShiftIso (1 : ℤ)))) ≪≫
    Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tk
      ((Functor.associator C G S₁').symm ≪≫ Functor.isoWhiskerRight BC S₁' ≪≫
        Functor.associator G' C' S₁')) ≪≫
    Functor.isoWhiskerLeft A ((Functor.associator Tk G' (C' ⋙ S₁')).symm ≪≫
      Functor.isoWhiskerRight TL (C' ⋙ S₁') ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator A G' _).symm ≪≫
    Functor.isoWhiskerRight eA.symm _ ≪≫
    Functor.isoWhiskerLeft (WeilComplex.upperStar (g' ≫ affinePlane.fst k₀))
      (Functor.isoWhiskerRight eT (C' ⋙ S₁'))⟩

end AlgebraicGeometry
