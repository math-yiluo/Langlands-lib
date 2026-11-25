/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProperProjectionFormula
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor

/-!
# The compact-support projection formula for Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the projection formula `Rf₀! M ⊗ T ≅ Rf₀!(M ⊗ f^* T)` for Weil complexes, natural in `M` and `T`
(blueprint: `fix-prop-projection-formula`). The tensor product is the native derived tensor
product of pro-étale Weil sheaves restricted to Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`), and the two sides are
`AlgebraicGeometry.WeilComplex.nativeCompactProjectionLeft` and
`AlgebraicGeometry.WeilComplex.nativeCompactProjectionRight`.

Writing `f = g ∘ i` for the chosen compactification, with `i` an open immersion and `g` proper,
`Rf₀! = Rg_* ∘ i_!`, and the formula is the composite of
- the proper projection formula `Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`
  (`AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso`)
  at `A = i_! M`;
- the open projection formula `i_! M ⊗ N ≅ i_!(M ⊗ i^* N)`
  (`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_derived_tensor`);
- the composition `i^* g^* ≅ f^*` (`AlgebraicGeometry.WeilComplex.nativeProjectionPullComp`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Compactification.over

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **The compact-support projection formula for Weil complexes** (blueprint:
`fix-prop-projection-formula`, for `Λ = ℚ̄_ℓ` with Weil structures): for a separated morphism of
finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
`Rf₀! M ⊗ T ≅ Rf₀!(M ⊗ f^* T)`, naturally in the Weil complexes `M` on `X` and `T` on `Y`. -/
theorem nonempty_nativeCompactProjectionLeft_iso :
    Nonempty (nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f) := by
  let c := nativeProjectionCompactification k₀ f
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨π⟩ := nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso (k₀ := k₀) (l := l) c.g
  obtain ⟨s, d, -, -⟩ := ProEtaleWeilSheaf.native_open_derived_tensor k₀ l c.i
  let ιX := (objectProperty k₀ l X).ι
  let ιY := (objectProperty k₀ l Y).ι
  let Rg := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor
  let gs := ProEtaleWeilSheaf.nativeOpenPull k₀ l c.g
  let e : nativeCompactProjectionLeft k₀ l f ⋙ ιY ≅ nativeCompactProjectionRight k₀ l f ⋙ ιY :=
    Functor.isoWhiskerLeft ((extensionByZero c.i).prod (𝟭 _)) π ≪≫
      Functor.isoWhiskerLeft (ιX.prod (ιY ⋙ gs)) (Functor.isoWhiskerRight d.gamma Rg) ≪≫
      Functor.isoWhiskerRight (NatIso.prod (Iso.refl ιX)
        (Functor.isoWhiskerLeft ιY (nativeProjectionPullComp k₀ l f)))
        (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X ⋙
          ProEtaleWeilSheaf.nativeOpenExtension k₀ l c.i ⋙ Rg)
  exact ⟨((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso e⟩

end WeilComplex

end AlgebraicGeometry
