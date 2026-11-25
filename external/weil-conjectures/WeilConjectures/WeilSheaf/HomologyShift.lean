/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
/-!
# Cohomology sheaves of shifted Weil complexes

The cohomology sheaves of a shifted Weil complex are those of the complex, reindexed:
`𝓗ⁿ(K[a]) ≅ 𝓗ⁿ⁺ᵃ(K)` (`AlgebraicGeometry.WeilComplex.homologySheafShiftIso`). In particular a
Weil sheaf `F` placed in degree `-a`, that is `F[a]`, has the single cohomology sheaf
`𝓗⁻ᵃ(F[a]) ≅ F`.

## Main declarations

- `AlgebraicGeometry.WeilComplex.isZero_homologySheaf_shift`: the cohomology sheaves of `K[n]`
  vanish where those of `K` do.
- `AlgebraicGeometry.WeilSheaf.homologySheafShiftToComplexIso`: for a Weil sheaf `F`, the
  cohomology sheaf `𝓗⁻ⁿ(F[n])` is `F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- The cohomology sheaves of a shifted Weil complex: `𝓗ⁿ(K[a]) ≅ 𝓗ⁿ'(K)` for `a + n = n'`,
those of the underlying complex of pro-étale Weil sheaves. -/
noncomputable def homologySheafShiftIso (K : WeilComplex k₀ l X) (a n n' : ℤ)
    (h : a + n = n') : (homologySheaf n).obj (K⟦a⟧) ≅ (homologySheaf n').obj K :=
  ObjectProperty.isoMk _ ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso a).app K) ≪≫
    ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso a n n' h).app K.obj)

/-- A shifted Weil sheaf `F[a]` has vanishing cohomology sheaves outside degree `-a`. -/
theorem isZero_homologySheaf_shift_toComplex (F : WeilSheaf k₀ l X) {a n : ℤ} (h : a + n ≠ 0) :
    IsZero ((homologySheaf n).obj ((WeilSheaf.toComplex.obj F)⟦a⟧)) :=
  (isZero_homologySheaf_singleComplex h F).of_iso (homologySheafShiftIso _ a n (a + n) rfl)

/-- The cohomology sheaf of a shifted Weil sheaf `F[a]` in degree `-a` is `F`. -/
noncomputable def homologySheafShiftToComplexIso (F : WeilSheaf k₀ l X) (a n : ℤ)
    (h : a + n = 0) : (homologySheaf n).obj ((WeilSheaf.toComplex.obj F)⟦a⟧) ≅ F :=
  homologySheafShiftIso _ a n 0 h ≪≫ homologySheafSingleComplexIso 0 F

/-- The cohomology sheaves of a shifted Weil complex vanish where those of the complex do. -/
theorem isZero_homologySheaf_shift {K : WeilComplex k₀ l X} {n a a' : ℤ} (h : n + a = a')
    (hK : IsZero ((homologySheaf a').obj K)) : IsZero ((homologySheaf a).obj (K⟦n⟧)) :=
  hK.of_iso (homologySheafShiftIso K n a a' h)

end WeilComplex

namespace WeilSheaf

/-- The cohomology sheaf `𝓗⁻ⁿ` of a Weil sheaf placed in degree `0` and shifted by `n` is the
sheaf itself. -/
noncomputable def homologySheafShiftToComplexIso (F : WeilSheaf k₀ l X) (n : ℤ) :
    (WeilComplex.homologySheaf (-n)).obj ((toComplex.obj F)⟦n⟧) ≅ F :=
  WeilComplex.homologySheafShiftIso _ n (-n) 0 (add_neg_cancel n) ≪≫
    toComplexCompHomologySheafIso.app F

/-- The cohomology sheaves of a Weil sheaf placed in degree `0` and shifted by `n` vanish outside
degree `-n`. -/
theorem isZero_homologySheaf_shift_toComplex (F : WeilSheaf k₀ l X) {n a : ℤ} (h : a ≠ -n) :
    IsZero ((WeilComplex.homologySheaf a).obj ((toComplex.obj F)⟦n⟧)) :=
  WeilComplex.isZero_homologySheaf_shift rfl
    (WeilComplex.isZero_homologySheaf_singleComplex (by omega) F)

end WeilSheaf

end AlgebraicGeometry
