/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# The zeroth higher direct image of a Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes as in `WeilSheaf.lowerStar`, the zeroth higher
direct image `R⁰φ_* F = 𝓗⁰(Rφ_* F)` of a Weil sheaf `F` is the ordinary direct image `φ_* F`
(`AlgebraicGeometry.WeilSheaf.higherLowerStarZeroIso`): the pushforward of pro-étale Weil
sheaves is left exact, and `𝓗⁰` of the total right derived functor of a left exact functor on an
object placed in degree `0` is the functor itself
(`CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso`).

Along an open immersion `j : U ⟶ C` into a curve this is the description of the middle extension
`j_* F = 𝓗⁰(Rj_* F)` of a lisse sheaf `F`
(`AlgebraicGeometry.WeilSheaf.higherDirectImageZeroIso`, blueprint `definition-middle-extension`).
This middle extension is constructible, for Weil sheaves and for lisse `ℓ`-adic sheaves on the
geometric curve (`AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_directImage`,
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isAdicConstructibleSheaf_lowerStar_of_isOpenImmersion`,
blueprint `theorem-purity-real-sheaves-curves` (5)).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- **`R⁰φ_* = φ_*`.** The zeroth higher direct image `𝓗⁰(Rφ_* F)` of a Weil sheaf `F` is the
ordinary direct image `φ_* F`, naturally in `F`: the pushforward of pro-étale Weil sheaves is
left exact, so `𝓗⁰` of its total right derived functor on `F` placed in degree `0` is `φ_* F`. -/
noncomputable def higherLowerStarZeroIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    higherLowerStar (k₀ := k₀) (l := l) φ 0 ≅ lowerStar φ :=
  let e := Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
    (ProEtaleWeilSheaf.lowerStar k₀ l φ)
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (e.app F.obj))
    fun α ↦ ObjectProperty.hom_ext _ (e.hom.naturality α.hom)

/-- Blueprint `definition-middle-extension`: the middle extension on a curve.

For a quasi-compact open immersion `j : U ⟶ C` (for instance a dense open of a smooth curve
`C₀`) and a Weil sheaf `F` on `U₀`, for instance a lisse one, the sheaf-theoretic middle
extension `j_* F`, the ordinary direct image `WeilSheaf.directImage j`, is the zeroth cohomology
sheaf `𝓗⁰(Rj_* F)` of the derived direct image: `R⁰j_* F ≅ j_* F`, naturally in `F`. It is a Weil
sheaf, that is constructible, since `Rj_*` preserves Weil complexes
(`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar`); its higher cohomology
sheaves `Rⁱj_* F`, `i > 0`, are the `WeilSheaf.higherDirectImage j i`. -/
noncomputable def higherDirectImageZeroIso {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))] :
    higherDirectImage (k₀ := k₀) (l := l) j 0 ≅ directImage j :=
  higherLowerStarZeroIso j

/-- Blueprint `theorem-purity-real-sheaves-curves` (5), for Weil `ℚ̄_ℓ`-sheaves: the middle
extension `j_* F` of a lisse (indeed of any) Weil sheaf `F` along a quasi-compact open immersion
`j` into a `k₀`-scheme of finite type is constructible. This is the finiteness theorem
(`AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_lowerStar`), which is built into
`WeilSheaf.directImage`. -/
theorem isAdicConstructibleSheaf_directImage {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) :
    ProEtale.IsAdicConstructibleSheaf ((directImage j).obj F).obj.carrier :=
  ((directImage j).obj F).property

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.ProEtale

/-- Blueprint `theorem-purity-real-sheaves-curves` (5), for lisse `ℚ̄_ℓ`-sheaves on a geometric
curve: over an algebraically closed field `K` of characteristic `≠ ℓ`, the middle extension
`j_* F` of a lisse `ℓ`-adic sheaf `F` along a quasi-compact open immersion `j : U ⟶ C` into a
scheme `C` locally of finite type over `K` is constructible, by the finiteness theorem
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.lowerStar`). -/
theorem IsAdicLisseSheaf.isAdicConstructibleSheaf_lowerStar_of_isOpenImmersion {l : ℕ}
    [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {U C : Scheme.{u}}
    (s : C ⟶ Spec (.of K)) [LocallyOfFiniteType s] (hK : ringChar K ≠ l) (j : U ⟶ C)
    [IsOpenImmersion j] [QuasiCompact j] {F : AdicSheaf l U} (hF : IsAdicLisseSheaf F) :
    IsAdicConstructibleSheaf ((j)_*ᵃ[l].obj F) :=
  hF.isAdicConstructibleSheaf.lowerStar s j hK

end AlgebraicGeometry.ProEtale
