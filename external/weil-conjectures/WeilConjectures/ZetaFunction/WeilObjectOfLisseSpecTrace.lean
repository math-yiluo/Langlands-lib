/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.PointTraceComparison
public import WeilConjectures.WeilSheaf.TraceFunctionCongr
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseCohomology
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseLocal

/-!
# Traces of the cohomology sheaves of `Ra_! H` on `Spec k₀` in the two models

Let `H` be a lisse `ℓ`-adic sheaf on `X₀` and `Mʲ = Hʲ(Ra_! H)` the homology sheaves of its
compactly supported direct image, module objects on `Spec k₀`
(`AlgebraicGeometry.WeilComplex.lowerShriekHomologyOfLisse`). The trace of the `(n + 1)`-st
Frobenius on the stalk at `Spec k̄` of `Mʲ` with the identity Weil structure is, through
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the trace of `F^{n+1}` on the global sections of the Weil sheaf on
`Spec k₀` pulled back from `Mʲ`
(`WeilComplex.endTensorUnitRingEquiv_weilSheafStalkTrace_ofId_lowerShriekHomologyOfLisse`).

This is the case `X₀ = Spec k₀` of the comparison of the local traces of the Weil object of a
lisse sheaf with its trace function
(`WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse`),
combined with the Grothendieck–Lefschetz formula on the point
(`AlgebraicGeometry.WeilSheaf.traceFunction_toComplex_spec_eq_trace_globalSections`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

/-- The stalk trace of a module object on `Spec k₀` with the identity Weil structure does not
depend on whether `Spec k₀` is seen as the base point `point k₀` or as the `k₀`-scheme
`overSpec (Spec k₀)`, at any geometric point equal to `Spec k̄ ⟶ Spec k₀`. -/
lemma weilSheafStalkTrace_ofId_overSpec_eq (n : ℕ)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of k₀))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (CommRingCat.of k₀))))
    (x : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (CommRingCat.of k₀))
    (hx : x ≫ ((Iso.refl (overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀)))).pow n).hom.left =
      ((geometricFrobeniusField k₀).pow n).hom ≫ x)
    (h : x = specAlgebraicClosure k₀) :
    weilSheafStalkTrace l n x hx
        (WeilSheaf.ofId l (X := overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))) M) =
      weilSheafStalkTrace l n (specAlgebraicClosure k₀) (specAlgebraicClosure_comp_pow n)
        (WeilSheaf.ofId l (X := point k₀) M) := by
  subst h
  rfl

variable [Fact (ringChar k₀ ≠ l)]

attribute [local instance] fact_ringChar_prime_of_finite

/-- **Stalk traces of `Mʲ = Hʲ(Ra_! H)` on `Spec k₀`**: through `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`,
the trace of the `(n + 1)`-st Frobenius on the stalk of `Mʲ` with the identity Weil structure is
the trace of `F^{n+1}` on the global sections of the Weil sheaf on `Spec k₀` pulled back from
`Mʲ`. -/
theorem endTensorUnitRingEquiv_weilSheafStalkTrace_ofId_lowerShriekHomologyOfLisse
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (n : ℕ) (j : ℤ) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilSheafStalkTrace l (n + 1) (specAlgebraicClosure k₀)
          (specAlgebraicClosure_comp_pow (n + 1))
          (WeilSheaf.ofId l (X := point k₀) (lowerShriekHomologyOfLisse hH j))) =
      LinearMap.trace (PadicAlgCl l) _ ((WeilSheaf.geometricFiberPullback (k₀ := k₀)
        (X := Spec (CommRingCat.of k₀))
        (isAdicLisseSheaf_lowerShriekHomologyAdicOfLisse hH j)).globalSections.frobeniusEnd ^
          (n + 1)) := by
  have : IsSeparated (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsSeparated (𝟙 _))
  have : LocallyOfFiniteType (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (𝟙 _))
  have : IsSeparated (overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))).hom :=
    inferInstanceAs (IsSeparated (𝟙 _))
  have : LocallyOfFiniteType (overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact (overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 _))
  set G := WeilSheaf.geometricFiberPullback (k₀ := k₀) (X := Spec (CommRingCat.of k₀))
    (isAdicLisseSheaf_lowerShriekHomologyAdicOfLisse hH j)
  have h1 : (WeilCoefficients.smulIso 1 G.obj.carrier).hom = 𝟙 _ :=
    (congrArg (fun c ↦ AdicSheaf.smul (ULift.up c) G.obj.carrier) Units.val_one).trans
      (AdicSheaf.smul_one _)
  have e : G.constantTwist 1 ≅ G := ObjectProperty.isoMk _ (Endofunctor.IsoAlgebra.isoMk
    (Iso.refl _) (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact (Category.comp_id _).symm.trans (congrArg (G.obj.str.hom ≫ ·) h1.symm)))
  let y : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ (n + 1)) := default
  have hy : (frobeniusFixedPointsReflOfFieldPoint
      (X := overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))) n y).1 = specAlgebraicClosure k₀ := by
    have h2 : (frobeniusFixedPointsReflOfFieldPoint
        (X := overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))) n y).1 ≫ 𝟙 _ =
        specAlgebraicClosure k₀ :=
      (frobeniusFixedPointsReflOfFieldPoint
        (X := overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))) n y).2.1
    rwa [Category.comp_id] at h2
  have h := endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse
    (X := Spec (CommRingCat.of k₀)) (isAdicLisseSheaf_lowerShriekHomologyAdicOfLisse hH j) 1 n y
  rw [weilStalkTraceAlternatingSum_weilObjectOfLisse_one (X := Spec (CommRingCat.of k₀)),
    weilSheafStalkTrace_congr _ _ _ _ (WeilSheaf.ofIdMapIso l
      ((adicSheafEquivCondensedMod l (Spec (CommRingCat.of k₀))).counitIso.app
        (lowerShriekHomologyOfLisse hH j))),
    weilSheafStalkTrace_ofId_overSpec_eq _ _ _ _ hy,
    WeilComplex.traceFunction_congr (WeilSheaf.toComplex.mapIso e),
    WeilSheaf.traceFunction_toComplex_spec_eq_trace_globalSections _ _ (Nat.le_add_left 1 n)] at h
  exact h

end AlgebraicGeometry.WeilComplex
