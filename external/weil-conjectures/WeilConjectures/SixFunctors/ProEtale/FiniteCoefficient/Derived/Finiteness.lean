/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# Finite-level bounded constructibility of compactly supported direct images, pro-étale

At a finite coefficient stage `Λ` (in the blueprint `A_{E,n} = 𝒪_E/ϖⁿ`) whose exponent is
invertible on the base field, the compactly supported direct image on the pro-étale site
preserves bounded constructibility (of étale origin), and shifts the cohomological interval
`[a, b]` of a complex to `[a, b + 2e]` when the geometric fibres have dimension at most `e`.
This is deduced from the étale finiteness theorems through the comparison
`Rf_!^{proét} ∘ ν^* ≅ ν^* ∘ Rf_!^{ét}`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerShriek` and
  `AlgebraicGeometry.ProEtale.constructibleIn_rightDerivedLowerShriek`
  (`theorem-results-from-etale-theory--3`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

omit [Finite Λ] in
/-- For a bounded constructible pro-étale complex `K`, there is a bounded constructible étale
complex `K'` with `ν_X^* K' ≅ K` and `Rf_!^{proét} K ≅ ν_Y^* Rf_!^{ét} K'`, by the
compact-support comparison `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`. -/
lemma exists_rightDerivedLowerShriek_obj_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    ∃ K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K' ∧
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ≅ K) ∧
      Nonempty ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ≅
        D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K')) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  let L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨K', hK'.1.1⟩
  exact ⟨K', hK', ⟨e⟩, ⟨(ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).mapIso
    e.symm ≪≫ (rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} Λ) f).app L⟩⟩

/-- Blueprint `theorem-results-from-etale-theory--3`: Finite-level bounded
constructibility for proper support (bounded constructibility).

Let `f : X ⟶ Y` be a separated finite-type morphism (here: one admitting a compactification)
between finite-type schemes over a field `k`, and let `Λ` be a finite ring whose exponent is
invertible in `k` (in the blueprint `Λ = A_{E,n}`). Then the compactly supported direct image on
the pro-étale site restricts to `Dᵇc_proét(X, Λ) ⥤ Dᵇc_proét(Y, Λ)`. It is triangulated, being
the restriction of a triangulated functor to triangulated subcategories.

The proof transports the étale statement
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` along the comparison
`Rf_!^{proét} ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}`. -/
theorem boundedConstructible_rightDerivedLowerShriek [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  obtain ⟨K', hK', -, ⟨e⟩⟩ := exists_rightDerivedLowerShriek_obj_iso Λ f K hK
  have := HasInvertibleExponent.of_hom (Λ := Λ) aX
  exact ObjectProperty.prop_of_iso _ e.symm
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      (Etale.boundedConstructible_rightDerivedLowerShriek Λ f aX aY hf K' hK'))

/-- Blueprint `theorem-results-from-etale-theory--3`: Finite-level bounded
constructibility for proper support (amplitude).

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerShriek`,
if every geometric fibre of `f` has dimension at most `e`, then the compactly supported direct
image sends `D_c^{[a, b]}(X, Λ)` into `D_c^{[a, b + 2e]}(Y, Λ)`; the bounds only depend on
`a`, `b` and `e`, not on the compactification, nor on the finite coefficient ring.

The lower bound holds because `Rf_! = Rg_* ∘ Di_!` with `i_!` exact and `Rg_*` left t-exact; the
upper bound is the dévissage `AlgebraicGeometry.Etale.isLE_rightDerivedLowerShriek_obj` of the
sheaf case `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor`
(`theorem-results-from-etale-theory`) on the étale site, transported along the comparison. -/
theorem constructibleIn_rightDerivedLowerShriek [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * e)
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) := by
  refine ⟨boundedConstructible_rightDerivedLowerShriek Λ f aX aY hf K hK.1, ?_, ?_⟩
  · -- the lower bound: `Di_!` is exact and `Rg_*` is left t-exact
    have : K.IsGE a := hK.2.1
    have : (D(((HasCompactification.compactification f).i)_!open[ModuleCat.{u + 1} Λ]).obj
        K).IsGE a := Functor.isGE_mapDerivedCategory_obj _ K a
    exact Functor.isGE_rightDerivedFunctor_obj _ _ a
  · -- the upper bound, transported from the étale site
    have := HasInvertibleExponent.of_hom (Λ := Λ) aY
    obtain ⟨K', hK', ⟨eK⟩, ⟨e'⟩⟩ := exists_rightDerivedLowerShriek_obj_iso Λ f K hK.1
    have hK'ab : _root_.DerivedCategory.homologyConcentratedIn a b K' :=
      Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
        ν^*(X)[ModuleCat.{u + 1} Λ] (ObjectProperty.prop_of_iso _ eK.symm hK.2)
    obtain ⟨hK'a, hK'b⟩ := hK'ab
    let a' := min a (b + 1)
    have : K'.IsGE a' :=
      _root_.DerivedCategory.TStructure.t.isGE_of_ge K' a' a (min_le_left _ _)
    have : K'.IsLE (a' + ↑(b + 1 - a').toNat - 1) :=
      _root_.DerivedCategory.TStructure.t.isLE_of_le K' b _ (by lia)
    have h (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (hF : IsConstructibleSheaf F) :
        _root_.DerivedCategory.TStructure.t.IsLE
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) (2 * e) :=
      (_root_.DerivedCategory.isLE_iff _ _).2 fun i hi ↦
        Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor Λ f aX aY hf e he F i hi
    have h' := Etale.isLE_rightDerivedLowerShriek_obj Λ f (2 * e) h (b + 1 - a').toNat a' K'
      inferInstance this hK'.2
    have hnat : ((b + 1 - a').toNat : ℤ) = b + 1 - a' :=
      Int.toNat_of_nonneg (by have := min_le_right a (b + 1); lia)
    have : ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K').IsLE
        (b + 2 * e) :=
      _root_.DerivedCategory.TStructure.t.isLE_of_le _ (a' + ↑(b + 1 - a').toNat - 1 + 2 * e)
        _ (by lia)
    have := Functor.isLE_mapDerivedCategory_obj (ν^*(Y)[ModuleCat.{u + 1} Λ])
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K') (b + 2 * e)
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso e'.symm _

end ProEtale

end AlgebraicGeometry
