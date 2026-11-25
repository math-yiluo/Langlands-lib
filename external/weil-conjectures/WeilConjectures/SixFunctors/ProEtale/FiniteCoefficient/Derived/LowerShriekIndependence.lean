/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# Independence of the compactification on objects of étale origin

For a morphism `f : X ⟶ Y` with two compactifications `c` and `d`, the pro-étale exceptional
direct images `Rf_!(c)` and `Rf_!(d)` agree on objects of étale origin `ν_X^* K₀`, `K₀` a
bounded below étale complex: transport the étale independence of the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`) along the
compact-support comparisons `Rf_!^{proét}(c) ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}(c)`. The resulting
isomorphisms satisfy the cocycle condition.

For the structure morphism `a : X ⟶ s` and a compactification `X ⟶[j] X̄ ⟶[ā] s`, this is the
comparison `RΓ_c(X, K) ≃ RΓ(X̄, j_! K)` of compactly supported cohomology with the cohomology of
the extension by zero on the compactification.

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso`: the
  comparison `Rf_!(c) ∘ ν^* ≅ Rf_!(d) ∘ ν^*` on bounded below étale complexes.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekCompactificationIso`: the comparison of the
  chosen `Rf_!` with `Rf_!(c) = Rf̄_* j_!` (blueprint
  `proposition-construction-independence-rf-shriek--7`).

## Main results

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso_trans`: the
  cocycle condition.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  [QuasiCompact f]

/-- The pro-étale exceptional direct images of two compactifications `c`, `d` of `f` agree on
objects of étale origin: `Rf_!(c) ∘ ν_X^* ≃ ν_Y^* ∘ Rf_!^{ét}(c) ≃ ν_Y^* ∘ Rf_!^{ét}(d) ≃
Rf_!(d) ∘ ν_X^*` as functors on bounded below étale complexes. -/
noncomputable def rightDerivedLowerShriekOfCompactificationOriginIso (c d : Compactification f) :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  rightDerivedLowerShriekOfCompactificationComparisonIso _ c ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c d) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (rightDerivedLowerShriekOfCompactificationComparisonIso _ d).symm

/-- The étale comparison `Rf_!(c) ≃ Rf_!(d)` on bounded below complexes satisfies the cocycle
condition. -/
lemma _root_.AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso_trans
    (c₁ c₂ c₃ : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c₁ c₂ ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c₂ c₃ =
      Etale.rightDerivedLowerShriekOfCompactificationPlusιIso Λ c₁ c₃ := by
  ext K
  simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  rw [← Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans Λ c₁ c₂ c₃]
  simp

/-- The cocycle condition for the comparisons of the pro-étale exceptional direct images of
three compactifications on objects of étale origin. -/
lemma rightDerivedLowerShriekOfCompactificationOriginIso_trans (c₁ c₂ c₃ : Compactification f) :
    rightDerivedLowerShriekOfCompactificationOriginIso Λ c₁ c₂ ≪≫
        rightDerivedLowerShriekOfCompactificationOriginIso Λ c₂ c₃ =
      rightDerivedLowerShriekOfCompactificationOriginIso Λ c₁ c₃ := by
  ext K
  simp only [rightDerivedLowerShriekOfCompactificationOriginIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  rw [← Etale.rightDerivedLowerShriekOfCompactificationPlusιIso_trans Λ c₁ c₂ c₃]
  simp

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: for a compactification
`c = (X ⟶[j] X̄ ⟶[ā] Y)` of `f`, the canonical isomorphism `Rf_! K ≃ Rā_* j_! K` between the
exceptional direct image (for the chosen compactification) and the derived direct image of the
extension by zero along `c`, on objects `K = ν_X^* K₀` of étale origin. For `f = a_X` the
structure morphism this is `RΓ_c(X, K) ≃ RΓ(X̄, j_! K)`. It respects changes of
compactification by `rightDerivedLowerShriekOfCompactificationOriginIso_trans`. -/
noncomputable def rightDerivedLowerShriekCompactificationIso [HasCompactification f]
    (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c :=
  rightDerivedLowerShriekOfCompactificationOriginIso Λ (HasCompactification.compactification f) c

end AlgebraicGeometry.ProEtale
