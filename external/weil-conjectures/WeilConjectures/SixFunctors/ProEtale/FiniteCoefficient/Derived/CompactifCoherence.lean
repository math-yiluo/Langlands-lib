/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate

/-!
# Compactification coherence

Let `f : X ⟶ Y` be a quasi-compact morphism, `Λ` a finite coefficient ring and
`r : c₁.Refinement c₂` a refinement of compactifications `cᵢ = (X ⟶[jᵢ] X̄ᵢ ⟶[f̄ᵢ] Y)` of `f`,
with underlying proper map `u : X̄₁ ⟶ X̄₂`. Blueprint
`proposition-construction-independence-rf-shriek` states that the canonical comparison between the
compact-support candidates `Rf̄₁_* j₁! ≅ Rf̄₂_* j₂!` is the composite of the proper composition
isomorphism `Rf̄₁_* ≅ Rf̄₂_* Ru_*` with `Rf̄₂_*` of the isomorphism `Ru_* j₁! ≅ j₂!`, that these
comparisons are identities for identity refinements and transitive, and that comparing through a
common refinement gives isomorphisms `Rf^{c₁}_! ≅ Rf^{c₂}_!` independent of the common refinement
and satisfying the cocycle condition, on the complexes of étale origin.

On the complexes `D⁺_et(X, Λ)` of étale origin the comparisons are by construction the étale
ones transported along `ν^*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso`).
This file proves the remaining clause: the étale comparison along an arbitrary refinement is
`Rf̄₂_*` of the isomorphism `α_u : j₂! ≅ Ru_* j₁!`
(`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso`), followed by the composition
isomorphism `Rf̄₂_* Ru_* ≅ Rf̄₁_*`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_hom_eq`:
  the étale comparison along a refinement is `Rf̄₂_* α_u` followed by the composition
  isomorphism.
- `ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_eq`:
  blueprint `proposition-construction-independence-rf-shriek`, on the complexes of étale origin.
- `rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_trans_symm_eq`:
  independence of the common refinement (blueprint
  `proposition-construction-independence-rf-shriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  [QuasiCompact f] {c d e : Compactification f}

namespace Etale

/-- The comparison of candidates along a refinement `x = w.comp r`, with `w` and `x` having
cartesian squares over `X`, is `R(d.g)_* α_r` followed by the composition isomorphism and the
comparison along `w`. -/
lemma rightDerivedLowerShriekOfCompactificationPlusComparison_eq_comp
    (r : c.Refinement d) {c' : Compactification f} (w : c'.Refinement c)
    (hw : IsPullback c'.i (𝟙 X) w.hom c.i) (hx : IsPullback c'.i (𝟙 X) (w.comp r).hom d.i) :
    rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ) (w.comp r) hx =
      (Functor.whiskerRight (refinementOpenImmersionLowerShriekIso Λ r).hom
          (d.g)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ≫
        Functor.whiskerLeft D+((c.i)_!open[ModuleCat.{u + 1} Λ])
          (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[ModuleCat.{u + 1} Λ]
            (d.g)_*[ModuleCat.{u + 1} Λ] (refinementLowerStarComp _ r)).hom) ≫
        rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ) w hw := by
  rw [rightDerivedLowerShriekOfCompactificationPlusComparison_eq,
    rightDerivedLowerShriekOfCompactificationPlusComparison_eq,
    refinementOpenImmersionLowerShriekComparison_eq_refinementOpenImmersionLowerShriekIso Λ r w
      hw (w.comp r) rfl hx]
  ext K : 2
  have hassoc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_assoc
    ((w.hom)_*[ModuleCat.{u + 1} Λ]) ((r.hom)_*[ModuleCat.{u + 1} Λ])
    ((d.g)_*[ModuleCat.{u + 1} Λ]) (((w.comp r).hom)_*[ModuleCat.{u + 1} Λ])
    ((c.g)_*[ModuleCat.{u + 1} Λ]) ((c'.g)_*[ModuleCat.{u + 1} Λ])
    (Etale.lowerStarComp _ w.hom r.hom ((w.comp r).hom) rfl)
    (refinementLowerStarComp _ r) (refinementLowerStarComp _ (w.comp r))
    (refinementLowerStarComp _ w) (refinementLowerStarComp_comp _ w r))
    (D+((c'.i)_!open[ModuleCat.{u + 1} Λ]).obj K)
  have hnat := (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[ModuleCat.{u + 1} Λ]
    (d.g)_*[ModuleCat.{u + 1} Λ] (refinementLowerStarComp _ r)).hom.naturality
    ((refinementOpenImmersionLowerShriekComparison _ w hw).app K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map] at hassoc hnat ⊢
  simp only [Functor.map_comp, Category.assoc, hassoc]
  rw [reassoc_of% hnat]

/-- Blueprint `proposition-construction-independence-rf-shriek`, the étale form of the first clause:
the comparison `Rf_!(d) ≅ Rf_!(c)` of the candidates along an arbitrary refinement
`r : c.Refinement d` with underlying proper map `u = r.hom` is `R(d.g)_*` of the isomorphism
`α_u : (d.i)_! ≅ Ru_* (c.i)_!` (`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso`)
followed by the proper composition isomorphism `R(d.g)_* Ru_* ≅ R(c.g)_*`. -/
theorem rightDerivedLowerShriekOfCompactificationPlusRefinementIso_hom_eq (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r).hom =
      Functor.whiskerRight (refinementOpenImmersionLowerShriekIso Λ r).hom
          (d.g)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ≫
        Functor.whiskerLeft D+((c.i)_!open[ModuleCat.{u + 1} Λ])
          (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[ModuleCat.{u + 1} Λ]
            (d.g)_*[ModuleCat.{u + 1} Λ] (refinementLowerStarComp _ r)).hom := by
  rw [rightDerivedLowerShriekOfCompactificationPlusRefinementIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, IsIso.comp_inv_eq,
    rightDerivedLowerShriekOfCompactificationPlusComparison_eq_comp Λ r
      (Compactification.infFst c c) (Compactification.isPullback_infFst c c)]

end Etale

namespace ProEtale

/-- The isomorphism `R(d.g)_* (d.i)_! ≅ R(c.g)_* (c.i)_!` on bounded below étale complexes
attached to a refinement `r : c.Refinement d`: `R(d.g)_*` of `α_u : (d.i)_! ≅ Ru_* (c.i)_!`
(`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekIso`), followed by the proper
composition isomorphism `R(d.g)_* Ru_* ≅ R(c.g)_*`. -/
noncomputable def refinementCompositeIso (r : c.Refinement d) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c :=
  Functor.isoWhiskerRight (Etale.refinementOpenImmersionLowerShriekIso Λ r)
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) d.g).rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' (Etale.lowerStar (ModuleCat.{u + 1} Λ) r.hom)
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) d.g) (Etale.refinementLowerStarComp _ r))

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compactification coherence.

For a refinement `r : c.Refinement d` of compactifications of `f` with underlying proper map
`u = r.hom`, the canonical comparison `Rf^d_{!,n} ≅ Rf^c_{!,n}` between the compact-support
candidates on the complexes `D⁺_et(X, Λ)` of étale origin
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso`)
is, through the equivalence `ν^* : D⁺(X_ét, Λ) ≌ D⁺_et(X, Λ)`, the composite of `R(d.g)_*` of
the isomorphism `α_u : (d.i)_! ≅ Ru_* (c.i)_!` with the proper composition isomorphism
`R(d.g)_* Ru_* ≅ R(c.g)_*` (`AlgebraicGeometry.ProEtale.refinementCompositeIso`).

The other clauses of the proposition are:
* identity and transitivity:
  `rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_id` and
  `rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_comp`;
* the comparison `Rf^{c}_{!,n} ≅ Rf^{d}_{!,n}` through a common refinement
  (`rightDerivedLowerShriekOfCompactificationEtaleOriginIso`), its independence of the common
  refinement (`rightDerivedLowerShriekOfCompactificationEtaleOriginIso_eq_refinementIso`,
  `rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_trans_symm_eq`) and the
  cocycle condition (`rightDerivedLowerShriekOfCompactificationEtaleOriginIso_refl`,
  `rightDerivedLowerShriekOfCompactificationEtaleOriginIso_trans`). -/
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_eq
    (r : c.Refinement d) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ r =
      etaleOriginIsoOfEtaleIso Λ (refinementCompositeIso Λ r) := by
  rw [rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso]
  congr 1
  ext : 1
  exact Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_hom_eq Λ r

/-- Blueprint `proposition-construction-independence-rf-shriek`: for compactifications
`X ⟶[j] X̄ ⟶[f̄] Y` of `f`, with `j_!` the extension by zero and `Rf̄_*` the derived direct image,
the comparison maps along refinements (proper maps over `Y`) are the natural isomorphisms of
blueprint `proposition-construction-independence-rf-shriek`
(`rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_eq`); they are the identity
for the identity refinement
(`rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_id`), transitive
(`rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_comp`), satisfy the cocycle
condition (`rightDerivedLowerShriekOfCompactificationEtaleOriginIso_trans`), and the comparison
between two compactifications obtained through a common refinement does not depend on that
refinement: this lemma. -/
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_trans_symm_eq
    {c₁ c₂ e e' : Compactification f} (r : e.Refinement c₁) (s : e.Refinement c₂)
    (r' : e'.Refinement c₁) (s' : e'.Refinement c₂) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ r ≪≫
        (rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ s).symm =
      rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ r' ≪≫
        (rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ s').symm := by
  rw [← rightDerivedLowerShriekOfCompactificationEtaleOriginIso_eq_refinementIso,
    ← rightDerivedLowerShriekOfCompactificationEtaleOriginIso_eq_refinementIso]

end ProEtale

end AlgebraicGeometry
