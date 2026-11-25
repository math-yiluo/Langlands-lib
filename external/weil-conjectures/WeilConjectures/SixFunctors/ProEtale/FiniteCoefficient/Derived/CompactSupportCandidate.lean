/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition

/-!
# The compact-support candidate and its compactification independence

Let `f : X ⟶ Y` be a morphism of schemes, `Λ` a finite ring (the stage `A = A_{E,n}`) and
`c = (X ⟶[j] X̄ ⟶[f̄] Y)` a compactification of `f`. Blueprint
`proposition-construction-independence-rf-shriek` attaches to `c` the functor
`Rf^c_{!,n} = Rf̄_* j_! : D(X_proét, Λ) ⥤ D(Y_proét, Λ)`; this is
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`. On the full subcategory
`D⁺_et(X, Λ)` of complexes coming from the étale site with a witness — the bounded below objects
of étale origin `AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin`, which contain the
bounded constructible ones — the superscript `c` may be dropped: blueprint
`proposition-construction-independence-rf-shriek` provides, for a refinement `u : c₁ ⟶ c₂`, a
comparison isomorphism `Rf^{c₁}_{!,n} ≅ Rf^{c₂}_{!,n}` which is the identity for identity
refinements and transitive under composition.

On `D⁺_et(X, Λ)` the comparison isomorphisms are those of the étale site
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, induced by
proper composition and extension by zero), transported along the equivalence
`ν^* : D⁺(X_ét, Λ) ≌ D⁺_et(X, Λ)`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarPlusEtaleOrigin`) and the compact-support
comparison `Rf^c_! ν^* ≅ ν^* Rf^{c,ét}_!`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso`). The
identity, transitivity, cocycle and independence-of-the-common-refinement laws are transported
from the étale ones.

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOrigin`: the
  compact-support candidate `Rf^c_{!,n}` on `D⁺_et(X, Λ)`.
- `AlgebraicGeometry.ProEtale.etaleOriginIsoOfEtaleIso`: the transport of an isomorphism
  between étale compact-support functors to the étale-origin subcategory.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso`:
  the comparison along a refinement.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso`: the
  comparison between two compactifications, through their common refinement.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekEtaleOrigin`: `Rf_{!,n}` on `D⁺_et(X, Λ)`
  for the chosen compactification, the functor with the superscript dropped.

## Main statements

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_id`
  and `..._comp`: the identity and transitivity laws.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso_refl` and
  `..._trans`: the cocycle condition.
- `..._eq_refinementIso`: independence of the common refinement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact-support candidate attached
to a compactification.

For a compactification `c = (X ⟶[j] X̄ ⟶[f̄] Y)` of `f`, the functor `Rf^c_{!,n} = Rf̄_* j_!`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, defined on all of
`D(X_proét, Λ)` with `j_!` exact and `Rf̄_*` computed by K-injective resolutions), restricted to
the full subcategory `D⁺_et(X, Λ)` of complexes coming from the étale site, the bounded below
objects of étale origin. -/
noncomputable def rightDerivedLowerShriekOfCompactificationEtaleOrigin (c : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
    ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c

/-- The compact-support candidate on `D⁺_et(X, Λ)`, read through the equivalence
`ν^* : D⁺(X_ét, Λ) ≌ D⁺_et(X, Λ)`, is `ν^*` of the étale compact-support functor of `c`:
the compact-support comparison
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso`. -/
noncomputable def comparisonUpperStarPlusEtaleOriginCompIso (c : Compactification f) :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X ⋙
        rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
        DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    rightDerivedLowerShriekOfCompactificationComparisonIso (ModuleCat.{u + 1} Λ) c ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility _ c).symm _ ≪≫
    Functor.associator _ _ _

/-- Precomposition with the equivalence `ν^* : D⁺(X_ét, Λ) ≌ D⁺_et(X, Λ)` is fully faithful on
functor categories. -/
noncomputable def whiskeringLeftComparisonUpperStarPlusEtaleOriginFullyFaithful :
    ((Functor.whiskeringLeft _ _
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))).obj
        (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X)).FullyFaithful :=
  (Functor.asEquivalence
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X)).symm.congrLeft
      |>.fullyFaithfulFunctor

/-- Transport of an isomorphism `φ : Rf^{c,ét}_! ≅ Rf^{d,ét}_!` of étale compact-support
functors on `D⁺(X_ét, Λ)` to an isomorphism `Rf^c_{!,n} ≅ Rf^d_{!,n}` on `D⁺_et(X, Λ)`, through
the compact-support comparisons and the equivalence `ν^*`. -/
noncomputable def etaleOriginIsoOfEtaleIso {c d : Compactification f}
    (φ : Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d) :
    rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ c ≅
      rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ d :=
  (whiskeringLeftComparisonUpperStarPlusEtaleOriginFullyFaithful Λ).preimageIso
    (comparisonUpperStarPlusEtaleOriginCompIso Λ c ≪≫ Functor.isoWhiskerRight φ _ ≪≫
      (comparisonUpperStarPlusEtaleOriginCompIso Λ d).symm)

/-- The transported isomorphism is characterised by its value on objects `ν^* K'`. -/
lemma etaleOriginIsoOfEtaleIso_hom_app {c d : Compactification f}
    (φ : Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d)
    (K' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (etaleOriginIsoOfEtaleIso Λ φ).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} Λ) X).obj K') =
      (comparisonUpperStarPlusEtaleOriginCompIso Λ c).hom.app K' ≫
        D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map (φ.hom.app K')) ≫
        (comparisonUpperStarPlusEtaleOriginCompIso Λ d).inv.app K' := by
  have := congrArg (fun α ↦ α.app K')
    ((whiskeringLeftComparisonUpperStarPlusEtaleOriginFullyFaithful Λ (Y := Y)).map_preimage
      (comparisonUpperStarPlusEtaleOriginCompIso Λ c ≪≫ Functor.isoWhiskerRight φ _ ≪≫
        (comparisonUpperStarPlusEtaleOriginCompIso Λ d).symm).hom)
  simpa [etaleOriginIsoOfEtaleIso] using this

/-- Transport sends the identity to the identity. -/
@[simp]
lemma etaleOriginIsoOfEtaleIso_refl (c : Compactification f) :
    etaleOriginIsoOfEtaleIso Λ (Iso.refl
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c)) =
      Iso.refl _ := by
  ext : 1
  apply (whiskeringLeftComparisonUpperStarPlusEtaleOriginFullyFaithful Λ (Y := Y)).map_injective
  ext K'
  simpa using etaleOriginIsoOfEtaleIso_hom_app Λ (Iso.refl _) K'

/-- Transport is compatible with composition. -/
lemma etaleOriginIsoOfEtaleIso_trans {c d e : Compactification f}
    (φ : Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d)
    (ψ : Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) e) :
    etaleOriginIsoOfEtaleIso Λ (φ ≪≫ ψ) =
      etaleOriginIsoOfEtaleIso Λ φ ≪≫ etaleOriginIsoOfEtaleIso Λ ψ := by
  ext : 1
  apply (whiskeringLeftComparisonUpperStarPlusEtaleOriginFullyFaithful Λ (Y := Y)).map_injective
  ext K'
  simp only [Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app]
  rw [etaleOriginIsoOfEtaleIso_hom_app, etaleOriginIsoOfEtaleIso_hom_app,
    etaleOriginIsoOfEtaleIso_hom_app]
  simp

/-- Transport is compatible with inverses. -/
lemma etaleOriginIsoOfEtaleIso_symm {c d : Compactification f}
    (φ : Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d) :
    etaleOriginIsoOfEtaleIso Λ φ.symm = (etaleOriginIsoOfEtaleIso Λ φ).symm := by
  have h : etaleOriginIsoOfEtaleIso Λ φ ≪≫ etaleOriginIsoOfEtaleIso Λ φ.symm = Iso.refl _ := by
    rw [← etaleOriginIsoOfEtaleIso_trans, Iso.self_symm_id, etaleOriginIsoOfEtaleIso_refl]
  ext1
  exact (Iso.inv_ext (congrArg Iso.hom h)).symm

section Refinement

variable [Finite Λ] [QuasiCompact f] {c d e : Compactification f}

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compactification-independent
finite-level direct image.

For a refinement `r : c.Refinement d` (a proper map `c.Z ⟶ d.Z` compatible with the open
immersions and the proper maps), the comparison isomorphism `Rf^d_{!,n} ≅ Rf^c_{!,n}` on the
complexes `D⁺_et(X, Λ)` coming from the étale site, induced by proper composition and extension
by zero: the étale comparison
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso`,
transported along `ν^*`. It is the identity for the identity refinement
(`rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_id`) and transitive under
composition (`rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_comp`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso
    (r : c.Refinement d) :
    rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ d ≅
      rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ c :=
  etaleOriginIsoOfEtaleIso Λ (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r)

/-- The comparison along the identity refinement is the identity. -/
@[simp]
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_id
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ
      (Compactification.Refinement.id c) = Iso.refl _ := by
  simp [rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso]

/-- The comparison along a composite of refinements is the composite of the comparisons. -/
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso_comp
    (r : c.Refinement d) (s : d.Refinement e) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ (r.comp s) =
      rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ s ≪≫
        rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ r := by
  simp [rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_comp,
    etaleOriginIsoOfEtaleIso_trans]

/-- The comparison `Rf^c_{!,n} ≅ Rf^d_{!,n}` on `D⁺_et(X, Λ)` between any two compactifications,
through their common refinement `Compactification.inf c d`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationEtaleOriginIso
    (c d : Compactification f) :
    rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ c ≅
      rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ d :=
  etaleOriginIsoOfEtaleIso Λ (Etale.rightDerivedLowerShriekOfCompactificationPlusIso Λ c d)

/-- The comparison between two compactifications does not depend on the common refinement
used to compute it. -/
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginIso_eq_refinementIso
    (r : e.Refinement c) (s : e.Refinement d) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c d =
      rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ r ≪≫
        (rightDerivedLowerShriekOfCompactificationEtaleOriginRefinementIso Λ s).symm := by
  rw [rightDerivedLowerShriekOfCompactificationEtaleOriginIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso Λ r s,
    etaleOriginIsoOfEtaleIso_trans, etaleOriginIsoOfEtaleIso_symm]
  rfl

/-- The comparison of a compactification with itself is the identity. -/
@[simp]
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginIso_refl (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c c = Iso.refl _ := by
  simp [rightDerivedLowerShriekOfCompactificationEtaleOriginIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl]

/-- The cocycle condition for three compactifications. -/
theorem rightDerivedLowerShriekOfCompactificationEtaleOriginIso_trans
    (c₁ c₂ c₃ : Compactification f) :
    rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c₁ c₂ ≪≫
        rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c₂ c₃ =
      rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c₁ c₃ := by
  simp only [rightDerivedLowerShriekOfCompactificationEtaleOriginIso,
    ← etaleOriginIsoOfEtaleIso_trans, Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans]

end Refinement

variable (f) [HasCompactification f]

/-- The compact-support direct image `Rf_{!,n}` on `D⁺_et(X, Λ)` with the superscript dropped:
the candidate for the chosen compactification `HasCompactification.compactification f`, which is
the restriction of `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek`. For any other
compactification `c` it is identified with `Rf^c_{!,n}` by
`rightDerivedLowerShriekOfCompactificationEtaleOriginIso`. -/
noncomputable abbrev rightDerivedLowerShriekEtaleOrigin :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :=
  rightDerivedLowerShriekOfCompactificationEtaleOrigin Λ (HasCompactification.compactification f)

lemma rightDerivedLowerShriekEtaleOrigin_eq :
    rightDerivedLowerShriekEtaleOrigin Λ f =
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f :=
  rfl

end AlgebraicGeometry.ProEtale
