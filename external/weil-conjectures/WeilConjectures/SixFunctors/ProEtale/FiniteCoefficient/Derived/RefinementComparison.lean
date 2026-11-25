/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# The proper–open comparison on the pro-étale site

Let `r : c.Refinement d` be a refinement of compactifications of `f : X ⟶ Y` whose square over
`X` is cartesian, with `u = r.hom : c.Z ⟶ d.Z`, and let `Λ` be a finite ring. On the étale site
the comparison `α_u : j_{d!} ⟶ Ru_* j_{c!}`
(`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison`) is an isomorphism, the
identity for the identity refinement and transitive. This file transports it to the pro-étale
site along the comparison functor `ν^*`, on bounded below complexes of étale origin
`K = ν_X^* L` (blueprint `proposition-construction-independence-rf-shriek--7`):
`j_{d!} ν^* L ≅ Ru_* j_{c!} ν^* L`
(`AlgebraicGeometry.ProEtale.refinementOpenImmersionLowerShriekProEtaleIso`).

The transport uses the commutation of extension by zero with `ν^*`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarDerivedPlusIso`) and the
base change isomorphism `ν^* Ru_* ≅ Ru_* ν^*` for the proper `u`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonUpperStarIso`). Since the latter is
compatible with the identity and composition isomorphisms of the derived direct images
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonUpperStarIso_hom_app_id` and
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonUpperStarIso_hom_app_comp`), the
pro-étale comparison inherits the identity and transitivity laws.

## Main results

- `AlgebraicGeometry.ProEtale.refinementOpenImmersionLowerShriekProEtaleIso_hom_app_id`
- `AlgebraicGeometry.ProEtale.refinementOpenImmersionLowerShriekProEtaleIso_hom_app_comp`
-/

@[expose] public section
universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The base change isomorphism `ν_V^* ∘ R⁺f_* ≅ R⁺f_* ∘ ν_U^*`. -/
noncomputable def rightDerivedLowerStarComparisonUpperStarIso {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  have := isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective _ f I)
  asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))

/-- The extension by zero commutes with `ν^*` on bounded below derived categories. -/
noncomputable def openImmersionLowerShriekComparisonUpperStarDerivedPlusIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: proper–open comparison for
complexes from the étale site.

For a refinement `r : c.Refinement d` of compactifications of `f : X ⟶ Y` whose square over `X`
is cartesian, with `u = r.hom : c.Z ⟶ d.Z` proper and `j_c = c.i`, `j_d = d.i` the open
immersions of `X` (so `u ∘ j_c = j_d`), a finite coefficient ring `Λ` and a bounded below étale
complex `L` on `X`, the isomorphism of pro-étale complexes `j_{d!} ν^* L ≅ Ru_* j_{c!} ν^* L`,
natural in `L`. It is obtained, as in the blueprint, by applying the exact functor `ν^*` to the
étale comparison isomorphism `α_u`
(`AlgebraicGeometry.Etale.refinementOpenImmersionLowerShriekComparison`,
blueprint `proposition-construction-independence-rf-shriek--7`), and identifying `ν^* j_! ≅ j_! ν^*`
and `ν^* Ru_* ≅ Ru_* ν^*` (the latter since `u` is quasi-compact and quasi-separated). Its identity
and composition laws are
`AlgebraicGeometry.ProEtale.refinementOpenImmersionLowerShriekProEtaleIso_hom_app_id` and
`AlgebraicGeometry.ProEtale.refinementOpenImmersionLowerShriekProEtaleIso_hom_app_comp`.

The blueprint states this for arbitrary proper `u` between Noetherian schemes; it is formalised
for refinements of compactifications with `u⁻¹(X) = X`, the setting of the étale comparison in
this repository. -/
noncomputable def refinementOpenImmersionLowerShriekProEtaleIso {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) d.i).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus ⋙
          (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) r.hom).rightDerivedFunctorPlus :=
  (openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ d.i).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (Etale.refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hr)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarComparisonUpperStarIso Λ r.hom) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ c.i) _ ≪≫
    Functor.associator _ _ _


/-- The components of `refinementOpenImmersionLowerShriekProEtaleIso`. -/
lemma refinementOpenImmersionLowerShriekProEtaleIso_hom_app {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (refinementOpenImmersionLowerShriekProEtaleIso Λ r hr).hom.app K =
      (openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ d.i).inv.app K ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) d.Z).mapDerivedCategoryPlus.map
          ((Etale.refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hr).app K) ≫
        (rightDerivedLowerStarComparisonUpperStarIso Λ r.hom).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj
            K) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) r.hom).rightDerivedFunctorPlus.map
          ((openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ c.i).hom.app K) := by
  simp [refinementOpenImmersionLowerShriekProEtaleIso]

/-- The pro-étale identity isomorphism `R⁺(𝟙)_* ≅ 𝟭`. -/
noncomputable def lowerStarIdDerivedPlus (V : Scheme.{u}) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 V)).rightDerivedFunctorPlus ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorPlusNatIso (ProEtale.lowerStarId _ V) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _

omit [Finite Λ] in
/-- The base change isomorphism `ν^* R(𝟙)_* ≅ R(𝟙)_* ν^*` is induced by the identity
isomorphisms `R(𝟙)_* ≅ 𝟭` on both sites. -/
lemma rightDerivedLowerStarComparisonUpperStarIso_hom_app_id (V : Scheme.{u})
    (M : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarComparisonUpperStarIso Λ (𝟙 V)).hom.app M =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.map
          ((Etale.lowerStarIdDerivedPlus _ V).hom.app M) ≫
        (lowerStarIdDerivedPlus Λ V).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj M) :=
  Functor.rightDerivedFunctorPlusBaseChange_id (Etale.lowerStarId _ V) (ProEtale.lowerStarId _ V)
    _ (lowerStarComparisonUpperStarBaseChange_app_id _ V) M

/-- The identity law of blueprint `proposition-construction-independence-rf-shriek--7`: for the
identity refinement the pro-étale comparison is the inverse of the identity isomorphism
`R(𝟙)_* ≅ 𝟭`. -/
theorem refinementOpenImmersionLowerShriekProEtaleIso_hom_app_id (c : Compactification f)
    (hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (refinementOpenImmersionLowerShriekProEtaleIso Λ (Compactification.Refinement.id c) hid).hom.app
        K = (lowerStarIdDerivedPlus Λ c.Z).inv.app _ := by
  rw [refinementOpenImmersionLowerShriekProEtaleIso_hom_app,
    Etale.refinementOpenImmersionLowerShriekComparison_id]
  erw [rightDerivedLowerStarComparisonUpperStarIso_hom_app_id]
  simp only [Functor.whiskerLeft_app]
  have hc : (comparisonUpperStar (ModuleCat.{u + 1} Λ) c.Z).mapDerivedCategoryPlus.map
        ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) c.Z).inv.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj
            K)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) c.Z).mapDerivedCategoryPlus.map
        ((Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) c.Z).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj
            K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  have hn := (lowerStarIdDerivedPlus Λ c.Z).inv.naturality
    ((openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ c.i).hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  erw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- The pro-étale direct image preserves injective objects, being right adjoint to the exact
pullback. -/
instance preservesInjectiveObjects_lowerStar {T S : Scheme.{u}} (h : T ⟶ S) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) h).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ProEtale.upperStarLowerStarAdjunction _ h)

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar_of_abelian

omit [Finite Λ] in
/-- The base change isomorphisms `ν^* Rf_* ≅ Rf_* ν^*` are compatible with the composition
isomorphisms of the derived direct images on both sites. -/
@[reassoc]
lemma rightDerivedLowerStarComparisonUpperStarIso_hom_app_comp {R S T : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) [IsProper h₁] [IsProper h₂]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) R).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' _ _
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂)).hom.app M) ≫
      (rightDerivedLowerStarComparisonUpperStarIso Λ (h₁ ≫ h₂)).hom.app M =
    (rightDerivedLowerStarComparisonUpperStarIso Λ h₂).hom.app
        ((Etale.lowerStar _ h₁).rightDerivedFunctorPlus.obj M) ≫
      (ProEtale.lowerStar _ h₂).rightDerivedFunctorPlus.map
        ((rightDerivedLowerStarComparisonUpperStarIso Λ h₁).hom.app M) ≫
      (Functor.rightDerivedFunctorPlusCompIso' _ _
          (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus.obj M) := by
  have h := Functor.rightDerivedFunctorPlusBaseChange_comp
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂)
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂)
    (lowerStarComparisonUpperStarBaseChange h₁ _) (lowerStarComparisonUpperStarBaseChange h₂ _)
    (lowerStarComparisonUpperStarBaseChange (h₁ ≫ h₂) _)
    (lowerStarComparisonUpperStarBaseChange_app_comp _ h₁ h₂) M
  rw [← cancel_epi ((comparisonUpperStar (ModuleCat.{u + 1} Λ) R).mapDerivedCategoryPlus.map
    ((Functor.rightDerivedFunctorPlusCompIso' _ _
      (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂)).inv.app M))]
  simp only [rightDerivedLowerStarComparisonUpperStarIso, asIso_hom]
  rw [reassoc_of% h]
  simp [← Functor.map_comp_assoc]

/-- The composition law of blueprint `proposition-construction-independence-rf-shriek--7`: for
refinements `r : c.Refinement d` and `s : d.Refinement e` with cartesian squares, the pro-étale
comparison along `r.comp s` is the comparison along `s` followed by `R(s)_*` of the comparison
along `r`, under `R(s)_* R(r)_* ≅ R(r ≫ s)_*`. -/
theorem refinementOpenImmersionLowerShriekProEtaleIso_hom_app_comp {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (hs : IsPullback d.i (𝟙 X) s.hom e.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (refinementOpenImmersionLowerShriekProEtaleIso Λ (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs)).hom.app K =
      (refinementOpenImmersionLowerShriekProEtaleIso Λ s hs).hom.app K ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) s.hom).rightDerivedFunctorPlus.map
          ((refinementOpenImmersionLowerShriekProEtaleIso Λ r hr).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusCompIso' _ _
          (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) r.hom s.hom)).hom.app
            ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
              c.i).mapDerivedCategoryPlus.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj K)) := by
  rw [refinementOpenImmersionLowerShriekProEtaleIso_hom_app,
    refinementOpenImmersionLowerShriekProEtaleIso_hom_app,
    refinementOpenImmersionLowerShriekProEtaleIso_hom_app,
    Etale.refinementOpenImmersionLowerShriekComparison_comp _ r s hr hs]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  have hcancel : (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) s.hom).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ d.i).hom.app K) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) s.hom).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ d.i).inv.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [reassoc_of% hcancel]
  have hBC := (rightDerivedLowerStarComparisonUpperStarIso Λ s.hom).hom.naturality
    ((Etale.refinementOpenImmersionLowerShriekComparison (ModuleCat.{u + 1} Λ) r hr).app K)
  simp only [Functor.comp_map] at hBC
  simp only [← reassoc_of% hBC]
  congr 3
  refine (rightDerivedLowerStarComparisonUpperStarIso_hom_app_comp_assoc Λ r.hom s.hom _ _).trans ?_
  have hC := (Functor.rightDerivedFunctorPlusCompIso' _ _
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} Λ) r.hom s.hom)).hom.naturality
    ((openImmersionLowerShriekComparisonUpperStarDerivedPlusIso Λ c.i).hom.app K)
  simp only [Functor.comp_map] at hC
  congr 2
  exact hC.symm

end AlgebraicGeometry.ProEtale
