/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperNoetherian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability

/-!
# Proper direct images with finite coefficients on the pro-étale site

Let `Λ` be a finite ring and `f : X ⟶ Y` a quasi-compact quasi-separated morphism of schemes.
Bounded constructibility on the pro-étale site is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), and the pro-étale direct
image of `ν^* K'` is `ν^* Rf_* K'` for bounded below `K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`). Hence:

* `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar_of_etale`: if the étale
  `Rf_*` preserves bounded constructible complexes, so does the pro-étale one;
* `ProEtale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`:
  for `f` proper over a noetherian scheme over a field `k` and `Λ` killed by an integer
  invertible in `k`, from
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- If the étale derived direct image along a quasi-compact quasi-separated morphism `f` preserves
bounded constructible complexes of sheaves of `Λ`-modules, so does the pro-étale one: a bounded
constructible pro-étale complex is `ν^* K'` for a bounded constructible étale complex `K'`, and
`Rf_* ν^* K' ≅ ν^* Rf_* K'`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (hf : ∀ K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K' →
        Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K'))
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  exact (DerivedCategory.boundedConstructible _ Y).prop_of_iso
    ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso e.symm ≪≫
      rightDerivedLowerStarMapDerivedCategoryObjIso _ f K' hK'.1.1).symm
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj (hf K' hK'))

/-- The pro-étale form of
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`:
for a proper morphism `f : X ⟶ Y` to a noetherian scheme over a field `k` in which the exponent of
the finite ring `Λ` is invertible, the pro-étale `Rf_*` preserves bounded constructible complexes of
sheaves of `Λ`-modules. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian {k : Type u}
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) :=
  boundedConstructible_rightDerivedLowerStar_of_etale f
    (fun _ hK' ↦ Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian aY f
      hK') hK

end AlgebraicGeometry.ProEtale
