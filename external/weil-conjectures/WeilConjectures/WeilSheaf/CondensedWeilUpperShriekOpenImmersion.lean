/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1)
-/
module

public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekAssembly

/-!
# The condensed Weil `Rf^!` and its exceptional datum

For the compactification `X ⟶[i] Z ⟶[g] Y` of `f` chosen by `WeilComplex.derivedLowerShriek`,
the condensed Weil `Rf^!` is `Rg^!` (the right adjoint of the Weil `Rg_*` in the condensed model,
`WeilComplex.condensedWeilProperRightAdjoint`) followed by the derived Weil pullback `D(i^*)`
along the open immersion. Its underlying complex is the geometric `ī^* ∘ ḡ^!`
(`WeilComplex.condensedGeometricUpperShriek`), and its Frobenius structure is the **exceptional
datum**: the transport along `D(ī^*)` of the right Weil datum of the upstream geometric adjunction
`Rḡ_* ⊣ ḡ^!`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructible_mapDerivedCategory_upperStar_obj`: `D(g^*)` of an
  exact pullback preserves bounded constructible complexes.
- `WeilComplex.condensedUpperShriek`: the condensed Weil `Rf^! = D(i^*) ∘ Rg^!`.
- `WeilComplex.condensedGeometricUpperShriek`: the geometric `ī^* ∘ ḡ^!` on bounded
  constructible condensed complexes.
- `WeilComplex.condensedUpperShriekExceptionalDatum`: the exceptional datum.

## Main result

- `WeilComplex.exists_condensedForget_upperShriek_obj_iso_isWeilEquivariant`: the underlying
  complex of `Rf^! L'` is `ī^* ḡ^! L̄'`, by an isomorphism carrying the Frobenius structure of
  `Rf^! L'` to the exceptional datum.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived pullback `D(g^*)` of the exact pullback of module objects along any morphism of
schemes preserves bounded constructible complexes: `g^*` is exact, so `Hⁿ(D(g^*) K) ≅ g^* Hⁿ(K)`,
and `g^*` preserves zero objects and constructible module objects. -/
theorem boundedConstructible_mapDerivedCategory_upperStar_obj {W X : Scheme.{u}} (g : W ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ W) ((upperStar Λ g).mapDerivedCategory.obj K) := by
  let e (n : ℤ) := ((upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n).app K
  obtain ⟨⟨a, b, hab⟩, hK⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (Functor.map_isZero (upperStar Λ g) (hab i hi)).of_iso (e i).symm
  · exact IsConstructibleModuleObject.of_iso (e n)
      (IsConstructibleModuleObject.upperStar Λ g (hK n))

end ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

open ProEtale

attribute [local instance] Compactification.over

attribute [local instance 1100] CategoryTheory.instOverClass

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

variable (k₀) in
/-- The base change `ī : X̄ ⟶ Z̄` of the open immersion of the compactification. -/
noncomputable abbrev condensedOpenImmersionMap :=
  Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
    (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀)))

variable (k₀) in
/-- The Frobenius exchange `ī^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Z⁻¹)_* ⋙ ī^*` of the condensed pullback along
`ī`. -/
noncomputable abbrev condensedOpenImmersionExchange :=
  CondensedRing.upperStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
    (shriekCompactification k₀ f).i
    (comp_over (shriekCompactification k₀ f).i (Spec (CommRingCat.of k₀)))

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
variable (k₀) in
/-- The condensed Weil pullback `D(i^*)` along the open immersion of the compactification
preserves bounded constructible condensed Weil complexes. -/
theorem condensedWeilObjectProperty_openImmersionUpperStar
    (M : _root_.DerivedCategory (IsoAlgebra (condensedFrobenius k₀ l (shriekCompactification k₀ f).Z)))
    (hM : condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z M) :
    condensedWeilObjectProperty k₀ l X
      ((IsoAlgebra.mapOfNatIso (condensedOpenImmersionExchange k₀ l f)).mapDerivedCategory.obj M) :=
  ObjectProperty.prop_of_iso (condensedBoundedConstructible k₀ l X)
    ((IsoAlgebra.derivedExactForgetCommIso (condensedOpenImmersionExchange k₀ l f)).app M).symm
    (CondensedRing.boundedConstructible_mapDerivedCategory_upperStar_obj _
      (condensedOpenImmersionMap k₀ f) _ hM)

variable (k₀) in
/-- **The condensed Weil `Rf^!`**: `Rg^!` followed by the derived Weil pullback `D(i^*)`, on
bounded constructible condensed Weil complexes. -/
noncomputable def condensedUpperShriek :
    (condensedWeilObjectProperty k₀ l Y).FullSubcategory ⥤
      (condensedWeilObjectProperty k₀ l X).FullSubcategory :=
  condensedWeilProperRightAdjoint k₀ l f ⋙
    ObjectProperty.liftFullSubcategory _ _
      (IsoAlgebra.mapOfNatIso (condensedOpenImmersionExchange k₀ l f)).mapDerivedCategory
      (condensedWeilObjectProperty_openImmersionUpperStar k₀ l f)

variable (k₀) in
/-- **The geometric `ī^* ∘ ḡ^!`** on bounded constructible condensed complexes, the underlying
functor of `condensedUpperShriek`. -/
noncomputable def condensedGeometricUpperShriek :
    (condensedBoundedConstructible k₀ l Y).FullSubcategory ⥤
      (condensedBoundedConstructible k₀ l X).FullSubcategory :=
  condensedProperRightAdjoint k₀ l f ⋙
    ObjectProperty.liftFullSubcategory _ _
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
      (fun K hK ↦ CondensedRing.boundedConstructible_mapDerivedCategory_upperStar_obj _
        (condensedOpenImmersionMap k₀ f) K hK)

set_option linter.style.longLine false in
variable (k₀) in
/-- The underlying bounded constructible condensed complex of a condensed Weil complex. -/
noncomputable abbrev condensedForgetObj (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    (condensedBoundedConstructible k₀ l Y).FullSubcategory :=
  ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩

variable (k₀) in
/-- **The exceptional datum** on `ī^* ḡ^! L̄'`: the transport along `D(ī^*)` of the right Weil
datum of the upstream geometric adjunction `Rḡ_* ⊣ ḡ^!` of the Frobenius structure of `L'`. -/
noncomputable def condensedUpperShriekExceptionalDatum
    (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    (condensedFrobenius k₀ l X).mapDerivedCategory.obj
        ((condensedGeometricUpperShriek k₀ l f).obj (condensedForgetObj k₀ l L')).obj ⟶
      ((condensedGeometricUpperShriek k₀ l f).obj (condensedForgetObj k₀ l L')).obj :=
  transportWeilDatum
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
    (IsoAlgebra.derivedExactCommIso (condensedOpenImmersionExchange k₀ l f)).symm
    (Adjunction.rightWeilDatum (condensedProperAdjunction k₀ l f)
      (IsoAlgebra.liftedDerivedCommIso (condensedProperExchange k₀ l f) _ _
        (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
          (shriekCompactification k₀ f).Z)
        (fun K hK ↦
          (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
        (condensedProperPreserves k₀ l f))
      (ObjectProperty.homMk
        (X := (ObjectProperty.liftFullSubcategory _ _
          (condensedFrobenius k₀ l Y).mapDerivedCategory
          (fun K hK ↦
            (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)).obj
            (condensedForgetObj k₀ l L'))
        (Y := condensedForgetObj k₀ l L')
        ((IsoAlgebra.derivedStrIso _).hom.app L'.obj))).hom

variable (k₀) in
/-- **The Frobenius structure of the condensed Weil `Rf^!` is the exceptional datum**: the
underlying complex of `Rf^! L'` is `ī^* ḡ^! L̄'`, by an isomorphism `θ` which is Frobenius
equivariant for the structure of `Rf^! L'` and the exceptional datum. -/
theorem exists_condensedForget_upperShriek_obj_iso_isWeilEquivariant
    (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    ∃ θ : (IsoAlgebra.forget _).mapDerivedCategory.obj
        ((condensedUpperShriek k₀ l f).obj L').obj ≅
        ((condensedGeometricUpperShriek k₀ l f).obj (condensedForgetObj k₀ l L')).obj,
      IsWeilEquivariant (condensedFrobenius k₀ l X).mapDerivedCategory
        ((IsoAlgebra.derivedStrIso _).hom.app ((condensedUpperShriek k₀ l f).obj L').obj)
        (condensedUpperShriekExceptionalDatum k₀ l f L') θ.hom := by
  obtain ⟨θg, hθg⟩ :=
    exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum_concrete k₀ l f L'
  -- the structure of `D(i^*) M` is the transport of that of `M`
  have h₂ := IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app
    (condensedOpenImmersionExchange k₀ l f) ((condensedWeilProperRightAdjoint k₀ l f).obj L').obj
  -- transport `θg` along `ī^*`
  have h₃ := hθg.map
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f)).mapDerivedCategory
    (IsoAlgebra.derivedExactCommIso (condensedOpenImmersionExchange k₀ l f)).symm
  exact ⟨(IsoAlgebra.derivedExactForgetCommIso (condensedOpenImmersionExchange k₀ l f)).app
      ((condensedWeilProperRightAdjoint k₀ l f).obj L').obj ≪≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (condensedOpenImmersionMap k₀ f)).mapDerivedCategory.mapIso θg, h₂.comp h₃⟩

end WeilComplex

end AlgebraicGeometry
