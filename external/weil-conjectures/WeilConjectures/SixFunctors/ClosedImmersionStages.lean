/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek

/-!
# The direct image along a closed immersion is fully faithful at every coefficient stage

Blueprint `lemma-local-cohomology-right-adjoint--1`: for a closed immersion `i : Z ⟶ X`, the direct
image `i_* = Ri_* = Ri_!` is fully faithful on the categories `Dᵇc(-, Λ)` at each of the coefficient
stages `Λ = A_{E,n}, 𝒪_E, E, ℚ̄_ℓ`, and consequently, at every stage at which `i_*` has a right
adjoint `Ri^!` on these categories, the unit `Q ⟶ Ri^! i_* Q` is an isomorphism.

In this repository the stages are realised as follows.

* `A_{E,n}`: the bounded constructible objects `Dᵇc_proét(-, Λ)` of the derived category of
  pro-étale sheaves of `Λ`-modules, `Λ` finite
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`). Here `Ri_*` is fully
  faithful on the whole derived category
  (`AlgebraicGeometry.ProEtale.full_rightDerivedFunctor_lowerStar`), and the right adjoint
  exists on the ambient categories (`lemma-local-cohomology-right-adjoint--1`,
  `AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`).
* `𝒪_E`: the derived complete objects `D_comp(X_ét, 𝒪_E)` of the derived category of étale
  sheaves of `𝒪_E`-modules (`DerivedCategoryDerivedCompleteIntegral`), which `Rf_*` preserves
  (`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`). As `Ri_*` is fully
  faithful on the whole étale derived category, it is so on `D_comp(-, 𝒪_E)`
  (`AlgebraicGeometry.Etale.full_rightDerivedLowerStarDerivedCompleteIntegral`).
* `E`: the rationalization `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)`
  (`DerivedCategoryDerivedCompleteRational`), whose `Hom` groups are those of
  `D_comp(X_ét, 𝒪_E)` with the nonzero elements of `𝒪_E` inverted. The functor induced by an
  `𝒪_E`-linear fully faithful triangulated functor is fully faithful
  (`CategoryTheory.Rationalization.full_map`), which is the blueprint's argument that
  bijectivity persists after tensoring with `E`.
* `ℚ̄_ℓ`: the bounded constructible objects `Dᵇc(X, ℚ̄_ℓ)` of the derived category of `ℓ`-adic
  sheaves `AlgebraicGeometry.ProEtale.AdicSheaf l X`, i.e. pro-étale sheaves of modules over the
  constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`). The `ℓ`-adic `i_*` is
  fully faithful and preserves K-injective complexes, so `Ri_*` is fully faithful on the whole
  derived category
  (`AlgebraicGeometry.ProEtale.full_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar`).

At each stage the full faithfulness is stated for the inclusion of the stage category followed by
`Ri_*`, which is full faithfulness of `i_* : Dᵇc(Z, Λ) ⥤ Dᵇc(X, Λ)` whatever the target
subcategory, and the unit statement for any right adjoint of the corestriction of `i_*` to a
full subcategory containing its image.

The blueprint's proof at the integral stage goes through the Roos triangles of the
`𝒪_E`-adic towers; in the derived-complete model used here this is unnecessary, since the
integral stage is a full subcategory of the derived category of `𝒪_E`-modules, on which `Ri_*`
is fully faithful outright.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- For a fully faithful functor `F : C ⥤ D`, the unit of any adjunction whose left adjoint is a
corestriction of `F` to a full subcategory `P'` of `D` is an isomorphism. -/
lemma _root_.CategoryTheory.ObjectProperty.isIso_unit_app_of_lift {C D : Type*} [Category C]
    [Category D] {P' : ObjectProperty D} {F : C ⥤ D} [F.Full] [F.Faithful]
    (h : ∀ K, P' (F.obj K)) {G : P'.FullSubcategory ⥤ C} (adj : P'.lift F h ⊣ G) (Q : C) :
    IsIso (adj.unit.app Q) :=
  inferInstance

section Finite

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, finite stage `A_{E,n}`: the direct image
`Ri_*` along a closed immersion is fully faithful on the bounded constructible pro-étale
complexes `Dᵇc_proét(Z, Λ)`, `Λ` finite. -/
instance ProEtale.full_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Full :=
  inferInstance

instance ProEtale.faithful_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Faithful :=
  inferInstance

omit [Finite Λ] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the finite stage: for any right
adjoint `Ri^!` of the corestriction of `Ri_* : Dᵇc_proét(Z, Λ) ⥤ D(X_proét, Λ)` to a full
subcategory `P` (for instance `Dᵇc_proét(X, Λ)`), the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism.
On the ambient categories the right adjoint exists, and this is
`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`. -/
theorem ProEtale.isIso_unit_app_boundedConstructible
    {P : ObjectProperty (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))}
    (h : ∀ K, P (((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).obj K))
    {G : P.FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory}
    (adj : P.lift _ h ⊣ G)
    (Q : (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift h adj Q

end Finite

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- `Rf_*` on derived complete objects, as a functor between the full subcategories of
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral`. -/
noncomputable abbrev Etale.rightDerivedLowerStarDerivedCompleteIntegralAux {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    (DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).FullSubcategory :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    ((DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor)
    (fun K ↦ Etale.derivedCompleteIntegral_rightDerivedLowerStar l E f _ K.property)

/-- The direct image `Rf_* : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` on derived complete
objects, the restriction of `Rf_*`
(`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`). -/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteIntegral {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f

noncomputable instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).CommShift ℤ :=
  inferInstanceAs ((Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).CommShift ℤ)

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).IsTriangulated :=
  inferInstanceAs
    (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).IsTriangulated

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) where
  map_smul _ _ :=
    (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.map_injective <|
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor.map_smul _ _

/-- The right derived direct image along a closed immersion is fully faithful on étale sheaves
with values in any Grothendieck abelian category: `i_*` is fully faithful
(`AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion`) and preserves K-injective
complexes as a right adjoint of the exact `i^*`. -/
instance Etale.full_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Full :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

instance Etale.faithful_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Faithful :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, integral stage `𝒪_E`: the direct image
`Ri_*` along a closed immersion is fully faithful on the derived complete objects
`D_comp(Z_ét, 𝒪_E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Full :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Full

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Faithful :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Faithful

/-- The direct image `Rf_* : D_comp(Y_ét, E) ⥤ D_comp(X_ét, E)` at the rational stage, induced
on the rationalizations by `AlgebraicGeometry.Etale.rightDerivedLowerStarDerivedCompleteIntegral`.
-/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteRational {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Rationalization.map _ (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f)

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, rational stage `E`: the direct image `Ri_*`
along a closed immersion is fully faithful on `D_comp(Z_ét, E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Full :=
  Rationalization.full_map _

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Faithful :=
  Rationalization.faithful_map _

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the integral stage: for any
right adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`, the unit `Q ⟶ Ri^! Ri_* Q`
is an isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteIntegral
    {G : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the rational stage: for any
right adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, E) ⥤ D_comp(X_ét, E)`, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteRational
    {G : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteRational l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Integral

section BoundedConstructible

/-! ### The categories `Dᵇc(-, Λ)` at the integral, rational and `ℚ̄_ℓ` stages -/

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, integral stage `𝒪_E`: the direct image
`Ri_*` along a closed immersion is fully faithful on `Dᵇc(Z, 𝒪_E)`
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`: derived complete objects
whose reductions modulo `𝔪_Eⁿ` are bounded constructible of uniformly bounded Tor amplitude). -/
instance Etale.full_boundedConstructibleIntegral_ι_comp_rightDerivedLowerStar :
    ((Etale.DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E)
      Z).ι ⋙ (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        i).rightDerivedFunctor).Full :=
  inferInstance

instance Etale.faithful_boundedConstructibleIntegral_ι_comp_rightDerivedLowerStar :
    ((Etale.DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E)
      Z).ι ⋙ (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        i).rightDerivedFunctor).Faithful :=
  inferInstance

/-- Blueprint `proposition-inverting-ell--2`: Rationalization (scalar localization), the
category `Dᵇc(Y, E) = Dᵇc(Y, 𝒪_E)[1/ϖ_E]` (as its full subcategory, with no Karoubi completion).

The objects of `D_comp(X_ét, E)` coming from `Dᵇc(X, 𝒪_E)`: the rationalization of
`Dᵇc(X, 𝒪_E)`, as a full subcategory of `D_comp(X_ét, E)`. Its `Hom` groups are those of
`Dᵇc(X, 𝒪_E)` with the nonzero elements of `𝒪_E` inverted
(`CategoryTheory.Rationalization.exists_smul_eq_map`,
`CategoryTheory.Rationalization.map_eq_map_iff`). -/
def Etale.DerivedCategory.boundedConstructibleRational (X : Scheme.{u}) :
    ObjectProperty (DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E) :=
  fun K ↦ ∃ L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E,
    Etale.DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K)

/-- The Karoubi envelope of the rational stage `Dᵇc(X, E)` of blueprint
`proposition-inverting-ell--2` (which takes no Karoubi completion; the canonical functor into
the envelope is an equivalence, the rationalization being idempotent complete): the Karoubi
envelope of the rationalization of `Dᵇc(X, 𝒪_E)`. -/
abbrev Etale.DerivedCategoryBoundedConstructibleRational (X : Scheme.{u}) :=
  Idempotents.Karoubi (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory

/-- The direct image `Ri_*` on `Dᵇc(Z, E)`, with values in the Karoubi envelope of
`D_comp(X_ét, E)`: the extension to Karoubi envelopes of
`AlgebraicGeometry.Etale.rightDerivedLowerStarDerivedCompleteRational`. -/
noncomputable def Etale.rightDerivedLowerStarBoundedConstructibleRational {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    Etale.DerivedCategoryBoundedConstructibleRational l E Y ⥤
      Idempotents.Karoubi (DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E) :=
  (Idempotents.functorExtension₂ _ _).obj
    ((Etale.DerivedCategory.boundedConstructibleRational l E Y).ι ⋙
      Etale.rightDerivedLowerStarDerivedCompleteRational l E f)

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, rational stage `E`: the direct image `Ri_*`
along a closed immersion is fully faithful on `Dᵇc(Z, E)`, the Karoubi envelope of the
rationalization of `Dᵇc(Z, 𝒪_E)`. It is the Karoubi extension of the functor induced on
rationalizations by the integral `Ri_*`, which is fully faithful because the integral `Ri_*`
is (`CategoryTheory.Rationalization.full_map`), and Karoubi extension preserves full faithfulness
(`CategoryTheory.Idempotents.full_functorExtension₂_obj`). -/
instance Etale.full_rightDerivedLowerStarBoundedConstructibleRational :
    (Etale.rightDerivedLowerStarBoundedConstructibleRational l E i).Full := by
  unfold Etale.rightDerivedLowerStarBoundedConstructibleRational
  infer_instance

instance Etale.faithful_rightDerivedLowerStarBoundedConstructibleRational :
    (Etale.rightDerivedLowerStarBoundedConstructibleRational l E i).Faithful := by
  unfold Etale.rightDerivedLowerStarBoundedConstructibleRational
  infer_instance

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the rational stage: for any
right adjoint `Ri^!` of the corestriction of `Ri_* : Dᵇc(Z, E) ⥤ Karoubi D_comp(X_ét, E)` to a full
subcategory `P` (for instance `Dᵇc(X, E)`), the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism. -/
theorem Etale.isIso_unit_app_boundedConstructibleRational
    {P : ObjectProperty (Idempotents.Karoubi
      (DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E))}
    (h : ∀ K, P ((Etale.rightDerivedLowerStarBoundedConstructibleRational l E i).obj K))
    {G : P.FullSubcategory ⥤ Etale.DerivedCategoryBoundedConstructibleRational l E Z}
    (adj : P.lift _ h ⊣ G) (Q : Etale.DerivedCategoryBoundedConstructibleRational l E Z) :
    IsIso (adj.unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift h adj Q

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the integral stage on
`Dᵇc(Z, 𝒪_E)`: for any right adjoint `Ri^!` of the corestriction of `Ri_*` to a full subcategory `P`
(for instance `Dᵇc(X, 𝒪_E)`), the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism. -/
theorem Etale.isIso_unit_app_boundedConstructibleIntegral
    {P : ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))}
    (h : ∀ K, P (((Etale.DerivedCategory.boundedConstructibleIntegral
      (PadicAlgCl.maximalIdealShrink l E) Z).ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
          i).rightDerivedFunctor).obj K))
    {G : P.FullSubcategory ⥤ (Etale.DerivedCategory.boundedConstructibleIntegral
      (PadicAlgCl.maximalIdealShrink l E) Z).FullSubcategory}
    (adj : P.lift _ h ⊣ G) (Q : (Etale.DerivedCategory.boundedConstructibleIntegral
      (PadicAlgCl.maximalIdealShrink l E) Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift h adj Q

instance ProEtale.full_adicLowerStar : (ProEtale.adicLowerStar l i).Full :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.full

instance ProEtale.faithful_adicLowerStar : (ProEtale.adicLowerStar l i).Faithful :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.faithful

/-- Algebraically closed coefficient category.

The stage `ℚ̄_ℓ` of `Dᵇc(X, ℚ̄_ℓ)`: bounded complexes of sheaves of modules over the
constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` with constructible cohomology sheaves
(`AlgebraicGeometry.ProEtale.adicConstructibleSheaf`), the `2`-colimit over finite `E ⊆ ℚ̄_ℓ`
realised in the Bhatt–Scholze model. -/
abbrev ProEtale.DerivedCategory.boundedConstructibleAdic (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (ProEtale.AdicSheaf l X)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (ProEtale.adicConstructibleSheaf l X)

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, stage `ℚ̄_ℓ`: the direct image `Ri_*` along
a closed immersion is fully faithful on `Dᵇc(Z, ℚ̄_ℓ)`. The `ℓ`-adic `i_*` is fully faithful, its
counit being an isomorphism, and preserves K-injective complexes, so its right derived functor is
fully faithful. -/
instance ProEtale.full_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructibleAdic l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor).Full :=
  inferInstance

instance ProEtale.faithful_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructibleAdic l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor).Faithful :=
  inferInstance

/-- Blueprint `lemma-local-cohomology-right-adjoint--1`, the unit at the stage `ℚ̄_ℓ`: for any right
adjoint `Ri^!` of the corestriction of `Ri_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ D(X_proét, ℚ̄_ℓ)` to a full
subcategory `P` (for instance `Dᵇc(X, ℚ̄_ℓ)`), the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism. -/
theorem ProEtale.isIso_unit_app_boundedConstructibleAdic
    {P : ObjectProperty (DerivedCategory (ProEtale.AdicSheaf l X))}
    (h : ∀ K, P (((ProEtale.DerivedCategory.boundedConstructibleAdic l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor).obj K))
    {G : P.FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory}
    (adj : P.lift _ h ⊣ G)
    (Q : (ProEtale.DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift h adj Q

end BoundedConstructible

end AlgebraicGeometry
