/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingDetermination
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

/-!
# The localizing categories `Loc(Dbc(X, Λ))` of module objects over `Λ_X`

Let `Λ` be a commutative condensed ring, for instance `𝒪̲_E`, `E̲` or `ℚ̲̄_ℓ`, and for a scheme `X`
let `D(X_proét, Λ) = D(Mod_{Λ_X})` be the derived category of module objects over
`Λ_X = p_X^* Λ` (`WeilConjectures.SixFunctors.ProEtale.ModuleObject`). This file is about the
localizing closure `Loc(Dbc(X, Λ))` of the bounded constructible complexes, defined in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing`
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`, blueprint
`definition-localizing-subcategory`; for `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` one has `Dctf(X, Λ) = Dbc(X, Λ)`),
the projection map and the base change map of the ambient categories, and the formal arguments of
blueprint `proposition-projection-formula-rational-coefficients` and
`lemma-projection-formula-integral-coefficients` extending the projection formula and the tensor
closure from `Dbc` to `Loc(Dbc)`.

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.projectionMap Λ p`: the projection map
  `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` on `D(Mod_{Λ_Y})`.
- `AlgebraicGeometry.ProEtale.CondensedRing.baseChangeMap Λ sq`: the base change map
  `Lg^* Rp_* ⟶ Rp'_* Lg'^*` of a commutative square, on the ambient derived categories.

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible_tensor`: if
  `Dbc(X, Λ)` is closed under `⊗ᴸ`, so is `Loc(Dbc(X, Λ))`.
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMap_of_localizingBoundedConstructible`:
  if the projection formula holds on `Dbc`, `Rp_*` maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))`
  preserving direct sums there, and the categories `Loc(Dbc)` are closed under `⊗ᴸ`, then the
  projection formula holds on `Loc(Dbc)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The localizing closure of `Dbc` -/

omit [IsCommMonObj Λ] in
lemma le_localizingBoundedConstructible (X : Scheme.{u}) :
    boundedConstructible (condensedRingObj Λ X) ≤ localizingBoundedConstructible Λ X :=
  ObjectProperty.le_localizingClosure _

instance (X : Scheme.{u}) : (localizingBoundedConstructible Λ X).IsLocalizing :=
  inferInstanceAs ((boundedConstructible _).localizingClosure).IsLocalizing

/-! ### Shifts and direct sums -/

section Shift

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback `Lf^*` commutes with the shifts, being isomorphic to the functor
`D(f^*)` induced by the exact pullback
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable instance commShift_leftDerivedUpperStar : (L((f)^*⟦Λ⟧)).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The derived pushforward `Rf_*` commutes with the shifts, as the right adjoint of `Lf^*`.
This structure (rather than the one transported from K-injective complexes) is the one for
which the adjunction `Lf^* ⊣ Rf_*` commutes with the shifts. -/
noncomputable instance commShift_rightDerivedLowerStar : (R((f)_*⟦Λ⟧)).CommShift ℤ :=
  (derivedUpperStarLowerStarAdjunction Λ f).rightAdjointCommShift ℤ

instance commShift_derivedUpperStarLowerStarAdjunction :
    (derivedUpperStarLowerStarAdjunction Λ f).CommShift ℤ :=
  (derivedUpperStarLowerStarAdjunction Λ f).commShift_of_leftAdjoint ℤ

instance isTriangulated_leftDerivedUpperStar : (L((f)^*⟦Λ⟧)).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
  exact Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

instance isTriangulated_rightDerivedLowerStar : (R((f)_*⟦Λ⟧)).IsTriangulated :=
  (derivedUpperStarLowerStarAdjunction Λ f).isTriangulated_rightAdjoint

/-- The counit `Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` of the derived pullback commutes with the shifts. -/
instance commShift_leftDerivedFunctorCounit_upperStar :
    NatTrans.CommShift (f)^*⟦Λ⟧.leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.inv ℤ)
  rw [← (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ≫ _) ℤ)

/-- The derived pullback preserves direct sums, being a left adjoint. -/
instance preservesColimitsOfShape_leftDerivedUpperStar (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) L((f)^*⟦Λ⟧) :=
  have : PreservesColimitsOfSize.{u + 1, u + 1} L((f)^*⟦Λ⟧) :=
    (derivedUpperStarLowerStarAdjunction Λ f).leftAdjoint_preservesColimits
  inferInstance

end Shift

section Tensor

variable {X : Scheme.{u}}

/-- The derived tensor product `K ⊗ᴸ -` preserves direct sums, being left adjoint to
`RHom(K, -)`. -/
instance preservesColimitsOfShape_tensorLeft (K : 𝔻(X)) (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) ((curriedTensor 𝔻(X)).obj K) :=
  have : PreservesColimitsOfSize.{u + 1, u + 1} ((curriedTensor 𝔻(X)).obj K) :=
    (derivedTensorHomAdjunction Λ K).leftAdjoint_preservesColimits
  inferInstance

/-- The derived tensor product `- ⊗ᴸ K` preserves direct sums, being isomorphic to `K ⊗ᴸ -`
through the braiding. -/
lemma preservesCoproductsOn_tensorRight (K : 𝔻(X)) (P : ObjectProperty 𝔻(X)) :
    ((curriedTensor 𝔻(X)).flip.obj K).PreservesCoproductsOn.{u + 1} P := by
  obtain ⟨β⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  exact (Functor.preservesCoproductsOn_of_preservesColimitsOfShape
    ((curriedTensor 𝔻(X)).obj K) P).of_iso (G := (curriedTensor 𝔻(X)).flip.obj K)
    (NatIso.ofComponents (fun M ↦ @BraidedCategory.braiding _ _ _ β K M)
      (fun f ↦ @BraidedCategory.braiding_naturality_right _ _ _ β K _ _ f))

/-- Blueprint `proposition-projection-formula-rational-coefficients--1` (2), for an arbitrary
condensed ring `Λ`: if the bounded constructible complexes `Dbc(X, Λ)` are closed under `⊗ᴸ`, so is
`Loc(Dbc(X, Λ))`. Fixing `B` in `Dbc(X, Λ)`, the objects `A` of `Loc(Dbc(X, Λ))` with
`A ⊗ᴸ B ∈ Loc(Dbc(X, Λ))` form a localizing subcategory containing `Dbc(X, Λ)`, `- ⊗ᴸ B` being exact
and preserving direct sums; then fix `A` in `Loc(Dbc(X, Λ))` and argue in `B`
(`CategoryTheory.ObjectProperty.localizingClosure_map₂`). -/
theorem localizingBoundedConstructible_tensor
    (h : ∀ A B : 𝔻(X), boundedConstructible (condensedRingObj Λ X) A →
      boundedConstructible (condensedRingObj Λ X) B →
        boundedConstructible (condensedRingObj Λ X) (A ⊗ B))
    {A B : 𝔻(X)} (hA : localizingBoundedConstructible Λ X A)
    (hB : localizingBoundedConstructible Λ X B) :
    localizingBoundedConstructible Λ X (A ⊗ B) :=
  ObjectProperty.localizingClosure_map₂ _ _ _ (curriedTensor 𝔻(X))
    (fun Y _ ↦ preservesCoproductsOn_tensorRight Λ Y _)
    (fun _ _ ↦ Functor.preservesCoproductsOn_of_preservesColimitsOfShape _ _)
    (fun A' B' hA' hB' ↦ le_localizingBoundedConstructible Λ X _ (h A' B' hA' hB')) hA hB

end Tensor

/-! ### The projection map and the base change map -/

section ProjectionMap

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of module objects over `Λ`, natural in
`M : D(X_proét, Λ)` and `L : D(Y_proét, Λ)`: the right adjoint projection map
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) of the adjunction `Lp^* ⊣ Rp_*` and of
the tensor comparison `Lp^*(K ⊗ᴸ L) ⟶ Lp^*K ⊗ᴸ Lp^*L`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`). Its transpose along
`Lp^* ⊣ Rp_*` is `Lp^*(Rp_*M ⊗ᴸ L) ⟶ Lp^*Rp_*M ⊗ᴸ Lp^*L ⟶ M ⊗ᴸ Lp^*L`. -/
noncomputable def projectionMap :
    R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y) ⟶
      (Functor.postcompose₂.obj R((p)_*⟦Λ⟧)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*⟦Λ⟧)).obj (curriedTensor 𝔻(X))) :=
  (derivedUpperStarLowerStarAdjunction Λ p).rightAdjointProjectionMap
    (leftDerivedUpperStarTensor Λ p)

lemma projectionMap_app_app (M : 𝔻(X)) (L : 𝔻(Y)) :
    ((projectionMap Λ p).app M).app L =
      (derivedUpperStarLowerStarAdjunction Λ p).homEquiv _ _
        (((leftDerivedUpperStarTensor Λ p).app (R((p)_*⟦Λ⟧).obj M)).app L ≫
          ((curriedTensor 𝔻(X)).map ((derivedUpperStarLowerStarAdjunction Λ p).counit.app M)).app
            (L((p)^*⟦Λ⟧).obj L)) :=
  rfl

/-! The two sides of the projection map are triangulated in each variable. -/

noncomputable instance (M : 𝔻(X)) :
    ((R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y)).obj M).CommShift ℤ :=
  inferInstanceAs (Functor.CommShift ((curriedTensor 𝔻(Y)).obj (R((p)_*⟦Λ⟧).obj M)) ℤ)

instance (M : 𝔻(X)) : ((R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y)).obj M).IsTriangulated :=
  inferInstanceAs (Functor.IsTriangulated ((curriedTensor 𝔻(Y)).obj (R((p)_*⟦Λ⟧).obj M)))

noncomputable instance (L : 𝔻(Y)) :
    ((R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y)).flip.obj L).CommShift ℤ :=
  inferInstanceAs (Functor.CommShift (R((p)_*⟦Λ⟧) ⋙ (curriedTensor 𝔻(Y)).flip.obj L) ℤ)

instance (L : 𝔻(Y)) : ((R((p)_*⟦Λ⟧) ⋙ curriedTensor 𝔻(Y)).flip.obj L).IsTriangulated :=
  inferInstanceAs (Functor.IsTriangulated (R((p)_*⟦Λ⟧) ⋙ (curriedTensor 𝔻(Y)).flip.obj L))

noncomputable instance (M : 𝔻(X)) : (((Functor.postcompose₂.obj R((p)_*⟦Λ⟧)).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*⟦Λ⟧)).obj
      (curriedTensor 𝔻(X)))).obj M).CommShift ℤ :=
  inferInstanceAs
    (Functor.CommShift ((L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj M) ⋙ R((p)_*⟦Λ⟧)) ℤ)

instance (M : 𝔻(X)) : (((Functor.postcompose₂.obj R((p)_*⟦Λ⟧)).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*⟦Λ⟧)).obj
      (curriedTensor 𝔻(X)))).obj M).IsTriangulated :=
  inferInstanceAs
    (Functor.IsTriangulated ((L((p)^*⟦Λ⟧) ⋙ (curriedTensor 𝔻(X)).obj M) ⋙ R((p)_*⟦Λ⟧)))

noncomputable instance (L : 𝔻(Y)) : (((Functor.postcompose₂.obj R((p)_*⟦Λ⟧)).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*⟦Λ⟧)).obj
      (curriedTensor 𝔻(X)))).flip.obj L).CommShift ℤ :=
  inferInstanceAs (Functor.CommShift
    ((curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj L) ⋙ R((p)_*⟦Λ⟧)) ℤ)

instance (L : 𝔻(Y)) : (((Functor.postcompose₂.obj R((p)_*⟦Λ⟧)).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((p)^*⟦Λ⟧)).obj
      (curriedTensor 𝔻(X)))).flip.obj L).IsTriangulated :=
  inferInstanceAs (Functor.IsTriangulated
    ((curriedTensor 𝔻(X)).flip.obj (L((p)^*⟦Λ⟧).obj L) ⋙ R((p)_*⟦Λ⟧)))

end ProjectionMap

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*` of a commutative square
`g' ≫ p = p' ≫ g` of schemes, on the ambient derived categories of module objects, obtained from
the composition isomorphisms `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp`
and the commutativity of the square. -/
noncomputable def pullbackSquareComparison (sq : CommSq g' p' p g) :
    L((g)^*⟦Λ⟧) ⋙ L((p')^*⟦Λ⟧) ≅ L((p)^*⟦Λ⟧) ⋙ L((g')^*⟦Λ⟧) :=
  (leftDerivedUpperStarComp Λ p' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' p

/-- The base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` of a commutative square `g' ≫ p = p' ≫ g` of
schemes, on the ambient derived categories `D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_{Y'}})`: the unit of
`Lp'^* ⊣ Rp'_*`, followed by the pullback comparison `Lp'^* Lg^* ≅ Lg'^* Lp^*` and by the counit of
`Lp^* ⊣ Rp_*` (`CategoryTheory.Adjunction.exchangeRight`). -/
noncomputable def baseChangeMap (sq : CommSq g' p' p g) :
    R((p)_*⟦Λ⟧) ⋙ L((g)^*⟦Λ⟧) ⟶ L((g')^*⟦Λ⟧) ⋙ R((p')_*⟦Λ⟧) :=
  Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
