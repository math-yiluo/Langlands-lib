/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!

# Orientations and the dual of a perfect complex

Let `Λ` be a finite coefficient ring carrying a Tate twist datum (`HasTateTwist Λ`), with
twisting objects `Λ_X(d) = tateObject Λ X d`. For a smooth separated morphism `f : X ⟶ Y` of
finite type and of pure relative dimension `d`, *smooth purity* provides a canonical isomorphism
`Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`, that is `Λ_X(d)[2d] ≅ Rf^! Λ_Y`. It is
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`
(`proposition-smooth-purity-finite-coefficients`), which gives orientations through
`AlgebraicGeometry.Etale.Orientation.nonempty`. What is recorded in this file is the interface it
produces, packaged as a structure `AlgebraicGeometry.Etale.Orientation`, together with the two
consequences the six-functor formalism uses: for the structure morphism `a : X ⟶ S` an orientation
reads `ω_X ≅ Λ_X(d)[2d]`, and substituting that into `𝔻_X = RHom(-, ω_X)` turns the Verdier dual of
a perfect complex into its coefficient dual, twisted and shifted.

## Main definitions

- `AlgebraicGeometry.Etale.Orientation`: the interface record of an orientation of relative
  dimension `d`, namely the smoothness of `f` together with `Λ_X(d)[2d] ≅ Rf^! Λ_Y` for the
  Tate twist `Λ_X(d)`.
- `AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`: the orientation given by an
  isomorphism `Λ_X(d)[2d] ≅ ω_X` for a smooth `a` of relative dimension `d`.
- `AlgebraicGeometry.Etale.Orientation.twistShiftIso` (`rem-ptr-sf-orientation-2`): the purity
  isomorphism in the twist conventions of `definition-tate-twists`,
  `(twistShift Λ X d).obj Λ_X ≅ Rf^! Λ_Y`.
- `AlgebraicGeometry.Etale.Orientation.verdierDualIso` (`theorem-poincare-duality--2`): the natural
  isomorphism `θ_f : 𝔻_{X/Y} K = RHom(K, Rf^! Λ_Y) ≅ K^∨ ⊗ᴸ Λ_X(d)[2d]`, the composite of
  `RHom(K, γ_f⁻¹)` and of the twist interchange; it is the case `T = Λ_X(d)[2d]` of
  `AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor`, defined for any
  `γ : T ≅ Rf^! Λ_Y` with `T` invertible.
- `AlgebraicGeometry.Etale.Orientation.verdierDualEquivalence` (`theorem-poincare-duality--2`): the
  anti-equivalence of the perfect objects given by `𝔻_{X/Y}`.
- `AlgebraicGeometry.Etale.Orientation.verdierDualVerdierDualIso`: the isomorphism
  `𝔻_{X/Y} 𝔻_{X/Y} K ≅ K^∨∨` induced by `θ_f`.

## Main statements

- `AlgebraicGeometry.Etale.Orientation.nonempty` (`rem-sf-orientation-pointer`): orientations
  are not assumed; smooth purity constructs one for every smooth separated `f` of pure relative
  dimension `d` over a separated scheme locally of finite type over a field.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`
  (`theorem-smooth-purity-all-admissible-coefficients`): for the structure morphism the orientation
  reads `ω_X ≅ Λ_X(d)[2d]`.
- `AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`
  (`theorem-poincare-duality--2`): `𝔻_X K ≅ K^∨(d)[2d]` for a perfect `K`.
- `AlgebraicGeometry.Etale.Orientation.isDualizable_verdierDual`
  (`theorem-poincare-duality--2`): `𝔻_X` preserves the perfect objects.
- `…Etale.Orientation.verdierDualDoubleDual_app_comp_verdierDualVerdierDualIso_hom`
  (`theorem-poincare-duality--2`): under `θ_f` the Verdier biduality `K ⟶ 𝔻_{X/Y} 𝔻_{X/Y} K` is
  the coefficient-dual biduality `K ⟶ K^∨∨`; hence it is an isomorphism for perfect `K`
  (`AlgebraicGeometry.Etale.Orientation.isIso_verdierDualDoubleDual_app_of_isDualizable`).
- `AlgebraicGeometry.Etale.whiskerLeft_verdierDualIsoCoefficientDualTensor_hom_app_comp`
  (`theorem-poincare-duality--2`): `θ` is compatible with the evaluations. The compatibility with a
  change of coefficients is `CategoryTheory.MonoidalClosed.map_ihomIsoIhomUnitTensor_hom`, and
  the pro-étale coefficient stages are
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect`.
- `AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor_hom_app_shift`
  (`theorem-poincare-duality--2`): `θ` commutes with shifts, `θ_{K⟦n⟧} = θ_K⟦-n⟧` under
  `AlgebraicGeometry.Etale.ihomShiftIso` (`RHom(K⟦n⟧, M) ≅ RHom(K, M)⟦-n⟧`).

## Implementation notes

The twist of an orientation is *the* Tate twist `tateObject Λ X d` of the Tate twist datum,
not an arbitrary invertible object: an arbitrary invertible `T` with `T[2d] ≅ Rf^! Λ_Y` exists
for every `d` as soon as `Rf^! Λ_Y` is invertible (take `T = Rf^! Λ_Y [-2d]`), so it would record
neither `d` nor the twist. The unit `Lf^* Λ_Y ≅ Λ_X` is left out of the purity isomorphism: it
is always invertible, and leaving it out keeps the field free of the comparison between `⊗` and
`AlgebraicGeometry.Etale.derivedTensor`. Likewise `f` is required to be smooth of relative
dimension `d`. Constructions that only use the shape of the purity isomorphism, such as the
derived Poincaré pairing of `WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing`, take
an isomorphism `T⟦2d⟧ ≅ ω_X` as an argument instead.

Perfectness is `CategoryTheory.IsDualizable`; see the implementation note of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect`.

The general biduality of the Verdier dual on `Dctf(X, Λ)` is
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual` of
`WeilConjectures.SixFunctors.Etale.Derived.Dualizing`; for perfect objects and an oriented
morphism it is proved here, without the constructibility hypotheses.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section InvertibleDualizingComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X : Scheme.{u}} {ω T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
  (γ : T ≅ ω) (hT : IsInvertible T)

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

For an isomorphism `γ : T ≅ ω_X` from an invertible complex `T` (for an orientation,
`T = Λ_X(d)[2d]`), the natural isomorphism
```
  θ_K : 𝔻_X K = RHom(K, ω_X) ≅ RHom(K, T) ≅ K^∨ ⊗ᴸ T,
```
the composite of `RHom(K, γ⁻¹)` and of the twist interchange
`AlgebraicGeometry.Etale.DerivedCategory.derivedHomIsoCoefficientDualTensor`
(`AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor_app`). The results of this section are
stated for an arbitrary object `ω` in place of the dualizing complex `ω_X`: for a finite
coefficient ring `Λ` and `ω = ω_X`, `RHom(-, ω)` is `AlgebraicGeometry.Etale.verdierDual` and the
double-dual map is `AlgebraicGeometry.Etale.verdierDualDoubleDual`. -/
noncomputable def verdierDualIsoCoefficientDualTensor :
    (RHom(X)[A]).flip.obj ω ≅
      DerivedCategory.coefficientDual A X ⋙ (derivedTensor A X).flip.obj T :=
  MonoidalClosed.ihomFlipIsoIhomUnitTensor γ hT

/-- The component of `θ` at `K` is `RHom(K, γ⁻¹)` followed by the twist interchange
`RHom(K, T) ≅ K^∨ ⊗ᴸ T`. -/
lemma verdierDualIsoCoefficientDualTensor_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (verdierDualIsoCoefficientDualTensor γ hT).app (op K) =
      (RHom(X)[A].obj (op K)).mapIso γ.symm ≪≫
        DerivedCategory.derivedHomIsoCoefficientDualTensor K hT :=
  rfl

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (compatibility with the
canonical evaluation).

Under `θ_K : 𝔻_X K ≅ K^∨ ⊗ᴸ T` the evaluation `K ⊗ᴸ 𝔻_X K ⟶ ω_X` is the coefficient evaluation
`K ⊗ᴸ K^∨ ⟶ Λ_X` tensored with `T`: the square
```
  K ⊗ᴸ 𝔻_X K ────── K ◁ θ_K ──────→ K ⊗ᴸ (K^∨ ⊗ᴸ T)
       │                                   │
       ev                         α⁻¹, ev_K ▷ T, λ
       ↓                                   ↓
      ω_X ─────────────── γ⁻¹ ────────────→ T
```
commutes. -/
@[reassoc]
lemma whiskerLeft_verdierDualIsoCoefficientDualTensor_hom_app_comp
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ◁ ((verdierDualIsoCoefficientDualTensor γ hT).hom.app (op K)) ≫ (α_ _ _ _).inv ≫
        DerivedCategory.coefficientEvaluation K ▷ T ≫ (λ_ T).hom =
      (ihom.ev K).app (ω) ≫ γ.inv :=
  MonoidalClosed.whiskerLeft_ihomIsoIhomUnitTensor_hom_comp γ hT K

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- The isomorphism `𝔻_X 𝔻_X K ≅ K^∨∨` induced by `θ_K : 𝔻_X K ≅ K^∨ ⊗ᴸ T`
(`CategoryTheory.MonoidalClosed.ihomIhomIsoIhomIhomUnit`). -/
noncomputable def verdierDualVerdierDualIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((RHom(X)[A]).flip.obj ω).obj (op (((RHom(X)[A]).flip.obj ω).obj (op K))) ≅
      (DerivedCategory.coefficientDual A X).obj
        (op ((DerivedCategory.coefficientDual A X).obj (op K))) :=
  MonoidalClosed.ihomIhomIsoIhomIhomUnit γ hT K

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

Under the isomorphism `𝔻_X 𝔻_X K ≅ K^∨∨` induced by `θ`, the double-dual map
`K ⟶ 𝔻_X 𝔻_X K` is the coefficient-dual biduality `K ⟶ K^∨∨`. -/
@[reassoc]
lemma verdierDualDoubleDual_app_comp_verdierDualVerdierDualIso_hom
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedHomToIhomIhomNatTrans A X ω).app K ≫ (verdierDualVerdierDualIso γ hT K).hom =
      (DerivedCategory.coefficientDualDoubleDual _ X).app K :=
  MonoidalClosed.toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom γ hT K

include γ hT in
/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

For a perfect `K` the double-dual map `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_of_isDualizable
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    IsIso ((derivedHomToIhomIhomNatTrans A X ω).app K) :=
  MonoidalClosed.isIso_toIhomIhom_of_isDualizable γ hT hK

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (anti-equivalence).

The Verdier dual `𝔻_X` restricts to an anti-equivalence of the perfect objects of `D(X_ét)`,
its own quasi-inverse, the unit and counit being the double-dual isomorphisms. -/
noncomputable def verdierDualEquivalenceOfIso :
    (ObjectProperty.FullSubcategory
      (IsDualizable (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (IsDualizable (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))) :=
  MonoidalClosed.dualizableIhomEquivalence γ hT

/-- The functor of the anti-equivalence `verdierDualEquivalenceOfIso` is `𝔻_X`. -/
lemma verdierDualEquivalenceOfIso_functor_obj_obj
    (K : (ObjectProperty.FullSubcategory
      (IsDualizable (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))))ᵒᵖ) :
    ((verdierDualEquivalenceOfIso γ hT).functor.obj K).obj =
      ((RHom(X)[A]).flip.obj ω).obj (op K.unop.obj) :=
  rfl

section Shift

variable (X) in
/-- Tensoring on the left with the shifted unit is the shift: `Λ_X⟦n⟧ ⊗ᴸ M ≅ M⟦n⟧`, naturally in
`M`, through the symmetry, the commutation of `M ⊗ᴸ -` with the shift
(`AlgebraicGeometry.Etale.derivedTensorRightShiftIso`) and the right unitor. -/
noncomputable def tensorLeftUnitShiftIso (n : ℤ) :
    tensorLeft ((𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))⟦n⟧) ≅
      shiftFunctor (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) n :=
  BraidedCategory.tensorLeftIsoTensorRight _ ≪≫ derivedTensorRightShiftIso A (𝟙_ _) n ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents (fun M ↦ ρ_ M) (fun f ↦ rightUnitor_naturality f) :
      derivedTensorRight A X (𝟙_ _) ≅ 𝟭 _) _

variable (X) in
/-- The derived hom out of the shifted unit is the opposite shift, `RHom(Λ_X⟦n⟧, M) ≅ M⟦-n⟧`,
naturally in `M`: both are right adjoint to `M ↦ M⟦n⟧ ≅ Λ_X⟦n⟧ ⊗ᴸ M`. -/
noncomputable def ihomUnitShiftIso (n : ℤ) :
    ihom ((𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))⟦n⟧) ≅
      shiftFunctor (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (-n) :=
  (ihom.adjunction _).rightAdjointUniq
    ((shiftEquiv (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) n).toAdjunction
      |>.ofNatIsoLeft
      (tensorLeftUnitShiftIso X n).symm)

/-- The shift as a twist: `K ⊗ᴸ Λ_X⟦n⟧ ≅ (K ⊗ᴸ Λ_X)⟦n⟧ ≅ K⟦n⟧`. -/
noncomputable def tensorUnitShiftIso (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (n : ℤ) : K ⊗ (𝟙_ _)⟦n⟧ ≅ K⟦n⟧ :=
  (derivedTensorRightShiftIso A (𝟙_ _) n).app K ≪≫ (shiftFunctor _ n).mapIso (ρ_ K)

/-- The derived internal hom turns shifts in the first variable into opposite shifts outside:
```
  RHom(K⟦n⟧, M) ≅ RHom(K ⊗ᴸ Λ_X⟦n⟧, M) ≅ RHom(Λ_X⟦n⟧, RHom(K, M)) ≅ RHom(K, M)⟦-n⟧,
```
the composite of `RHom(K ⊗ᴸ Λ_X⟦n⟧ ≅ K⟦n⟧, M)`, of internal currying and of
`AlgebraicGeometry.Etale.ihomUnitShiftIso`. -/
noncomputable def ihomShiftIso (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (n : ℤ) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ihom (K⟦n⟧)).obj M ≅ ((ihom K).obj M)⟦-n⟧ :=
  (MonoidalClosed.internalHom.flip.obj M).mapIso (tensorUnitShiftIso K n).op ≪≫
    MonoidalClosed.ihomCurryIso K _ M ≪≫ (ihomUnitShiftIso X n).app _

/-- Moving the shift out of the left factor of a tensor product with an invertible complex:
```
  M⟦-n⟧ ⊗ᴸ T ≅ RHom(Λ_X⟦n⟧, M) ⊗ᴸ T ≅ RHom(Λ_X⟦n⟧, M ⊗ᴸ T) ≅ (M ⊗ᴸ T)⟦-n⟧,
```
by `AlgebraicGeometry.Etale.ihomUnitShiftIso` and the twist interchange.

This identification is built ad hoc. It is not (yet) known to agree with the canonical
commutation of `⊗ᴸ` with shifts (`AlgebraicGeometry.Etale.derivedTensorShiftIso`,
`AlgebraicGeometry.Etale.commShiftDerivedTensorFlipObj`), since the coherence of the
associator with shifts is not available. The shift compatibility
`AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor_hom_app_shift` is stated relative
to this identification. -/
noncomputable def shiftTensorIsoOfIsInvertible (n : ℤ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    M⟦-n⟧ ⊗ T ≅ (M ⊗ T)⟦-n⟧ :=
  haveI := MonoidalClosed.isIso_ihomTensorToIhom ((𝟙_ _)⟦n⟧) M hT
  whiskerRightIso ((ihomUnitShiftIso X n).app M).symm T ≪≫
    asIso (MonoidalClosed.ihomTensorToIhom _ M T) ≪≫ (ihomUnitShiftIso X n).app _

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (compatibility with
shifts).

The isomorphism `θ_K : 𝔻_X K ≅ K^∨ ⊗ᴸ T` commutes with shifts: under the identifications
`𝔻_X (K⟦n⟧) ≅ (𝔻_X K)⟦-n⟧` and `(K⟦n⟧)^∨ ⊗ᴸ T ≅ K^∨⟦-n⟧ ⊗ᴸ T ≅ (K^∨ ⊗ᴸ T)⟦-n⟧`
(`AlgebraicGeometry.Etale.ihomShiftIso`,
`AlgebraicGeometry.Etale.shiftTensorIsoOfIsInvertible`), `θ_{K⟦n⟧}` is `θ_K⟦-n⟧`. -/
theorem verdierDualIsoCoefficientDualTensor_hom_app_shift
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) :
    (verdierDualIsoCoefficientDualTensor γ hT).hom.app (op (K⟦n⟧)) ≫
        (ihomShiftIso K n (𝟙_ _)).hom ▷ T ≫ (shiftTensorIsoOfIsInvertible hT n _).hom =
      (ihomShiftIso K n (ω)).hom ≫
        ((verdierDualIsoCoefficientDualTensor γ hT).hom.app (op K))⟦-n⟧' := by
  have h₁ := MonoidalClosed.pre_app_comp_ihomIsoIhomUnitTensor_hom γ hT
    (tensorUnitShiftIso K n).hom
  have h₂ := MonoidalClosed.ihomCurry_comp_map_ihomIsoIhomUnitTensor_hom γ hT K
    ((𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))⟦n⟧)
  have h₃ := (ihomUnitShiftIso X n).hom.naturality
    (MonoidalClosed.ihomIsoIhomUnitTensor γ hT K).hom
  have h₄ : (ihomUnitShiftIso X n).hom.app ((ihom K).obj (𝟙_ _)) ▷ T ≫
      (ihomUnitShiftIso X n).inv.app ((ihom K).obj (𝟙_ _)) ▷ T = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight]
  simp only [ihomShiftIso, shiftTensorIsoOfIsInvertible, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, whiskerRightIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, asIso_hom,
    MonoidalClosed.ihomCurryIso_hom, comp_whiskerRight, Category.assoc, Functor.flip_obj_map,
    MonoidalClosed.internalHom_map, Quiver.Hom.unop_op]
  rw [show (verdierDualIsoCoefficientDualTensor γ hT).hom.app (op K) =
      (MonoidalClosed.ihomIsoIhomUnitTensor γ hT K).hom from rfl,
    show (verdierDualIsoCoefficientDualTensor γ hT).hom.app (op (K⟦n⟧)) =
      (MonoidalClosed.ihomIsoIhomUnitTensor γ hT (K⟦n⟧)).hom from rfl,
    reassoc_of% h₄, ← reassoc_of% h₁, ← reassoc_of% h₂, h₃]

end Shift

end InvertibleDualizingComplex

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation: an interface record.

An *orientation* of relative dimension `d` for a separated morphism `f : X ⟶ Y` of finite type
consists of the smoothness of `f`, of pure relative dimension `d`, together with an isomorphism
`γ : Λ_X(d)[2d] ≅ Rf^! Λ_Y`, where `Λ_X(d) = tateObject Λ X d` is the Tate twist. Since
`Lf^* Λ_Y ≅ Λ_X` (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`), this is the
blueprint's `Lf^* Λ_Y (d)[2d] ≅ Rf^! Λ_Y`.

In the blueprint an orientation is **not** an assumption: it is the smooth purity theorem
`proposition-smooth-purity-finite-coefficients`, which lives in a different blueprint block; see
`AlgebraicGeometry.Etale.Orientation.nonempty` (`rem-sf-orientation-pointer`).
This structure therefore records only the interface that purity produces and that the six
operations consume. The blueprint's naturality in `Y` and its compatibilities with composition,
étale base change, finite reduction, scalar extension and the pro-étale realization concern the
whole family of orientations; they are the conditions of
`AlgebraicGeometry.Etale.OrientationDatum` (`theorem-smooth-purity-all-admissible-coefficients`).

For the structure morphism `f = a_X` the isomorphism reads `ω_X ≅ Λ_X(d)[2d]`; see
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex`. -/
structure Orientation (f : X ⟶ Y) (d : ℕ) [HasCompactification f] where
  /-- The morphism is smooth of pure relative dimension `d`. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension d f
  /-- The purity isomorphism `γ : Λ_X(d)[2d] ≅ Rf^! Λ_Y`. -/
  purity : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ f

variable {Λ}

/-- The twist `Λ_X(d)` of an orientation of relative dimension `d`: the Tate twist
`tateObject Λ X d`. -/
noncomputable abbrev Orientation.twist {f : X ⟶ Y} {d : ℕ} [HasCompactification f]
    (_o : Orientation Λ f d) : DerivedCategoryModule Λ X :=
  tateObject Λ X d

/-- Blueprint `rem-ptr-sf-orientation-2`: Pointer to the properties of
[theorem-smooth-purity-all-admissible-coefficients].

The purity isomorphism of an orientation, read in the Tate twist conventions of
`definition-tate-twists`: the source `Λ_X(d)[2d]` is the twist-and-shift
`(twistShift Λ X d).obj Λ_X = (Λ_X ⊗ Λ_X(d))[2d]` of the constant complex, so that `γ` takes
the form in which smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) states it. -/
noncomputable def Orientation.twistShiftIso {f : X ⟶ Y} {d : ℕ} [HasCompactification f]
    (o : Orientation Λ f d) :
    (twistShift Λ X d).obj (constantComplex Λ X) ≅ dualizingComplex Λ f :=
  twistShiftConstantComplexIso Λ X d ≪≫ o.purity

/-- Blueprint `rem-sf-orientation-pointer`: Where the orientation is constructed.

The orientation datum is not an assumption: for `f : X ⟶ Y` smooth separated of pure relative
dimension `d`, with `Y` separated and locally of finite type over a field `k` and the exponent
of `Λ` invertible on `X`, smooth purity (`proposition-smooth-purity-finite-coefficients`,
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) gives
`Rf^! Λ_Y ≅ Λ_X(d)[2d]`, hence an orientation of `f` of relative dimension `d`. -/
theorem Orientation.nonempty [HasTateTwist.IsNormalized Λ] {d : ℕ} (f : X ⟶ Y)
    [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] :
    Nonempty (Orientation Λ f d) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨⟨inferInstance, (twistShiftConstantComplexIso Λ X d).symm ≪≫ e.symm⟩⟩

variable {S : Scheme.{u}} {d : ℕ} {a : X ⟶ S} [HasCompactification a]

/-- The orientation of a structure morphism `a : X ⟶ S`, smooth of relative dimension `d`,
given by an isomorphism `γ : Λ_X(d)⟦2d⟧ ≅ ω_X`. This is how an orientation in the form
`Λ_X(d)[2d] ≅ ω_X`, as produced by smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), is turned into an
`AlgebraicGeometry.Etale.Orientation`. -/
def Orientation.ofDualizingComplexIso [SmoothOfRelativeDimension d a]
    (γ : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) :
    Orientation Λ a d where
  smoothOfRelativeDimension := inferInstance
  purity := γ

/-- Blueprint `theorem-smooth-purity-all-admissible-coefficients`: Orientation: an interface record.

The special case of the orientation at the structure morphism `a : X ⟶ S`: `Ra^! Λ_S` is by
definition the dualizing complex, so the purity isomorphism reads
```
ω_X ═══ Ra^! Λ_S ≅ Λ_X(d)[2d]
```
the dualizing complex of a smooth `X` of pure relative dimension `d` over `S` is a shifted Tate
twist. -/
theorem Orientation.nonempty_iso_dualizingComplex (o : Orientation Λ a d) :
    Nonempty (dualizingComplex Λ a ≅ (tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  ⟨o.purity.symm⟩

variable (Λ X d) in
omit [Finite Λ] in
/-- The shifted Tate twist `Λ_X(d)[2d]` is invertible. -/
theorem isInvertible_tateObject_shift [HasInvertibleExponent Λ X] :
    IsInvertible ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  DerivedCategory.isInvertible_shift
    ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X d)) _

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

Let `f = a : X ⟶ S` be a morphism admitting a compactification, with an orientation
`γ_f : Λ_X(d)[2d] ≅ Rf^! Λ_S` of relative dimension `d`, and put
`𝔻_{X/S} K = RHom_X(K, Rf^! Λ_S)`. The natural isomorphism
```
  θ_{f,K} : 𝔻_{X/S} K = RHom_X(K, Rf^! Λ_S) ≅ RHom_X(K, Λ_X(d)[2d]) ≅ K^∨ ⊗ᴸ Λ_X(d)[2d],
```
the composite of `RHom_X(K, γ_f⁻¹)` and of the twist interchange
`AlgebraicGeometry.Etale.DerivedCategory.derivedHomIsoCoefficientDualTensor` (see
`AlgebraicGeometry.Etale.verdierDualIsoCoefficientDualTensor_app`). For the structure morphism
`a_X : X ⟶ Spec k` this is `θ_K : 𝔻_X K ≅ K^∨(d)[2d]`. The isomorphism `θ_{f,K}` exists for
every `K`; the subsection's perfectness hypothesis is only needed for the biduality
(`AlgebraicGeometry.Etale.Orientation.isIso_verdierDualDoubleDual_app_of_isDualizable`). -/
noncomputable def Orientation.verdierDualIso [HasInvertibleExponent Λ X] (o : Orientation Λ a d) :
    verdierDual Λ a ≅
      DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) :=
  verdierDualIsoCoefficientDualTensor o.purity (isInvertible_tateObject_shift Λ X d)

/-- The component of `θ_f` at `K` is `RHom_X(K, γ_f⁻¹)` followed by the twist interchange. -/
lemma Orientation.verdierDualIso_app [HasInvertibleExponent Λ X] (o : Orientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    o.verdierDualIso.app (op K) =
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso o.purity.symm ≪≫
        DerivedCategory.derivedHomIsoCoefficientDualTensor K
          (isInvertible_tateObject_shift Λ X d) :=
  rfl

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

Let `a : X ⟶ S` be a structure morphism admitting a compactification, let `o` be an
orientation of `a` of relative dimension `d`, and let `K` be perfect over `Λ_X`, i.e.
dualizable. Substituting `ω_X ≅ Λ_X(d)[2d]` into `𝔻_X K = RHom_X(K, ω_X)` and interchanging
the twist with the internal hom identifies the Verdier dual of `K` with the twisted, shifted
coefficient dual: `𝔻_X K ≅ K^∨(d)[2d]`.

When `[HasInvertibleExponent Λ X]` holds, the component `o.verdierDualIso.app (op K)` of `θ_f`
is such an isomorphism. This statement needs no such hypothesis, because `K` is dualizable. -/
theorem Orientation.nonempty_iso_verdierDual_coefficientDual (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    Nonempty ((verdierDual Λ a).obj (op K) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).obj
          ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)) := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_derivedHom_derivedTensor hK
    ((tateObject Λ X d)⟦(2 * d : ℤ)⟧)
  exact ⟨(RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso o.purity.symm ≪≫ e⟩

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex.

Under an orientation the Verdier dual of a perfect complex is perfect, so that `𝔻_X`
restricts to a contravariant anti-equivalence of the perfect objects. -/
theorem Orientation.isDualizable_verdierDual [HasInvertibleExponent Λ X] (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    IsDualizable ((verdierDual Λ a).obj (op K)) := by
  obtain ⟨e⟩ := o.nonempty_iso_verdierDual_coefficientDual hK
  have hT : IsInvertible (tateObject Λ X d) :=
    (isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X d)
  exact IsDualizable.of_iso e.symm (DerivedCategory.isDualizable_derivedTensor
    (DerivedCategory.isDualizable_coefficientDual hK)
    (DerivedCategory.isDualizable_of_isInvertible (DerivedCategory.isInvertible_shift hT _)))

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (anti-equivalence).

Under an orientation the Verdier dual `𝔻_{X/S} = RHom_X(-, Rf^! Λ_S)` restricts to an
anti-equivalence of the perfect objects of `D(X_ét, Λ)`, its own quasi-inverse; the unit and
the counit are the double-dual isomorphisms
(`AlgebraicGeometry.Etale.Orientation.isIso_verdierDualDoubleDual_app_of_isDualizable`). -/
noncomputable def Orientation.verdierDualEquivalence [HasInvertibleExponent Λ X]
    (o : Orientation Λ a d) :
    (ObjectProperty.FullSubcategory (IsDualizable (C := DerivedCategoryModule Λ X)))ᵒᵖ ≌
      ObjectProperty.FullSubcategory (IsDualizable (C := DerivedCategoryModule Λ X)) :=
  verdierDualEquivalenceOfIso o.purity (isInvertible_tateObject_shift Λ X d)

/-- The isomorphism `𝔻_{X/S} 𝔻_{X/S} K ≅ K^∨∨` induced by `θ_f`. -/
noncomputable def Orientation.verdierDualVerdierDualIso [HasInvertibleExponent Λ X]
    (o : Orientation Λ a d) (K : DerivedCategoryModule Λ X) :
    (verdierDual Λ a).obj
        (op ((verdierDual Λ a).obj (op K))) ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj
        (op ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) :=
  Etale.verdierDualVerdierDualIso o.purity (isInvertible_tateObject_shift Λ X d) K

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

Under the isomorphism `𝔻_{X/S} 𝔻_{X/S} K ≅ K^∨∨` induced by `θ_f`, the double-dual map
`K ⟶ 𝔻_{X/S} 𝔻_{X/S} K` is the coefficient-dual biduality `K ⟶ K^∨∨`. -/
@[reassoc]
lemma Orientation.verdierDualDoubleDual_app_comp_verdierDualVerdierDualIso_hom
    [HasInvertibleExponent Λ X] (o : Orientation Λ a d) (K : DerivedCategoryModule Λ X) :
    (verdierDualDoubleDual Λ a).app K ≫ (o.verdierDualVerdierDualIso K).hom =
      (DerivedCategory.coefficientDualDoubleDual _ X).app K :=
  Etale.verdierDualDoubleDual_app_comp_verdierDualVerdierDualIso_hom _ _ K

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (biduality).

Under an orientation, the double-dual map `K ⟶ 𝔻_{X/S} 𝔻_{X/S} K` of a perfect `K` is an
isomorphism. -/
theorem Orientation.isIso_verdierDualDoubleDual_app_of_isDualizable [HasInvertibleExponent Λ X]
    (o : Orientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : IsDualizable K) :
    IsIso ((verdierDualDoubleDual Λ a).app K) :=
  Etale.isIso_verdierDualDoubleDual_app_of_isDualizable o.purity
    (isInvertible_tateObject_shift Λ X d) hK

end Etale

end AlgebraicGeometry
