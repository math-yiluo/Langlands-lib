/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.AlgebraicGeometry.StrictLocalGlobalGermIso
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricFibreStalk

/-!
# Cohomology of geometric fibres of a proper morphism

Let `f : X ⟶ Y` be proper and `ȳ : Spec Ω ⟶ Y` a geometric point (`Ω` separably closed), with
geometric fibre `X_ȳ = X ×_Y Spec Ω` and projection `i : X_ȳ ⟶ X`. For a bounded below complex
`K` of abelian étale sheaves on `X` with torsion cohomology sheaves, the derived stalk of `Rf_* K`
at `ȳ` is the derived global sections `RΓ(X_ȳ, i^* K)` of the restriction of `K` to the fibre
(`AlgebraicGeometry.Etale.sheafFiberRightDerivedLowerStarIsoOfIsProper`). Its degreewise form for
a sheaf of modules over a finite ring is
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isProper`.

## Main statements

- `AlgebraicGeometry.Etale.sheafFiberRightDerivedLowerStarIsoOfIsProper`:
  `(Rf_* K)_ȳ ≅ RΓ(X_ȳ, i^* K)`.
- `AlgebraicGeometry.Etale.cohomology_geometricFibres`: the derived and the degreewise statements.

## Implementation details

The isomorphism applies proper base change (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`)
to the cartesian square of the geometric fibre, so that the stalk of `Rf_* K` at `ȳ` is the stalk
of `R(f_ȳ)_* (i^* K)` at the closed point of `Spec Ω`. Over the strictly local scheme `Spec Ω`,
taking the stalk at the closed point is taking global sections
(`AlgebraicGeometry.Etale.strictLocal_globalGerm_isIso`), and `RΓ(Spec Ω, R(f_ȳ)_* -) = RΓ(X_ȳ, -)`
(`AlgebraicGeometry.Etale.derivedGlobalGerm`).

As for `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`, the statement is
made on the étale site rather than the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive

/-- The closed point `Spec κ(Ω) ⟶ Spec Ω` of the spectrum of a field `Ω`, as an isomorphism. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.specResidueFieldIso (Ω : Type u) [Field Ω] :
    Spec (.of (IsLocalRing.ResidueField Ω)) ≅ Spec (.of Ω) :=
  have : IsIso (CommRingCat.ofHom (IsLocalRing.residue Ω)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨(IsLocalRing.residue Ω).injective, IsLocalRing.residue_surjective⟩
  asIso (Spec.map (CommRingCat.ofHom (IsLocalRing.residue Ω)))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

/-- **Cohomology of geometric fibres**: let `f : X ⟶ Y` be proper, `ȳ : Spec Ω ⟶ Y` a geometric
point with geometric fibre `X_ȳ = X ×_Y Spec Ω` and projection `i : X_ȳ ⟶ X`, and let
`K ∈ D⁺(X_ét)` have torsion cohomology sheaves. Then the derived stalk at `ȳ` of `Rf_* K` is
canonically isomorphic to the derived global sections of `i^* K` on the geometric fibre:
`(Rf_* K)_ȳ ≅ RΓ(X_ȳ, i^* K)`. -/
noncomputable def sheafFiberRightDerivedLowerStarIsoOfIsProper
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.torsionHomology X K) :
    D+((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj K) ≅
      R+(Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (D+((pullback.fst f y)^*[AddCommGrpCat.{u + 1}]).obj K) :=
  let sq := IsPullback.of_hasPullback f y
  let t₀ := (specResidueFieldIso Ω).hom
  have : IsIso (globalGerm t₀) := (strictLocal_globalGerm_isIso (RingHom.id Ω)).2
  have := isIso_derivedGlobalGerm (pullback.snd f y) t₀
  have : IsIso ((baseChange AddCommGrpCat.{u + 1} sq.toCommSq).app K) :=
    isIso_baseChange_of_isProper sq K hK
  have : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) := by
    rwa [← baseChange_eq_derivedBaseChangeMapPlus]
  (Functor.mapDerivedCategoryPlusNatIso (GrothendieckTopology.Point.sheafFiberIso
      (pointSmallEtaleCongr (specResidueFieldIso Ω) y).symm)).app _ ≪≫
    (Functor.mapDerivedCategoryPlusNatIso (upperStarCompSheafFiberIso _ y t₀).symm).app _ ≪≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).app _ ≪≫
    D+((pointSmallEtale t₀).sheafFiber).mapIso
      (asIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)) ≪≫
    (asIso ((derivedGlobalGerm (pullback.snd f y) t₀).app _)).symm

/-- **Cohomology of geometric fibres** of a proper morphism `f : X ⟶ Y` at a geometric point
`ȳ : Spec Ω ⟶ Y`, with geometric fibre `X_ȳ = X ×_Y Spec Ω` and projection `i : X_ȳ ⟶ X`.

1. For `K ∈ D⁺(X_ét)` with torsion cohomology sheaves, `(Rf_* K)_ȳ ≅ RΓ(X_ȳ, i^* K)`.
2. For a sheaf `F` of modules over a finite ring `Λ` and `q ≥ 0`,
   `(Rᵠf_* F)_ȳ ≃ Hᵠ(X_ȳ, i^* F)`. -/
theorem cohomology_geometricFibres :
    (∀ (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.torsionHomology X K →
        Nonempty (D+((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
            (R+((f)_*[AddCommGrpCat.{u + 1}]).obj K) ≅
          R+(Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (D+((pullback.fst f y)^*[AddCommGrpCat.{u + 1}]).obj K))) ∧
    ∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ),
      Nonempty (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
            ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst f y)^*[ModuleCat.{u + 1} Λ].obj F)) q) :=
  ⟨fun K hK ↦ ⟨sheafFiberRightDerivedLowerStarIsoOfIsProper f y K hK⟩,
    fun _ _ _ F q ↦ nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isProper f y F q⟩

end AlgebraicGeometry.Etale
