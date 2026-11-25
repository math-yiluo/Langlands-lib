/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Extension by zero along an étale morphism

Let `v : W ⟶ X` be étale. The extension by zero `v_! M` of an `A`-valued sheaf `M` on
`W_ét` is the sheafification of the presheaf

`V ↦ ⨁_{s ∈ Hom_X(V, W)} M(V, s)`

on `X_ét`, that is, the left Kan extension along the localization functor `W_ét ⟶ X_ét`
followed by sheafification. It is left adjoint to the pullback `v^*`, which for an étale `v`
is restriction. When `v` is an open immersion there is at most one lift `s`, and `v_!` is the
extension by zero `AlgebraicGeometry.Etale.openImmersionLowerShriek`.

At a geometric point `x̄` of `X` one has `(v_! M)_x̄ = ⨁_{w̄ ∈ W_x̄} M_w̄`, so `v_!` is exact;
consequently `v^*` preserves injective sheaves.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriek`: the extension by zero `v_!`.
- `AlgebraicGeometry.Etale.etaleLowerShriekUpperStarAdjunction`: the adjunction `v_! ⊣ v^*`.

## Main statements

- `AlgebraicGeometry.Etale.preservesFiniteLimits_etaleLowerShriek`: `v_!` is exact.
- `AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale`: `v^*` preserves injectives.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {W X : Scheme.{u}} (v : W ⟶ X) (h : Etale v)

/-- **Extension by zero along an étale morphism** `v : W ⟶ X`, on `A`-valued sheaves: the
sheafification of the presheaf `V ↦ ⨁_{s ∈ Hom_X(V, W)} M(V, s)` on `X_ét`, that is, the left
Kan extension along the localization functor `W_ét ⟶ X_ét` followed by sheafification.
(blueprint: `lemma-acyclicity-pulled-back-injectives`) -/
noncomputable def Etale.etaleLowerShriek :
    Sheaf W.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h)
    A W.smallEtaleTopology X.smallEtaleTopology

/-- The adjunction `v_! ⊣ v^*` for an étale `v`: maps from the defining presheaf of `v_! M`
to a sheaf `N` are compatible families of maps `M(V, s) ⟶ N(V)`, that is maps `M ⟶ v^* N`. -/
noncomputable def Etale.etaleLowerShriekUpperStarAdjunction :
    Etale.etaleLowerShriek A v h ⊣ (v)^*[A] :=
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous W.smallEtaleTopology
      X.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (W.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale))
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A W.smallEtaleTopology X.smallEtaleTopology).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction A v h).symm

end General

variable (Λ : Type (u + 1)) [CommRing Λ] {W X : Scheme.{u}} (v : W ⟶ X) (h : Etale v)

/-- **Extension by zero along an étale morphism is exact.** Left exactness is the content;
right exactness holds for every left adjoint. On presheaves, `v_!` sends `M` to
`V ↦ ⨁_{s ∈ Hom_X(V, W)} M(V, s)`, which is left exact because direct sums of modules are
exact (`AlgebraicGeometry.SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian`),
and sheafification is left exact. -/
instance Etale.preservesFiniteLimits_etaleLowerShriek :
    PreservesFiniteLimits (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h) := by
  have heq : Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h =
      sheafToPresheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (MorphismProperty.Over.map ⊤ h).op.lan ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    rfl
  have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (W.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤ X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian _ h
  rw [heq]
  exact comp_preservesFiniteLimits _ _

/-- **Étale restriction preserves injectives**: for an étale `v : W ⟶ X`, the pullback `v^*`
sends injective sheaves of `Λ`-modules to injective sheaves, since it has the exact left
adjoint `v_!` (`AlgebraicGeometry.Etale.etaleLowerShriekUpperStarAdjunction`,
`AlgebraicGeometry.Etale.preservesFiniteLimits_etaleLowerShriek`).
(blueprint: `lemma-acyclicity-pulled-back-injectives`) -/
theorem Etale.injective_upperStar_obj_of_etale [Etale v]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    Injective ((v)^*[ModuleCat.{u + 1} Λ].obj I) := by
  have := Etale.preservesFiniteLimits_etaleLowerShriek Λ v inferInstance
  exact (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v
    inferInstance).map_injective I inferInstance

end AlgebraicGeometry
