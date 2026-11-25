/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Extension by zero along a weakly étale morphism on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `g : V ⟶ U` a weakly étale morphism of schemes.
This file lifts the extension by zero `g_!` on abelian pro-étale sheaves
(`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriek`) to the categories `Mod_{Λ_X}` of module
objects over `Λ_X = p_X^* Λ`, as an exact left adjoint of the pullback `g^*` on module objects.
This is the weakly étale counterpart of the extension by zero along an open immersion of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.

* By the projection formula
  (`AlgebraicGeometry.ProEtale.hasProjectionFormula_weaklyEtaleLowerShriekAdjunction`), `g_!`
  lifts to a *linear* extension by zero `Mod_{g^* Λ_U} ⥤ Mod_{Λ_U}`
  (`ProEtale.CondensedRing.linearWeaklyEtaleLowerShriek`), left adjoint to `mapMod(g^*)`.
* The extension by zero on module objects is the restriction of scalars along
  `α_g : g^* Λ_U ⟶ Λ_V` followed by the linear extension by zero
  (`ProEtale.CondensedRing.weaklyEtaleLowerShriek`). It is exact, and left adjoint to `g^*` on
  module objects (`ProEtale.CondensedRing.weaklyEtaleLowerShriekUpperStarAdjunction`), since
  `α_g` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {V U : Scheme.{u}} (g : V ⟶ U) [WeaklyEtale g]

/-- The *linear* extension by zero `Mod_{g^* Λ_U} ⥤ Mod_{Λ_U}` along a weakly étale
`g : V ⟶ U`: the lift of the extension by zero `g_!` on abelian sheaves to module objects
through the projection formula, sending `M` to `g_! M` with the `Λ_U`-action
`Λ_U ⊗ g_! M ≅ g_!(g^* Λ_U ⊗ M) ⟶ g_! M`. -/
noncomputable def linearWeaklyEtaleLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ U)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) :=
  (ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).mapModLeft (condensedRingObj Λ U)

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of the linear extension by zero is the extension by zero. -/
lemma linearWeaklyEtaleLowerShriek_comp_forget :
    linearWeaklyEtaleLowerShriek Λ g ⋙ Mod.forget (condensedRingObj Λ U) =
      Mod.forget _ ⋙ ProEtale.weaklyEtaleLowerShriek Ab.{u + 1} g := rfl

/-- The linear extension by zero is left adjoint to the transport `mapMod(g^*)` of module
objects along the strong monoidal `g^*`. -/
noncomputable def linearWeaklyEtaleLowerShriekAdjunction :
    linearWeaklyEtaleLowerShriek Λ g ⊣ (g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ U) :=
  (ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).mapModLeftAdjunction

instance linearWeaklyEtaleLowerShriek_additive : (linearWeaklyEtaleLowerShriek Λ g).Additive :=
  inferInstanceAs ((ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).mapModLeft
    (condensedRingObj Λ U)).Additive

/-- The linear extension by zero is left exact, since the extension by zero on abelian sheaves
is. -/
instance preservesFiniteLimits_linearWeaklyEtaleLowerShriek :
    PreservesFiniteLimits (linearWeaklyEtaleLowerShriek Λ g) :=
  inferInstanceAs (PreservesFiniteLimits
    ((ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).mapModLeft
      (condensedRingObj Λ U)))

/-- The linear extension by zero is right exact. -/
instance preservesFiniteColimits_linearWeaklyEtaleLowerShriek :
    PreservesFiniteColimits (linearWeaklyEtaleLowerShriek Λ g) :=
  inferInstanceAs (PreservesFiniteColimits
    ((ProEtale.weaklyEtaleLowerShriekAdjunction Ab.{u + 1} g).mapModLeft
      (condensedRingObj Λ U)))

/-- The extension by zero `g_! : Mod_{Λ_V} ⥤ Mod_{Λ_U}` along a weakly étale `g : V ⟶ U` on
module objects over `Λ`: the restriction of scalars along `α_g : g^* Λ_U ⟶ Λ_V` followed by the
linear extension by zero. Its underlying sheaf is the extension by zero `g_! M` of the
underlying sheaf. -/
noncomputable def weaklyEtaleLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V) ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) :=
  Mod.comap (condensedPullbackHom Λ g) ⋙ linearWeaklyEtaleLowerShriek Λ g

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of the extension by zero on module objects is the extension by zero
of the underlying sheaf. -/
lemma weaklyEtaleLowerShriek_comp_forget :
    weaklyEtaleLowerShriek Λ g ⋙ Mod.forget (condensedRingObj Λ U) =
      Mod.forget (condensedRingObj Λ V) ⋙ ProEtale.weaklyEtaleLowerShriek Ab.{u + 1} g := rfl

instance weaklyEtaleLowerShriek_additive : (weaklyEtaleLowerShriek Λ g).Additive := by
  unfold weaklyEtaleLowerShriek
  infer_instance

/-- The extension by zero on module objects along a weakly étale morphism is left exact. -/
instance preservesFiniteLimits_weaklyEtaleLowerShriek :
    PreservesFiniteLimits (weaklyEtaleLowerShriek Λ g) := by
  unfold weaklyEtaleLowerShriek
  exact comp_preservesFiniteLimits _ _

/-- The extension by zero on module objects along a weakly étale morphism is right exact. -/
instance preservesFiniteColimits_weaklyEtaleLowerShriek :
    PreservesFiniteColimits (weaklyEtaleLowerShriek Λ g) := by
  unfold weaklyEtaleLowerShriek
  exact comp_preservesFiniteColimits _ _

/-- The extension by zero on module objects along a weakly étale morphism is exact. -/
instance preservesHomology_weaklyEtaleLowerShriek :
    (weaklyEtaleLowerShriek Λ g).PreservesHomology := {}

/-- The adjunction `g_! ⊣ g^*` on module objects along a weakly étale morphism: the adjunction
`linear g_! ⊣ mapMod(g^*)` composed with the adjunction `Res_{α_g} ⊣ Coext_{α_g}`, and
`Coext_{α_g} ≅ Ext_{α_g}` since `α_g` is an isomorphism. -/
noncomputable def weaklyEtaleLowerShriekUpperStarAdjunction :
    weaklyEtaleLowerShriek Λ g ⊣ (g)^*⟦Λ⟧ :=
  ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ g)).comp
    (linearWeaklyEtaleLowerShriekAdjunction Λ g)).ofNatIsoRight
    (Functor.isoWhiskerLeft ((g)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ U))
      (Mod.extendScalarsIsoCoextendScalars (condensedPullbackHom Λ g)).symm)

instance : (weaklyEtaleLowerShriek Λ g).IsLeftAdjoint :=
  (weaklyEtaleLowerShriekUpperStarAdjunction Λ g).isLeftAdjoint

end AlgebraicGeometry.ProEtale.CondensedRing
