/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!

# Lower shriek on module objects over `Λ`

Let `Λ` be a commutative condensed ring. This file defines the extension by zero along open
immersions and the lower shriek along morphisms admitting a compactification on the categories
`Mod_{Λ_X}` of module objects over `Λ_X = p_X^* Λ`, from the corresponding functors on
abelian sheaves and the change of scalars along the canonical coefficient morphisms.

* For an open immersion `j : U ⟶ X`, the extension by zero `j_!` on abelian sheaves is left
  adjoint to the strong monoidal `j^*` and satisfies the projection formula
  `j_!(j^* L ⊗ M) ≅ L ⊗ j_! M` (`ProEtale.CondensedRing.hasProjectionFormula_openImmersion`,
  the geometric input of this file). Hence it lifts to a *linear* extension by zero
  `Mod_{j^* Λ_X} ⥤ Mod_{Λ_X}`, sending `M` to `j_! M` with the `Λ_X`-action
  `Λ_X ⊗ j_! M ≅ j_!(j^* Λ_X ⊗ M) ⟶ j_! M`
  (`ProEtale.CondensedRing.linearOpenImmersionLowerShriek`, the lift
  `Adjunction.mapModLeft` of `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`).
  The extension by zero on module objects over `Λ_U` is the restriction of scalars along
  `α_j : j^* Λ_X ⟶ Λ_U` followed by the linear extension by zero,
  ```
  j_! = (linear j_!) ∘ Res_{α_j}
  ```
  (`ProEtale.CondensedRing.openImmersionLowerShriek`, notation `(j)_!open⟦Λ⟧`). Its
  underlying sheaf is `j_! M`, and it is exact. Since `α_j` is an isomorphism, `j_!` is left
  adjoint to `j^* = Ext_{α_j} ∘ mapMod(j^*)` on module objects
  (`ProEtale.CondensedRing.openImmersionLowerShriekUpperStarAdjunction`): the adjunction
  `linear j_! ⊣ mapMod(j^*)` composed with `Res_{α_j} ⊣ Coext_{α_j}`, and
  `Coext_{α_j} ≅ Ext_{α_j}` for an isomorphism `α_j`.
* For a compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y`, the lower shriek is
  `f_! := i_! ⋙ g_*` (`ProEtale.CondensedRing.compactificationLowerShriek`), and for `f`
  with a chosen compactification `HasCompactification.compactification f` it is
  `ProEtale.CondensedRing.lowerShriek`, notation `(f)_!⟦Λ⟧`, *definitionally* the
  composition for the chosen compactification (`ProEtale.CondensedRing.lowerShriek_eq`).

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`.

## Projection formula

* `ProEtale.CondensedRing.hasProjectionFormula_openImmersion`: the projection formula for the
  extension by zero along an open immersion `j`. The unit of `j_! ⊣ j^*` is an isomorphism since
  `j_!` is fully faithful, and the counit at `L ⊗ j_! M` is an isomorphism via
  `ProEtale.openImmersionLowerShriekTensorIso`; the projection map is composed of these two.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The projection formula for the extension by zero `j_!` along an open immersion on abelian
pro-étale sheaves: the canonical map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. See the
module docstring. -/
instance hasProjectionFormula_openImmersion :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).HasProjectionFormula := by
  refine ⟨fun L M ↦ ?_⟩
  let adj := ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : IsIso (adj.counit.app (L ⊗ (j)_!open[Ab.{u + 1}].obj M)) :=
    adj.isIso_counit_app_of_iso
      ((β_ L ((j)_!open[Ab.{u + 1}].obj M)) ≪≫
        ProEtale.openImmersionLowerShriekTensorIso Ab.{u + 1} j M L)
  change IsIso (adj.projectionFormulaMap L M)
  rw [Adjunction.projectionFormulaMap, Adjunction.homEquiv_counit]
  infer_instance

/-- The *linear* extension by zero `Mod_{j^* Λ_X} ⥤ Mod_{Λ_X}` along an open immersion
`j : U ⟶ X`: the lift of the extension by zero `j_!` on abelian sheaves to module objects
through the projection formula, sending `M` to `j_! M` with the `Λ_X`-action
`Λ_X ⊗ j_! M ≅ j_!(j^* Λ_X ⊗ M) ⟶ j_! M`. -/
noncomputable def linearOpenImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (condensedRingObj Λ X)

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of the linear extension by zero is the extension by zero. -/
lemma linearOpenImmersionLowerShriek_comp_forget :
    linearOpenImmersionLowerShriek Λ j ⋙ Mod.forget (condensedRingObj Λ X) =
      Mod.forget _ ⋙ (j)_!open[Ab.{u + 1}] := rfl

/-- The linear extension by zero is left adjoint to the transport `mapMod(j^*)` of module
objects along the strong monoidal `j^*`. -/
noncomputable def linearOpenImmersionLowerShriekAdjunction :
    linearOpenImmersionLowerShriek Λ j ⊣ (j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

instance linearOpenImmersionLowerShriek_additive : (linearOpenImmersionLowerShriek Λ j).Additive :=
  inferInstanceAs ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (condensedRingObj Λ X)).Additive

/-- The extension by zero on abelian sheaves preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_openImmersionLowerShriek_ab :
    PreservesFiniteColimits (j)_!open[Ab.{u + 1}] :=
  have : PreservesColimitsOfSize.{0, 0} (j)_!open[Ab.{u + 1}] :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
      ).leftAdjoint_preservesColimits
  inferInstance

/-- The linear extension by zero is left exact, since the extension by zero on abelian sheaves
is. -/
instance preservesFiniteLimits_linearOpenImmersionLowerShriek :
    PreservesFiniteLimits (linearOpenImmersionLowerShriek Λ j) :=
  inferInstanceAs (PreservesFiniteLimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (condensedRingObj Λ X)))

/-- The linear extension by zero is right exact. -/
instance preservesFiniteColimits_linearOpenImmersionLowerShriek :
    PreservesFiniteColimits (linearOpenImmersionLowerShriek Λ j) :=
  inferInstanceAs (PreservesFiniteColimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (condensedRingObj Λ X)))

/-- The extension by zero `j_! : Mod_{Λ_U} ⥤ Mod_{Λ_X}` along an open immersion
`j : U ⟶ X` on module objects over `Λ`: the restriction of scalars along
`α_j : j^* Λ_X ⟶ Λ_U` followed by the linear extension by zero. Its underlying sheaf is
the extension by zero `j_! M` of the underlying sheaf, with the `Λ_X`-action induced by the
projection formula and `α_j`. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  Mod.comap (condensedPullbackHom Λ j) ⋙ linearOpenImmersionLowerShriek Λ j

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open⟦" Λ "⟧" => openImmersionLowerShriek Λ j

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of the extension by zero on module objects is the extension by zero
of the underlying sheaf. -/
lemma openImmersionLowerShriek_comp_forget :
    (j)_!open⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ X) =
      Mod.forget (condensedRingObj Λ U) ⋙ (j)_!open[Ab.{u + 1}] := rfl

instance openImmersionLowerShriek_additive : (j)_!open⟦Λ⟧.Additive := by
  unfold openImmersionLowerShriek
  infer_instance

/-- The extension by zero on module objects along an open immersion is left exact. -/
instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open⟦Λ⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteLimits _ _

/-- The extension by zero on module objects along an open immersion is right exact. -/
instance preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (j)_!open⟦Λ⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteColimits _ _

/-- The extension by zero on module objects along an open immersion is exact. -/
instance preservesHomology_openImmersionLowerShriek : (j)_!open⟦Λ⟧.PreservesHomology := {}

/-- The adjunction `j_! ⊣ j^*` on module objects along an open immersion: the adjunction
`linear j_! ⊣ mapMod(j^*)` composed with the adjunction `Res_{α_j} ⊣ Coext_{α_j}`, and
`Coext_{α_j} ≅ Ext_{α_j}` since `α_j` is an isomorphism. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction : (j)_!open⟦Λ⟧ ⊣ (j)^*⟦Λ⟧ :=
  ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).comp
    (linearOpenImmersionLowerShriekAdjunction Λ j)).ofNatIsoRight
    (Functor.isoWhiskerLeft ((j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X))
      (Mod.extendScalarsIsoCoextendScalars (condensedPullbackHom Λ j)).symm)

instance : (j)_!open⟦Λ⟧.IsLeftAdjoint :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).isLeftAdjoint

end OpenImmersion

/-! ### Lower shriek along a morphism admitting a compactification -/

section Compactification

variable {X Y : Scheme.{u}}

/-- The lower shriek on module objects associated with a compactification `X ⟶[i] Z ⟶[g] Y`
of `f`: the extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def compactificationLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  (c.i)_!open⟦Λ⟧ ⋙ (c.g)_*⟦Λ⟧

variable (f : X ⟶ Y) [HasCompactification f]

/-- The lower shriek `f_! : Mod_{Λ_X} ⥤ Mod_{Λ_Y}` along a morphism `f : X ⟶ Y` admitting
a compactification, on module objects over `Λ`: the composition `i_! ⋙ g_*` associated
with the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  compactificationLowerShriek Λ (HasCompactification.compactification f)

@[inherit_doc lowerShriek]
scoped notation "(" f ")_!⟦" Λ "⟧" => lowerShriek Λ f

omit [IsCommMonObj Λ] in
/-- The lower shriek `f_!` on module objects is the extension by zero along the open immersion
of the chosen compactification followed by the pushforward along its proper structure
morphism. -/
lemma lowerShriek_eq :
    (f)_!⟦Λ⟧ = ((HasCompactification.compactification f).i)_!open⟦Λ⟧ ⋙
      ((HasCompactification.compactification f).g)_*⟦Λ⟧ :=
  rfl

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of `f_! M` is `f_! M`. -/
lemma lowerShriek_comp_forget :
    (f)_!⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) =
      Mod.forget (condensedRingObj Λ X) ⋙ ProEtale.lowerShriek Ab.{u + 1} f := rfl

instance lowerShriek_additive : (f)_!⟦Λ⟧.Additive := by
  rw [lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on module objects is left exact, being the composition of the exact
extension by zero along the open immersion of the chosen compactification with the left exact
pushforward along its proper structure morphism. -/
instance preservesFiniteLimits_lowerShriek : PreservesFiniteLimits (f)_!⟦Λ⟧ := by
  rw [lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
