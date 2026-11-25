/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# The pushforward `f_*` and the pullback `f^*` on module objects over `Λ`

Let `Λ` be a commutative condensed ring, with coefficient ring objects
`Λ_X = p_X^* Λ` of abelian pro-étale sheaves and canonical coefficient morphisms
`η_f : Λ_Y ⟶ f_* Λ_X` and `α_f : f^* Λ_Y ⟶ Λ_X`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`). This file
defines the ordinary adjoint pair `f^* ⊣ f_*` on the categories `Mod_{Λ_X}` of module
objects, by the "`mapMod` followed by change of scalars" recipe:

* the pushforward `f_* : Mod_{Λ_X} ⥤ Mod_{Λ_Y}` is `mapMod(f_*)`, which sends an
  `Λ_X`-module to an `f_* Λ_X`-module since `f_*` is lax monoidal, followed by restriction
  of scalars along `η_f` (`ProEtale.CondensedRing.lowerStar`, notation `(f)_*⟦Λ⟧`). Its
  underlying sheaf is `f_* M`, with `Λ_Y` acting through `η_f`.
* the pullback `f^* : Mod_{Λ_Y} ⥤ Mod_{Λ_X}` is `mapMod(f^*)`, which sends an
  `Λ_Y`-module to an `f^* Λ_Y`-module since `f^*` is strong monoidal, followed by
  extension of scalars along `α_f` (`ProEtale.CondensedRing.upperStar`, notation
  `(f)^*⟦Λ⟧`). Its underlying sheaf is `Λ_X ⊗_{f^* Λ_Y} f^* M`, the ordinary ringed-topos
  pullback.
* the adjunction `f^* ⊣ f_*` (`ProEtale.CondensedRing.upperStarLowerStarAdjunction`) is the
  composition of the lift of the monoidal adjunction `f^* ⊣ f_*` to module objects
  (`Adjunction.mapModAdjunction`) with the adjunction between extension and restriction of
  scalars along `α_f`, using that `η_f` is the mate of `α_f`.

The constructions are formal and use no finiteness or completeness hypothesis on `Λ`. Since the
coefficients are pulled back from the point, `α_f` is an isomorphism for every `f`
(`ProEtale.isIso_condensedPullbackHom`), so the extension of scalars along it is an equivalence
and `f^*` on module objects is exact.

## Main results

- `ProEtale.CondensedRing.lowerStar_comp_forget`: the underlying sheaf of `f_* M` is
  `f_* M`; `ProEtale.CondensedRing.preservesFiniteLimits_lowerStar`: `f_*` is left exact.
- `ProEtale.CondensedRing.upperStar_comp_forget`: the underlying sheaf of `f^* M` is
  `Λ_X ⊗_{f^* Λ_Y} f^* M`; `ProEtale.CondensedRing.preservesFiniteColimits_upperStar`:
  `f^*` is right exact, and `ProEtale.CondensedRing.preservesFiniteLimits_upperStar`: `f^*`
  is left exact.
- `ProEtale.CondensedRing.upperStarLowerStarAdjunction`: the adjunction `f^* ⊣ f_*`.
- `ProEtale.CondensedRing.linearLowerStar`: the linear pushforward
  `Mod_{f^* Λ_Y} ⥤ Mod_{Λ_Y}`, of which `f_*` is the composition with the restriction of
  scalars along `α_f`.
- `ProEtale.CondensedRing.lowerStarComp` and `ProEtale.CondensedRing.upperStarComp`: the
  composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, the latter
  obtained from the former by uniqueness of left adjoints.
- `ProEtale.CondensedRing.lowerStarId` and `ProEtale.CondensedRing.upperStarId`: the identity
  isomorphisms `(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`, the latter obtained from the former by
  uniqueness of left adjoints.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The pushforward -/

section LowerStar

/-- The pushforward `f_* : Mod_{Λ_X} ⥤ Mod_{Λ_Y}` on module objects over `Λ`:
`mapMod(f_*)` followed by restriction of scalars along `η_f : Λ_Y ⟶ f_* Λ_X`. The
underlying sheaf of `f_* M` is `f_* M`, with `Λ_Y` acting through `η_f`. -/
noncomputable def lowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  (f)_*[Ab.{u + 1}].mapMod _ ⋙ Mod.comap (condensedPushforwardHom Λ f)

@[inherit_doc lowerStar]
scoped notation "(" f ")_*⟦" Λ "⟧" => lowerStar Λ f

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of `f_* M` is `f_* M`. -/
lemma lowerStar_comp_forget :
    (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) =
      Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}] := rfl

omit [IsCommMonObj Λ] in
lemma lowerStar_obj_X
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((f)_*⟦Λ⟧.obj M).X = (f)_*[Ab.{u + 1}].obj M.X := rfl

omit [IsCommMonObj Λ] in
/-- The action of `Λ_Y` on `f_* M` is `η_f` followed by the action of `f_* Λ_X` on `f_* M`
induced by the lax monoidal structure of `f_*`. -/
lemma lowerStar_obj_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    γ[condensedRingObj Λ Y,((f)_*⟦Λ⟧.obj M).X] =
      condensedPushforwardHom Λ f ▷ (f)_*[Ab.{u + 1}].obj M.X ≫
        Functor.LaxMonoidal.μ (f)_*[Ab.{u + 1}] (condensedRingObj Λ X) M.X ≫
          (f)_*[Ab.{u + 1}].map γ[condensedRingObj Λ X,M.X] := rfl

instance lowerStar_additive : (f)_*⟦Λ⟧.Additive := by
  unfold lowerStar
  infer_instance

/-- The pushforward `f_*` on module objects is left exact, since `f_*` is and finite limits of
module objects are computed on the underlying sheaves. -/
instance preservesFiniteLimits_lowerStar : PreservesFiniteLimits (f)_*⟦Λ⟧ := by
  unfold lowerStar
  infer_instance

end LowerStar

/-! ### The pullback -/

section UpperStar

/-- The pullback `f^* : Mod_{Λ_Y} ⥤ Mod_{Λ_X}` on module objects over `Λ`:
`mapMod(f^*)` followed by extension of scalars along `α_f : f^* Λ_Y ⟶ Λ_X`. The
underlying sheaf of `f^* M` is `Λ_X ⊗_{f^* Λ_Y} f^* M`. -/
noncomputable def upperStar :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (f)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.extendScalars (condensedPullbackHom Λ f)

@[inherit_doc upperStar]
scoped notation "(" f ")^*⟦" Λ "⟧" => upperStar Λ f

/-- The underlying sheaf of `f^* M` is the extension of scalars `Λ_X ⊗_{f^* Λ_Y} f^* M` of
the `f^* Λ_Y`-module `f^* M`. -/
lemma upperStar_comp_forget :
    (f)^*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ X) =
      (f)^*[Ab.{u + 1}].mapMod _ ⋙ Mod.extendScalars (condensedPullbackHom Λ f) ⋙
        Mod.forget (condensedRingObj Λ X) := rfl

lemma upperStar_obj
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*⟦Λ⟧.obj M =
      Mod.extendScalarsObj (condensedPullbackHom Λ f) (((f)^*[Ab.{u + 1}].mapMod _).obj M) := rfl

instance upperStar_additive : (f)^*⟦Λ⟧.Additive := by
  unfold upperStar
  infer_instance

/-- The pullback `f^*` on module objects is right exact, being a composition of a left adjoint
with the exact functor `mapMod(f^*)`. It is also left exact
(`ProEtale.CondensedRing.preservesFiniteLimits_upperStar`). -/
instance preservesFiniteColimits_upperStar : PreservesFiniteColimits (f)^*⟦Λ⟧ := by
  unfold upperStar
  exact comp_preservesFiniteColimits _ _

end UpperStar

/-! ### The linear pushforward and the adjunction `f^* ⊣ f_*` -/

section Adjunction

/-- The *linear* pushforward `Mod_{f^* Λ_Y} ⥤ Mod_{Λ_Y}` of module objects over `Λ`:
`mapMod(f_*)` followed by restriction of scalars along the unit `Λ_Y ⟶ f_* f^* Λ_Y`. Its
underlying sheaf functor is `f_*`, and `f_*` on module objects over `Λ_X` is its composition
with the restriction of scalars along `α_f`
(`ProEtale.CondensedRing.comapPullbackHomCompIso`). It is the pushforward that enters the
exceptional operations. -/
noncomputable def linearLowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  (f)_*[Ab.{u + 1}].mapMod _ ⋙
    Mod.comap ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom
      (condensedRingObj Λ Y))

omit [IsCommMonObj Λ] in
/-- The underlying sheaf of the linear pushforward is the pushforward. -/
lemma linearLowerStar_comp_forget :
    linearLowerStar Λ f ⋙ Mod.forget (condensedRingObj Λ Y) =
      Mod.forget _ ⋙ (f)_*[Ab.{u + 1}] := rfl

instance linearLowerStar_additive : (linearLowerStar Λ f).Additive := by
  unfold linearLowerStar
  infer_instance

/-- The linear pushforward is left exact. -/
instance preservesFiniteLimits_linearLowerStar : PreservesFiniteLimits (linearLowerStar Λ f) := by
  unfold linearLowerStar
  infer_instance

/-- The pushforward `f_*` on module objects over `Λ_X` is the restriction of scalars along
`α_f` followed by the linear pushforward: restricting scalars along `α_f`, then along `f_* α_f`
and the unit `Λ_Y ⟶ f_* f^* Λ_Y`, is restricting scalars along their composition `η_f`. -/
noncomputable def comapPullbackHomCompIso :
    Mod.comap (condensedPullbackHom Λ f) ⋙ linearLowerStar Λ f ≅ (f)_*⟦Λ⟧ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)_*[Ab.{u + 1}].mapModComapIso (condensedPullbackHom Λ f)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
      Mod.comapCongr (unitAlgHom_comp_map_condensedPullbackHom Λ f))

/-- The adjunction `f^* ⊣ f_*` on module objects over `Λ`: a `Λ_X`-linear map
`Λ_X ⊗_{f^* Λ_Y} f^* M ⟶ N` is the same as an `f^* Λ_Y`-linear map `f^* M ⟶ N`, which
is the same as a `Λ_Y`-linear map `M ⟶ f_* N`. -/
noncomputable def upperStarLowerStarAdjunction : (f)^*⟦Λ⟧ ⊣ (f)_*⟦Λ⟧ :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).comp
    (Mod.extendRestrictAdjunction (condensedPullbackHom Λ f))).ofNatIsoRight
    (comapPullbackHomCompIso Λ f)

instance : (f)_*⟦Λ⟧.IsRightAdjoint := (upperStarLowerStarAdjunction Λ f).isRightAdjoint

instance : (f)^*⟦Λ⟧.IsLeftAdjoint := (upperStarLowerStarAdjunction Λ f).isLeftAdjoint

/-- The pushforward `f_*` on module objects preserves all limits of size `0`, being a right
adjoint. -/
noncomputable instance preservesLimitsOfSize_lowerStar : PreservesLimitsOfSize.{0, 0} (f)_*⟦Λ⟧ :=
  (upperStarLowerStarAdjunction Λ f).rightAdjoint_preservesLimits

/-- The pullback `f^*` on module objects preserves all colimits of size `0`, being a left
adjoint. -/
noncomputable instance preservesColimitsOfSize_upperStar :
    PreservesColimitsOfSize.{0, 0} (f)^*⟦Λ⟧ :=
  (upperStarLowerStarAdjunction Λ f).leftAdjoint_preservesColimits

end Adjunction

/-! ### Exactness of the pullback -/

section Exact

/-- The pullback `f^*` on module objects over `Λ` is left exact: since `α_f` is an isomorphism
(`ProEtale.isIso_condensedPullbackHom`), the extension of scalars along it is the restriction of
scalars along its inverse, and `f^*` on module objects is the left exact `mapMod(f^*)` up to this
equivalence. -/
instance preservesFiniteLimits_upperStar : PreservesFiniteLimits (f)^*⟦Λ⟧ :=
  preservesFiniteLimits_of_natIso (Functor.isoWhiskerLeft
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm

/-- The pullback `f^*` on module objects over `Λ` is exact. -/
instance preservesHomology_upperStar : (f)^*⟦Λ⟧.PreservesHomology := {}

end Exact

/-! ### Composition -/

section Comp

variable {Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The restriction of scalars along the two ways of letting `Λ_Z` act on `(f ≫ g)_* M`: through
`η_g`, `g_* η_f` and the composition isomorphism `g_* f_* ≅ (f ≫ g)_*`, or through `η_{f ≫ g}`.
This is the comparison of the actions entering `ProEtale.CondensedRing.lowerStarComp`. The two
restrictions agree since `η_{f ≫ g} = η_g ≫ g_* η_f ≫ (g_* f_* ≅ (f ≫ g)_*)`
(`ProEtale.condensedPushforwardHom_comp`). -/
noncomputable def comapCondensedPushforwardHomComp :
    (Mod.comap (Functor.compAlgHom (f)_*[Ab.{u + 1}] (g)_*[Ab.{u + 1}]
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom (condensedRingObj Λ X)) :
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((f ≫ g)_*[Ab.{u + 1}].obj (condensedRingObj Λ X)) ⥤ _) ⋙
      Mod.comap (condensedPushforwardHom Λ g ≫
        (g)_*[Ab.{u + 1}].map (condensedPushforwardHom Λ f)) ≅
      Mod.comap (condensedPushforwardHom Λ (f ≫ g)) :=
  (Mod.comapComp _ _).symm ≪≫
    Mod.comapCongr (by rw [condensedPushforwardHom_comp, Category.assoc])

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of pushforwards on module objects over
`Λ`: on underlying sheaves it is the composition isomorphism `ProEtale.lowerStarComp`,
which is monoidal (`ProEtale.isMonoidal_lowerStarComp`), and the two actions of `Λ_Z`
agree since `η_{f ≫ g}` is `η_g` followed by `g_* η_f` up to `ProEtale.lowerStarComp`
(`ProEtale.CondensedRing.comapCondensedPushforwardHomComp`). -/
noncomputable def lowerStarComp : (f)_*⟦Λ⟧ ⋙ (g)_*⟦Λ⟧ ≅ (f ≫ g)_*⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((g)_*[Ab.{u + 1}].mapModComapIso (condensedPushforwardHom Λ f)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso (f)_*[Ab.{u + 1}] (g)_*[Ab.{u + 1}]
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom (condensedRingObj Λ X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (comapCondensedPushforwardHomComp Λ f g)

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of pullbacks on module objects over
`Λ`, obtained from `ProEtale.CondensedRing.lowerStarComp` by uniqueness of left
adjoints: both sides are left adjoint to `f_* ⋙ g_*`. -/
noncomputable def upperStarComp : (f ≫ g)^*⟦Λ⟧ ≅ (g)^*⟦Λ⟧ ⋙ (f)^*⟦Λ⟧ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction Λ (f ≫ g))
      ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))).symm
    (lowerStarComp Λ f g).symm).symm

end Comp

/-! ### Identity -/

section Id

variable (X)

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of the pushforward on module objects over `Λ`: on
underlying sheaves it is the identity isomorphism `ProEtale.lowerStarId`, which is monoidal
(`ProEtale.isMonoidal_lowerStarId`), and it is compatible with the actions of `Λ_X` since
`η_{𝟙 X}` is the inverse of `ProEtale.lowerStarId` at `Λ_X`
(`ProEtale.condensedPushforwardHom_id`). -/
noncomputable def lowerStarId :
    (𝟙 X)_*⟦Λ⟧ ≅ 𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X) (by
    have h := NatTrans.IsMonoidal.tensor (τ := (ProEtale.lowerStarId Ab.{u + 1} X).hom)
      (condensedRingObj Λ X) M.X
    simp only [Functor.LaxMonoidal.id_μ, Category.comp_id] at h
    change (condensedPushforwardHom Λ (𝟙 X) ▷ _ ≫ Functor.LaxMonoidal.μ _ _ _ ≫ _) ≫ _ = _
    rw [condensedPushforwardHom_id, Category.assoc, Category.assoc, Iso.app_hom,
      (ProEtale.lowerStarId Ab.{u + 1} X).hom.naturality, ← Category.assoc
        (Functor.LaxMonoidal.μ _ _ _), h, Functor.id_map, ← Category.assoc]
    congr 1
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Category.id_comp]
    exact id_tensorHom _ _))
    (fun f ↦ by ext : 1; exact (ProEtale.lowerStarId Ab.{u + 1} X).hom.naturality f.hom)

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback on module objects over `Λ`, obtained
from `ProEtale.CondensedRing.lowerStarId` by uniqueness of left adjoints. -/
noncomputable def upperStarId :
    (𝟙 X)^*⟦Λ⟧ ≅ 𝟭 (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction Λ (𝟙 X)) Adjunction.id).symm
    (lowerStarId Λ X)).symm

end Id

end AlgebraicGeometry.ProEtale.CondensedRing
