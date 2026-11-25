/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The ideal criterion for flatness of étale sheaves

Let `Λ` be a commutative ring and `F` an étale sheaf of `Λ`-modules on a scheme `X`. Then `F`
is flat as soon as, for every ideal `I` of `Λ`, tensoring `F` with the inclusion `I_X ⟶ Λ_X`
of constant sheaves is a monomorphism (`AlgebraicGeometry.Etale.flat_of_forall_mono_whiskerLeft`).

Indeed the stalk of `F ⊗ I_X ⟶ F ⊗ Λ_X` at a geometric point `s` is `F_s ⊗ I ⟶ F_s ⊗ Λ`, so
every stalk `F_s` is a flat `Λ`-module by the ideal criterion for modules
(`Module.Flat.iff_lTensor_injective'`), and flatness of étale sheaves is checked on stalks
(`AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

namespace Etale

/-- The inclusion `I ⟶ Λ` of an ideal, as a morphism of `ModuleCat Λ`. -/
noncomputable abbrev idealSubtype (I : Ideal Λ) :
    ModuleCat.of Λ I ⟶ ModuleCat.of Λ Λ :=
  ModuleCat.ofHom I.subtype

/-- **Ideal criterion for flatness of étale sheaves.** An étale sheaf `F` of `Λ`-modules is flat
as soon as, for every ideal `I` of `Λ`, tensoring `F` with the inclusion `I_X ⟶ Λ_X` of
constant sheaves is a monomorphism. -/
theorem flat_of_forall_mono_whiskerLeft (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ I : Ideal Λ, Mono (F ◁ (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).map (idealSubtype I))) :
    ObjectProperty.flat F := by
  refine (flat_iff_forall_flat_sheafFiber_obj F).2 fun s ↦ ?_
  let Φ := (pointSmallEtale s).ulift.{u + 1}
  rw [ModuleCat.flat_iff_flat, Module.Flat.iff_lTensor_injective']
  intro I
  let c := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (idealSubtype I)
  have : Mono (Φ.sheafFiber.map (F ◁ c)) := Φ.sheafFiber.map_mono _
  -- the fibre of `F ◁ c` is `F_s ◁ c_s`, up to the monoidal structure of the fibre functor
  have : Mono (Φ.sheafFiber.obj F ◁ Φ.sheafFiber.map c) := by
    rw [(IsIso.eq_inv_comp _).2 (Functor.OplaxMonoidal.δ_natural_right Φ.sheafFiber F c)]
    infer_instance
  have h : idealSubtype I = (Φ.sheafFiberConstantSheafIso _).inv ≫ Φ.sheafFiber.map c ≫
      (Φ.sheafFiberConstantSheafIso _).hom := by
    simp [c, Φ.sheafFiber_map_constantSheaf_map]
  have : Mono (Φ.sheafFiber.obj F ◁ idealSubtype I) := by
    rw [h, whiskerLeft_comp, whiskerLeft_comp]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).1 this

end Etale

end AlgebraicGeometry
