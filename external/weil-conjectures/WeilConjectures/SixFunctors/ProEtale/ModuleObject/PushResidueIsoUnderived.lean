/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# The underived (Push) comparison for a quotient coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. If, for a `Λ_X`-module `M`, the units `f_* M ⟶ Λ'_Y ⊗ f_* M` and
`f_* M ⟶ f_*(Λ'_X ⊗ M)` are cokernels of the same map, then the underived (Push) comparison
`Λ'_Y ⊗ f_* M ⟶ f_*(Λ'_X ⊗ M)` is an isomorphism at `M`
(`ProEtale.CondensedRing.isIso_pushHom_app_of_isColimit`): it is compatible with the units
(`ProEtale.CondensedRing.extendUnitHom_comp_pushHom_app_hom`).

For the residue map `𝒪_E ⟶ 𝔽_E` and a uniformizer `ϖ`, both units are cokernels of the
multiplication by `ϖ` on `f_* M` as soon as `ϖ` acts injectively on `M` and `R¹f_* M = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ'] in
/-- **The underived (Push) comparison through cokernels**: if the units
`f_* M ⟶ Λ'_Y ⊗ f_* M` and `f_* M ⟶ f_*(Λ'_X ⊗ M)` are cokernels of the same map `g`, then
`(pushHom a f).app M` is an isomorphism. -/
lemma isIso_pushHom_app_of_isColimit
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {W : Sheaf (ProEt.topology Y) Ab.{u + 1}} (g : W ⟶ ((f)_*⟦Λ⟧.obj M).X)
    (w₁ : g ≫ Mod.extendUnitHom (coefficientMap a Y) ((f)_*⟦Λ⟧.obj M) = 0)
    (w₂ : g ≫ (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a X) M) = 0)
    (h₁ : IsColimit (CokernelCofork.ofπ _ w₁)) (h₂ : IsColimit (CokernelCofork.ofπ _ w₂)) :
    IsIso ((pushHom a f).app M) := by
  have h : ((pushHom a f).app M).hom = (h₁.coconePointUniqueUpToIso h₂).hom :=
    Cofork.IsColimit.hom_ext h₁ (by
      refine (extendUnitHom_comp_pushHom_app_hom f a M).trans ?_
      exact (h₁.comp_coconePointUniqueUpToIso_hom h₂ WalkingParallelPair.one).symm)
  have : IsIso ((Mod.forget _).map ((pushHom a f).app M)) := by
    change IsIso ((pushHom a f).app M).hom
    rw [h]
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale.CondensedRing
