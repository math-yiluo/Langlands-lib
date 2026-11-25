/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Free sheaves of modules on étale objects as extensions by zero

Let `W` be an object of the small étale site of a scheme `X` and `Λ` a commutative ring. The
free sheaf `Λ[W]`, the sheafification of the presheaf `V ↦ Λ^{(Hom_X(V, W))}`
(`AlgebraicGeometry.Etale.freeSheaf`), is the extension by zero `j_{W!} Λ_W` along the étale
structure morphism `j_W : W ⟶ X` of the constant sheaf `Λ_W` on `W_ét`. Indeed, the free sheaf
on the terminal object of `W_ét` is the constant sheaf `Λ_W`, since `Hom_W(V, W)` is a singleton
for every étale `W`-scheme `V`, and extension by zero sends free sheaves to free sheaves
(`AlgebraicGeometry.Etale.etaleLowerShriekFreeSheafIso`).

## Main definitions

- `AlgebraicGeometry.Etale.freeSheafTerminalIso`: `Λ[W] ≅ Λ_W` on `W_ét`.
- `AlgebraicGeometry.Etale.freeSheafIsoEtaleLowerShriekConstantSheaf`: `Λ[W] ≅ j_{W!} Λ_W`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On the small étale site of a scheme `W`, the presheaf `V ↦ Λ^{(Hom_W(V, W))}` is the
constant presheaf `Λ`, `Hom_W(V, W)` being a singleton. -/
noncomputable def freePresheafTerminalIso (W : Scheme.{u}) :
    uliftYoneda.{u + 1}.obj (Scheme.Etale.mk (𝟙 W)) ⋙ ModuleCat.free Λ ≅
      (Functor.const W.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ) :=
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 W)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale W
  letI (V : W.Etaleᵒᵖ) : Unique (ULift.{u + 1} (V.unop ⟶ Scheme.Etale.mk (𝟙 W))) :=
    { default := ULift.up (hT.from V.unop)
      uniq := fun _ ↦ ULift.ext (hT.hom_ext _ _) }
  Functor.isoWhiskerRight (NatIso.ofComponents (fun _ ↦ Equiv.toIso (Equiv.ofUnique _ PUnit))
      (fun _ ↦ rfl) : uliftYoneda.{u + 1}.obj (Scheme.Etale.mk (𝟙 W)) ≅
        (Functor.const W.Etaleᵒᵖ).obj PUnit) (ModuleCat.free Λ) ≪≫
    Functor.constComp _ _ _ ≪≫
    (Functor.const W.Etaleᵒᵖ).mapIso
      (Finsupp.uniqueLinearEquiv Λ Λ PUnit.unit).toModuleIso

/-- The free sheaf on the terminal object of the small étale site of `W` is the constant sheaf
`Λ_W`. -/
noncomputable def freeSheafTerminalIso (W : Scheme.{u}) :
    (Etale.freeSheaf Λ W).obj (Scheme.Etale.mk (𝟙 W)) ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) :=
  (presheafToSheaf _ _).mapIso (freePresheafTerminalIso Λ W)

/-- **Free representable sheaves of modules are étale extensions by zero**: for an object `W`
of the small étale site of `X`, the free sheaf `Λ[W]`, the sheafification of the presheaf
`V ↦ Λ^{(Hom_X(V, W))}` with restriction by precomposition, is isomorphic to the extension by
zero `j_{W!} Λ_W` along `j_W : W ⟶ X` of the constant rank-one sheaf `Λ_W` on `W_ét`.
(blueprint: `lem-weil-pbc-free-etale-module-shriek-comparison`) -/
noncomputable def freeSheafIsoEtaleLowerShriekConstantSheaf {X : Scheme.{u}} (W : X.Etale) :
    (Etale.freeSheaf Λ X).obj W ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom W.prop).obj
        ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)) :=
  (Etale.freeSheaf Λ X).mapIso (MorphismProperty.Over.isoMk (Iso.refl _) (by simp)) ≪≫
    (Etale.etaleLowerShriekFreeSheafIso Λ W.hom W.prop (Scheme.Etale.mk (𝟙 W.left))).symm ≪≫
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom W.prop).mapIso
      (freeSheafTerminalIso Λ W.left)

end AlgebraicGeometry.Etale
