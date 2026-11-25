/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The pullback of a constant étale sheaf

For `g : Z ⟶ Y`, the étale pullback of the constant sheaf `M_Y` is the constant sheaf `M_Z`.

## Main definitions

- `AlgebraicGeometry.Etale.isTerminalOverPullbackObjMkId`: the base change of the terminal
  object of `Y.Etale` along `g` is terminal in `Z.Etale`.
- `AlgebraicGeometry.Etale.constantSheafCompUpperStarIso`: the isomorphism `g^* M_Y ≅ M_Z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Y : Scheme.{u}}

/-- The base change `Y ×_Y Z` of the terminal object `Y` of `Y.Etale` along `g : Z ⟶ Y` is a
terminal object of `Z.Etale`. -/
noncomputable def isTerminalOverPullbackObjMkId {Z : Scheme.{u}} (g : Z ⟶ Y) :
    IsTerminal ((MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 Y))) :=
  IsTerminal.ofIso (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z)
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) g)) (Category.comp_id _)).symm

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pullback of a constant étale sheaf is the constant sheaf: `g^* M_Y ≅ M_Z`. Both functors
are left adjoint to taking global sections, since `Γ(Y, g_* G) = G(Y ×_Y Z) = Γ(Z, G)`. -/
noncomputable def constantSheafCompUpperStarIso {Z : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ (g)^*[ModuleCat.{u + 1} Λ] ≅
      constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
    (upperStarLowerStarAdjunction _ g)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))).leftAdjointUniq
    (constantSheafAdj _ _ (isTerminalOverPullbackObjMkId g))

end Etale

end AlgebraicGeometry
