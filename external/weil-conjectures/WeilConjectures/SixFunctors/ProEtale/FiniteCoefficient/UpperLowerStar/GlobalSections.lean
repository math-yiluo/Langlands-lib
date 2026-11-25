/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Global sections of pro-étale sheaves along pushforwards

The small pro-étale site of a scheme `X` has the terminal object `X` itself
(`AlgebraicGeometry.Scheme.ProEt.isTerminalMkId`), so the global sections of a pro-étale sheaf
are its sections over `X`. Base change along any morphism `g : Z ⟶ W` sends the terminal object
of `W.ProEt` to `W ×_W Z ≅ Z`, which gives the invariance of global sections under
pushforward, `Γ(W, g_* G) ≅ Γ(Z, G)`, and, for an isomorphism `e`, under pullback.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.isTerminalMkId`: `X` is terminal in `X.ProEt`.
- `AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`: `Γ(W, g_* G) ≅ Γ(Z, G)`.
- `AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso`: `Γ(Z, e^* G) ≅ Γ(W, G)` for an
  isomorphism `e : Z ≅ W`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- The scheme `X`, with the identity, is a terminal object of its small pro-étale site. -/
noncomputable def Scheme.ProEt.isTerminalMkId (X : Scheme.{u}) :
    IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom) fun V f ↦
    MorphismProperty.Over.Hom.ext <| by
      change f.left = V.hom
      rw [← MorphismProperty.Over.w f]
      exact (Category.comp_id _).symm

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

variable {Z W : Scheme.{u}}

/-- The base change of the terminal object `W` of `W.ProEt` along `g : Z ⟶ W` is
`W ×_W Z ≅ Z`, the terminal object of `Z.ProEt`. -/
noncomputable def overPullbackObjMkIdIso (g : Z ⟶ W) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj (Scheme.ProEt.mk (𝟙 W)) ≅
      Scheme.ProEt.mk (𝟙 Z) :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 W) g)) (Category.comp_id _)

/-- The global sections of a pushforward: `Γ(W, g_* G) = G(W ×_W Z) ≅ G(Z) = Γ(Z, G)`. -/
noncomputable def globalSectionsLowerStarIso (g : Z ⟶ W) :
    (g)_*[A] ⋙ Sheaf.Γ (Scheme.ProEt.topology W) A ≅ Sheaf.Γ (Scheme.ProEt.topology Z) A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId W)) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    ((sheafSections _ _).mapIso (overPullbackObjMkIdIso g).op).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Z)).symm

/-- The global sections of the pullback along an isomorphism `e : Z ≅ W`:
`Γ(Z, e^* G) ≅ Γ(Z, (e⁻¹)_* G) ≅ Γ(W, G)`. -/
noncomputable def globalSectionsUpperStarIso (e : Z ≅ W) :
    (e.hom)^*[A] ⋙ Sheaf.Γ (Scheme.ProEt.topology Z) A ≅ Sheaf.Γ (Scheme.ProEt.topology W) A :=
  Functor.isoWhiskerRight (upperStarIsoLowerStarInv A e) _ ≪≫
    globalSectionsLowerStarIso A e.inv

end ProEtale

end AlgebraicGeometry
