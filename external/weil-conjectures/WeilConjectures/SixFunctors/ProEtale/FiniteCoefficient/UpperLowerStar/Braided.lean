/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.SectionsMonoidal

/-!
# Pullback and global sections of pro-étale sheaves are braided

The pullback `g^*` of pro-étale sheaves along any morphism of schemes is braided: its strong
monoidal structure is the oplax structure of the left adjoint of the lax braided pushforward
`g_*`, which is compatible with the braidings
(`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_δ_braiding`). The global sections functor
`Γ` is lax braided, as the sections over the terminal object of the site. Hence the stalk
functors `Γ(Spec K, s^* -)` at points `s : Spec K ⟶ X` are lax braided.

## Main results

- `AlgebraicGeometry.ProEtale.laxBraided_upperStar_of_monoidal`: the pullback is braided.
- `AlgebraicGeometry.ProEtale.laxBraided_Γ`: the global sections functor is lax braided.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

/-- Evaluation at an object is braided for the pointwise braiding of the functor category. -/
instance Functor.LaxBraided.evaluation {C : Type*} [Category* C] (E : Type*) [Category* E]
    [MonoidalCategory E] [BraidedCategory E] (X : C) :
    ((evaluation C E).obj X).LaxBraided where
  braided _ _ := (Category.id_comp _).trans (Category.comp_id _).symm

end CategoryTheory

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Z).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pullback `g^*` on pro-étale sheaves along any morphism is braided: its monoidal
structure is the oplax structure of the left adjoint of the lax braided pushforward `g_*`. -/
noncomputable instance ProEtale.laxBraided_upperStar_of_monoidal : (g)^*[A].LaxBraided where
  braided := Functor.Monoidal.μ_braiding_of_δ_braiding
    (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal_δ_braiding

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections functor is lax braided, as the sections over the terminal object. -/
noncomputable instance laxBraided_Γ (X : Scheme.{u}) :
    (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).LaxBraided :=
  letI : ((sheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 X)))).LaxBraided :=
    { laxMonoidal_sheafSections X _ with
      braided := (inferInstance : (sheafToPresheaf _ _ ⋙
        (evaluation _ (WeilCoefficients.{u} l)).obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X)))).LaxBraided).braided }
  haveI : NatTrans.IsMonoidal (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).symm.hom :=
    isMonoidal_ΓNatIsoSheafSections_inv X
  Functor.LaxBraided.ofNatIso
    (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

end AlgebraicGeometry.ProEtale
