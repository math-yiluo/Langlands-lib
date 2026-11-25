/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Germs of sections of pushforwards

Let `f : Z ⟶ Y` and `g : S ⟶ Z` be morphisms of schemes, `Q` a sheaf on `Z_proét` and `V` an
object of `Y_proét`. A section `p` of `f_* Q` over `V` is a section of `Q` over `V ×_Y Z`. Its germ
along `g ≫ f`, followed by `(g ≫ f)^* f_* Q ≅ g^* f^* f_* Q ⟶ g^* Q` (the counit of `f^* ⊣ f_*`),
is its germ along `g` as a section of `Q`
(`AlgebraicGeometry.ProEtale.germ_comp_lowerStar`). This follows from the description of the unit
of `(g ≫ f)^* ⊣ (g ≫ f)_*` as the composite of the units and from the triangle identity.

For an open immersion `f = j`, this compares the germs of sections of `j_* F` at the points of
`U` with the germs of sections of `F`, as used for the boundary stalks of direct images in
blueprint `lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Germs of sections of a pushforward.** The germ along `g ≫ f` of a section of `f_* Q` over
`V`, followed by `(g ≫ f)^* f_* Q ≅ g^* f^* f_* Q ⟶ g^* Q`, is its germ along `g` as a section of
`Q` over `V ×_Y Z`. -/
lemma germ_comp_lowerStar {S Z Y : Scheme.{u}} (g : S ⟶ Z) (f : Z ⟶ Y)
    (Q : Sheaf (ProEt.topology Z) A) {V : Y.ProEt}
    (t : ProEt.mk (𝟙 S) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g ≫ f)).obj V)
    (t' : ProEt.mk (𝟙 S) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V))
    (ht : t ≫ (MorphismProperty.Over.pullbackComp g f).hom.app V = t') :
    germ A (g ≫ f) ((f)_*[A].obj Q) t ≫
      (Sheaf.Γ _ A).map ((upperStarComp A g f).hom.app _ ≫
        (g)^*[A].map ((upperStarLowerStarAdjunction A f).counit.app Q)) = germ A g Q t' := by
  set P := (f)_*[A].obj Q
  set φ := (upperStarComp A g f).hom.app P ≫
    (g)^*[A].map ((upperStarLowerStarAdjunction A f).counit.app Q)
  have hE := congrArg (fun ψ ↦ ψ.hom.app (op V))
    (upperStarLowerStarAdjunction_unit_app_comp_map_upperStarComp A g f P)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hE
  -- the triangle identity at `V`
  have htri := congrArg (fun ψ ↦ ψ.hom.app (op V))
    ((upperStarLowerStarAdjunction A f).right_triangle_components Q)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at htri
  -- naturality of the unit of `g^* ⊣ g_*` with respect to the counit of `f^* ⊣ f_*`
  have hu := congrArg (fun ψ ↦ ψ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
    f).obj V))) ((upperStarLowerStarAdjunction A g).unit.naturality
      ((upperStarLowerStarAdjunction A f).counit.app Q))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.id_map,
    Functor.comp_map] at hu
  have n₁ := (φ.hom.naturality t.op)
  have n₂ := (Sheaf.ΓNatIsoSheafSections _ A (ProEt.isTerminalMkId S)).inv.naturality φ
  have n₃ := ((g)^*[A].map ((upperStarLowerStarAdjunction A f).counit.app Q)).hom.naturality
    ((MorphismProperty.Over.pullbackComp g f).hom.app V).op
  rw [germ, germ, Category.assoc, Category.assoc, ← n₂]
  erw [reassoc_of% n₁]
  have hφ : φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g ≫ f)).obj V)) =
      ((upperStarComp A g f).hom.app P).hom.app _ ≫
        ((g)^*[A].map ((upperStarLowerStarAdjunction A f).counit.app Q)).hom.app _ := rfl
  rw [hφ]
  simp only [Category.assoc]
  simp only [lowerStar_map_hom_app'] at hE htri hu
  erw [reassoc_of% hE]
  rw [lowerStarComp_hom_app_hom_app]
  erw [reassoc_of% n₃]
  erw [reassoc_of% hu.symm]
  erw [reassoc_of% htri]
  erw [NatTrans.id_app, Category.id_comp]
  congr 1
  rw [← ht, op_comp, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale
