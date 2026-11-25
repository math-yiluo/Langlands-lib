/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalNatTrans

/-!
# The composition isomorphisms of the derived pullback and the units

For `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) of the derived pullbacks of étale sheaves is
compatible with the counits `η : Lh^* Λ ⟶ Λ` of the oplax monoidal derived pullbacks:

```
L(fg)^* Λ_Z ──────────▶ Lf^* Lg^* Λ_Z
     │                       │ Lf^* η_g
     │ η_{fg}                ▼
     │                  Lf^* Λ_Y
     ▼                       │ η_f
    Λ_X ◀────────────────────┘
```

Its compatibility with the tensor comparisons is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`.

## Main statements

- `AlgebraicGeometry.Etale.isMonoidal_upperStarComp_hom`: the composition isomorphism
  `(fg)^* ≅ g^* ⋙ f^*` of the underived pullbacks of sheaves of `Λ`-modules is monoidal.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_unit`: the compatibility of the
  derived composition isomorphism with the counits `η`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` of the pullbacks of étale sheaves of
`Λ`-modules is monoidal: it is conjugate to the composition isomorphism of the pushforwards, which
is monoidal (`AlgebraicGeometry.Etale.isMonoidal_lowerStarComp_hom`). -/
instance isMonoidal_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    NatTrans.IsMonoidal (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
  have h : (Etale.upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom =
      (conjugateEquiv ((Etale.upperStarLowerStarAdjunction _ h₂).comp
        (Etale.upperStarLowerStarAdjunction _ h₁))
        (Etale.upperStarLowerStarAdjunction _ h₁₂)).symm
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂ h₁₂ hh).hom := by
    rw [Equiv.eq_symm_apply]
    exact congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarComp _ h₁ h₂ h₁₂ hh)
  rw [h]
  exact isMonoidal_conjugateEquiv_symm _ _ _

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

open _root_.DerivedCategory

/-- The counit `η : Lh^* Λ_Y ⟶ Λ_X` of the oplax monoidal derived pullback, in terms of the counit
of the left derived functor. -/
lemma leftDerivedUpperStar_η_eq {W V : Scheme.{u}} (h : W ⟶ V) [(h)^*[A].PreservesFlat] :
    letI := leftDerivedUpperStarOplaxMonoidal A h
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf W.smallEtaleTopology A)
    Functor.OplaxMonoidal.η (L((h)^*[A])) = (L((h)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
      (h)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
        Qh.map (Functor.OplaxMonoidal.η ((h)^*[A].mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (Functor.LaxMonoidal.ε Qh) :=
  rfl

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
  [(f)^*[A].PreservesFlat] [(g)^*[A].PreservesFlat] [(fg)^*[A].PreservesFlat]
  [NatTrans.IsMonoidal (Etale.upperStarComp A f g fg hfg).hom]

-- the kernel unfolds the counits of three left derived functors
/-- The composition isomorphism `L(fg)^* ≅ Lg^* ⋙ Lf^*` is compatible with the counits
`η : Lh^* Λ ⟶ Λ` of the oplax monoidal derived pullbacks. -/
theorem leftDerivedUpperStarComp_hom_app_unit :
    letI := leftDerivedUpperStarOplaxMonoidal A f
    letI := leftDerivedUpperStarOplaxMonoidal A g
    letI := leftDerivedUpperStarOplaxMonoidal A fg
    (leftDerivedUpperStarComp A f g fg hfg).hom.app (𝟙_ _) ≫
        (L((f)^*[A])).map (Functor.OplaxMonoidal.η (L((g)^*[A]))) ≫
          Functor.OplaxMonoidal.η (L((f)^*[A])) =
      Functor.OplaxMonoidal.η (L((fg)^*[A])) := by
  rw [leftDerivedUpperStar_η_eq, leftDerivedUpperStar_η_eq, leftDerivedUpperStar_η_eq]
  have := DerivedCategory.isIso_ε_Qh (Sheaf Y.smallEtaleTopology A)
  have e₁ : (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
        (g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
          Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫
            CategoryTheory.inv (Functor.LaxMonoidal.ε Qh)) ≫
        (L((f)^*[A])).map (Functor.LaxMonoidal.ε Qh) =
      (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh)) ≫
        (L((f)^*[A])).map ((g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _)) ≫
          (L((f)^*[A])).map
            (Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) := by
    simp only [← Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn : (L((f)^*[A])).map
        (Qh.map (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) ≫
        (f)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) =
      (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj (𝟙_ _)) ≫
        Qh.map (((f)^*[A].mapHomotopyCategory (.up ℤ)).map
          (Functor.OplaxMonoidal.η ((g)^*[A].mapHomotopyCategory (.up ℤ)))) :=
    (f)^*[A].leftDerivedFunctorCounit.naturality _
  have hc : (leftDerivedUpperStarComp A f g fg hfg).hom.app (𝟙_ _) ≫
        (L((f)^*[A])).map ((L((g)^*[A])).map (Functor.LaxMonoidal.ε Qh)) =
      (L((fg)^*[A])).map (Functor.LaxMonoidal.ε Qh) ≫
        (leftDerivedUpperStarComp A f g fg hfg).hom.app (Qh.obj (𝟙_ _)) :=
    ((leftDerivedUpperStarComp A f g fg hfg).hom.naturality _).symm
  have hX : (fg)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (Functor.mapHomotopyCategoryCompNatTrans (g)^*[A] (f)^*[A] (fg)^*[A]
        (Etale.upperStarComp A f g fg hfg).hom (𝟙_ _)) = _ :=
    (leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit A f g fg hfg (𝟙_ _)).symm
  have hu := Functor.mapHomotopyCategoryCompNatTrans_η (g)^*[A] (f)^*[A] (fg)^*[A]
    (Etale.upperStarComp A f g fg hfg).hom
  have e₂ := congrArg Qh.map hu
  simp only [Functor.map_comp] at e₂
  rw [reassoc_of% e₁, reassoc_of% hn, reassoc_of% hc, ← reassoc_of% hX]
  rw [← e₂]
  simp only [Category.assoc]

end Derived

end Etale

end AlgebraicGeometry
