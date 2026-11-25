/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# The closed-support triangle pulled back to the pro-étale site

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` a complementary quasi-compact open
immersion. For a bounded below object `M` of `D(X_ét, Λ)`, the étale closed-support triangle
`Ri_* Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` is sent by the comparison pullback `ν_X^*` to a distinguished
triangle of `D(X_proét, Λ)`, whose outer vertices are identified with
`Ri_* ν_Z^* (Ri^! M)` and `Rj_* ν_U^* (j^* M)` by the comparison of direct images on bounded
below objects (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`).

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.exists_distTriang_mapDerivedCategory_closedSupport`:
  there are bounded below `C ∈ D(Z_ét, Λ)`, `N ∈ D(U_ét, Λ)` and a distinguished triangle
  `Ri_* ν_Z^* C ⟶ ν_X^* M ⟶ Rj_* ν_U^* N ⟶ (Ri_* ν_Z^* C)⟦1⟧` in `D(X_proét, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}}

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3), pulled back to the pro-étale
site: for a closed immersion `i : Z ⟶ X` and the complementary quasi-compact open immersion
`j : U ⟶ X`, and a bounded below `M ∈ D(X_ét, Λ)`, there are bounded below `C ∈ D(Z_ét, Λ)` and
`N ∈ D(U_ét, Λ)` (namely `Ri^! M` and `j^* M`) and a distinguished triangle
`Ri_* ν_Z^* C ⟶ ν_X^* M ⟶ Rj_* ν_U^* N ⟶ (Ri_* ν_Z^* C)⟦1⟧` in `D(X_proét, Λ)`. -/
theorem exists_distTriang_mapDerivedCategory_closedSupport (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : t.plus M) :
    ∃ (C : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_ : t.plus C) (_ : t.plus N)
      (f : (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor.obj
          (D(ν^*(Z)[ModuleCat.{u + 1} Λ]).obj C) ⟶ D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)
      (g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M ⟶
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
          (D(ν^*(U)[ModuleCat.{u + 1} Λ]).obj N))
      (h : (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
          (D(ν^*(U)[ModuleCat.{u + 1} Λ]).obj N) ⟶
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor.obj
          (D(ν^*(Z)[ModuleCat.{u + 1} Λ]).obj C))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ := by
  obtain ⟨w, hw, -⟩ := Etale.existsUnique_distTriang_closedSupportTriangle i j hij M
  obtain ⟨m, hm⟩ := hM
  let adj := Etale.rightDerivedLowerStarUpperShriekAdjunction Λ i
  have hC : t.plus ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i).rightAdjoint.obj M) :=
    t.plus_rightAdjoint_obj t adj 0 (fun K n hK ↦ by
      rw [add_zero]
      have : K.IsLE n := hK
      have := (Etale.lowerStar (ModuleCat.{u + 1} Λ) i).isLE_mapDerivedCategory_obj K n
      exact t.isLE_of_iso
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorIsoMapDerivedCategory).app
          K).symm n) M ⟨m, hm⟩
  have hN : t.plus ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.obj M) :=
    have := (Etale.upperStar (ModuleCat.{u + 1} Λ) j).isGE_mapDerivedCategory_obj M m
    ⟨m, t.isGE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app M).symm m⟩
  let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
  have hT := F.map_distinguished _ hw
  let e₁ := (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} Λ) i).app ⟨_, hC⟩
  let e₃ := (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} Λ) j).app ⟨_, hN⟩
  let T' := F.mapTriangle.obj (Etale.closedSupportTriangle i j M w)
  refine ⟨_, _, hC, hN, e₁.hom ≫ T'.mor₁, T'.mor₂ ≫ e₃.inv,
    e₃.hom ≫ T'.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁ (Iso.refl _) e₃ ?_ ?_ ?_)
  · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id]; rfl
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]; rfl
  · change (e₃.hom ≫ T'.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧') ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ T'.mor₃
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.DerivedCategory
