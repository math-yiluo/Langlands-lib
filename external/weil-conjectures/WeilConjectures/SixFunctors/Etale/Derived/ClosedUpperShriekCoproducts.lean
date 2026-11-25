/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral

/-!
# The exceptional inverse image along a closed immersion commutes with coproducts

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X` of finite
cohomological dimension. The right adjoint `Ri^!` of `Ri_*` on the unbounded derived categories
of étale sheaves of modules (`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`)

* commutes with coproducts
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek`): the
  closed-support triangles `Ri_* Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` of a family are compared with that of
  the coproduct; the coproduct of distinguished triangles is distinguished, `Rj_* j^*` commutes
  with coproducts, and `Ri_*` is fully faithful and left adjoint;
* has bounded amplitude
  (`AlgebraicGeometry.Etale.exists_isLE_rightDerivedFunctor_closedUpperShriek`): it sends objects
  in degrees `≤ n` into degrees `≤ n + d + 1` if `Rj_*` has cohomological dimension `≤ d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Category

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

/-- The closed-support triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` for an arbitrary coefficient
ring `Λ`, as the supported localization triangle of the recollement
(`CategoryTheory.Pretriangulated.Recollement.exists_distTriang_counit_unit`). For finite `Λ`
this is `AlgebraicGeometry.Etale.exists_distTriang_closedSupport`. -/
private lemma exists_distTriang_closedSupport_recollement
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ w, Triangle.mk ((derivedLowerStarClosedUpperShriekAdjunction i j hij).counit.app K)
      ((derivedUpperStarLowerStarAdjunction _ j).unit.app K) w ∈ distTriang _ :=
  Recollement.exists_distTriang_counit_unit (derivedUpperStarLowerStarAdjunction _ j)
    (derivedLowerStarClosedUpperShriekAdjunction i j hij)
    (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion i)
    (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj i j (hij ▸ disjoint_compl_left))
    (fun _ hK ↦ rightDerivedLowerStar_essImage_of_isZero i j hij hK) K

variable [QuasiCompact j]

include hij in
/-- The exceptional inverse image `Ri^!` along a closed immersion commutes with coproducts, when
the complementary open immersion `j` has finite cohomological dimension. -/
theorem isIso_sigmaComparison_rightDerivedFunctor_closedUpperShriek
    (hj : HasFiniteCohomologicalDimensionMorphism Λ j) {J : Type (u + 1)}
    (M : J → _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (sigmaComparison
      (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor M) := by
  let F := ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor
  let G := (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor
  let adj : F ⊣ G := derivedLowerStarClosedUpperShriekAdjunction i j hij
  let L := L((j)^*[ModuleCat.{u + 1} Λ])
  let R := R((j)_*[ModuleCat.{u + 1} Λ])
  let adj' : L ⊣ R := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have := preservesCoproducts_rightDerivedLowerStar Λ j hj J
  have : PreservesColimitsOfShape (Discrete J) L := adj'.leftAdjoint_preservesColimits.1
  have : PreservesColimitsOfShape (Discrete J) F := adj.leftAdjoint_preservesColimits.1
  have hgi : Disjoint (Set.range j.base) (Set.range i.base) := hij ▸ disjoint_compl_right
  -- the closed-support triangles of the family and of its coproduct
  choose w hw using fun t ↦ exists_distTriang_closedSupport_recollement i j hij (M t)
  obtain ⟨w₀, hw₀⟩ := exists_distTriang_closedSupport_recollement i j hij (∐ M)
  let T (t : J) := Triangle.mk (adj.counit.app (M t)) (adj'.unit.app (M t)) (w t)
  have hcp := coproductTriangle_distinguished T hw
  let c := sigmaComparison (L ⋙ R) M
  have hcomm : (Limits.Sigma.map fun t ↦ adj'.unit.app (M t)) ≫ c = adj'.unit.app (∐ M) :=
    Sigma.hom_ext _ _ fun t ↦ by
      rw [Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison]
      exact (adj'.unit.naturality (Sigma.ι M t)).symm
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ (coproductTriangle T) _ hcp
    hw₀ (𝟙 (∐ M)) c (hcomm.trans (id_comp _).symm)
  have ha : IsIso a := isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a (𝟙 _) c ha₁
    (hcomm.trans (id_comp _).symm) ha₃) hcp hw₀ 
    ⟨⟨𝟙 _, comp_id _, comp_id _⟩⟩
    (by simpa using (inferInstance : IsIso c))
  let a' : (∐ fun t ↦ F.obj (G.obj (M t))) ⟶ F.obj (G.obj (∐ M)) := a
  have ha' : a' ≫ adj.counit.app (∐ M) = Limits.Sigma.map fun t ↦ adj.counit.app (M t) :=
    ((comp_id _).symm.trans ha₁).symm
  -- the canonical comparison agrees with `a`
  let can := sigmaComparison F (fun t ↦ G.obj (M t)) ≫ F.map (sigmaComparison G M)
  have hcan : can ≫ adj.counit.app (∐ M) = Limits.Sigma.map fun t ↦ adj.counit.app (M t) :=
    Sigma.hom_ext _ _ fun t ↦ by
      simp only [can, assoc, ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc,
        ι_comp_sigmaComparison, Limits.Sigma.ι_map]
      exact adj.counit.naturality (Sigma.ι M t)
  have hzero (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Y : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (h : F.obj N ⟶ (R.obj Y)⟦(-1 : ℤ)⟧) : h = 0 := by
    have hz := isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj (Λ := Λ) i j hgi.symm N
    have h1 : h ≫ (R.commShiftIso (-1 : ℤ)).inv.app Y = 0 := by
      rw [← (adj'.homEquiv _ _).apply_symm_apply (h ≫ _),
        hz.eq_of_src ((adj'.homEquiv _ _).symm _) 0]
      simp
    simpa using h1 =≫ (R.commShiftIso (-1 : ℤ)).hom.app Y
  have ce {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (f : W ⟶ F.obj (G.obj (∐ M))) (hf : f ≫ adj.counit.app (∐ M) = 0) : ∃ g :
        W ⟶ (R.obj (L.obj (∐ M)))⟦(-1 : ℤ)⟧,
        f = g ≫ (Triangle.mk (adj.counit.app (∐ M)) (adj'.unit.app (∐ M)) w₀).invRotate.mor₁ :=
    Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hw₀) f hf
  have heq : can = a' := by
    rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := ce (can - a') (by rw [Preadditive.sub_comp, hcan, ha', sub_self])
    have : g = 0 := Sigma.hom_ext _ _ fun t ↦ by
      rw [comp_zero]
      exact hzero _ _ _
    rw [hg, this, zero_comp]
  have : IsIso can := heq ▸ ha
  have : IsIso (F.map (sigmaComparison G M)) := IsIso.of_isIso_comp_left (sigmaComparison F _) _
  exact isIso_of_fully_faithful F _

include hij in
/-- The exceptional inverse image `Ri^!` along a closed immersion commutes with coproducts, when
the complementary open immersion `j` has finite cohomological dimension. -/
theorem preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek
    (hj : HasFiniteCohomologicalDimensionMorphism Λ j) (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor :=
  have (M : J → _) := isIso_sigmaComparison_rightDerivedFunctor_closedUpperShriek i j hij hj M
  have (M : J → _) : PreservesColimit (Discrete.functor M)
      (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor :=
    PreservesCoproduct.of_iso_comparison _ _
  preservesColimitsOfShape_of_discrete _

omit [QuasiCompact j] in
include hij in
/-- The exceptional inverse image `Ri^!` along a closed immersion has bounded amplitude, when the
complementary open immersion `j` has finite cohomological dimension: from the closed-support
triangle `Ri_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶`, if `K` lies in degrees `≤ n` then so does
`Ri_* Ri^! K` up to `d + 1`, and `i_*` is exact and faithful. -/
theorem exists_isLE_rightDerivedFunctor_closedUpperShriek
    (hj : HasFiniteCohomologicalDimensionMorphism Λ j) :
    ∃ c : ℤ, ∀ (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (n : ℤ), K.IsLE n →
        ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K).IsLE (n + c) := by
  obtain ⟨d, hd⟩ := hj
  have hcd : ∀ (F : Sheaf _ (ModuleCat.{u + 1} Λ)) (q : ℕ), d.toNat < q →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).rightDerived q).obj F) := fun F q hq ↦
    Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia))
  refine ⟨d.toNat + 1, fun K n hK ↦ ?_⟩
  let F := ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor
  let G := (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor
  let adj : F ⊣ G := derivedLowerStarClosedUpperShriekAdjunction i j hij
  obtain ⟨w, hw⟩ := exists_distTriang_closedSupport_recollement i j hij K
  have := ((j)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K n
  have hL : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K).IsLE n :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm n
  have hB := Functor.isLE_rightDerivedFunctor_obj _ d.toNat hcd
    ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) n
  have hB' : (((R((j)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))⟦(-1 : ℤ)⟧).IsLE (n + (d.toNat + 1)) :=
    DerivedCategory.TStructure.t.isLE_shift _ (n + d.toNat) (-1) _ (by lia)
  have hK' : K.IsLE (n + (d.toNat + 1)) := DerivedCategory.TStructure.t.isLE_of_le K n _ (by lia)
  have hA : (F.obj (G.obj K)).IsLE (n + (d.toNat + 1)) :=
    DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang _ hw) _ hB' hK'
  have hA' : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (G.obj K)).IsLE
      (n + (d.toNat + 1)) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app _) _
  exact (DerivedCategory.isLE_iff _ _).2 fun q hq ↦
    Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj _
      ((DerivedCategory.isLE_iff _ _).1 hA' q hq)

end Etale

end AlgebraicGeometry
