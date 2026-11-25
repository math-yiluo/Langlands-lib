/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarIdCoherence

/-!
# The commutation of `ν^*` with pullbacks and sections

For a section `s` of `p : X ⟶ Y`, pulling back along `p` and then along `s` is the identity,
`Lp^* ⋙ Ls^* ≅ L(s ≫ p)^* = L(𝟙)^* ≅ 𝟭`, on étale sheaves
(`Etale.leftDerivedUpperStarCompSectionIso`) and on pro-étale sheaves
(`ProEtale.leftDerivedUpperStarCompSectionIso`). This file shows that the commutations
`D(ν^*) ⋙ Lg^*_{proét} ≅ Lg^*_{ét} ⋙ D(ν^*)` are compatible with these isomorphisms and with the
exchanges of composition isomorphisms, using their compatibility with composition and with
identities.

## Main statements

- `ProEtale.derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso`: `D(ν^*)` carries the
  étale section isomorphisms to the pro-étale ones.
- `ProEtale.leftDerivedUpperStarComp_inv_app_comp_congr_comp_hom_app_comparisonUpperStar`: the
  same for exchanges `Lg₁^* Lg₂^* ≅ Lg₁'^* Lg₂'^*` along `g₁ ≫ g₂ = g₁' ≫ g₂'`.
- `ProEtale.leftDerivedUpperStar_map_comp_compSectionIso_comparisonUpperStar`: sections commute
  with base change, on complexes of étale origin.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Transport along the inverse equality is the inverse transport. -/
lemma leftDerivedUpperStarCongr_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    leftDerivedUpperStarCongr A h.symm = (leftDerivedUpperStarCongr A h).symm := by
  subst h
  rfl

/-- For a section `s` of `p`, pulling back along `p` and then along `s` is the identity:
`Lp^* ⋙ Ls^* ≅ L(s ≫ p)^* = L(𝟙)^* ≅ 𝟭` on pro-étale sheaves. -/
noncomputable def leftDerivedUpperStarCompSectionIso {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y)
    (h : s ≫ p = 𝟙 Y) :
    (ProEtale.upperStar A p).leftDerivedFunctor ⋙ (ProEtale.upperStar A s).leftDerivedFunctor ≅
      𝟭 _ :=
  (leftDerivedUpperStarComp A s p).symm ≪≫ leftDerivedUpperStarCongr A h ≪≫
    leftDerivedUpperStarId A Y

/-- The compatibility of the commutations `D(ν^*) ⋙ Lg^* ≅ Lg^* ⋙ D(ν^*)` with the composition
isomorphisms, for a composite `g₁₂ = g₁ ≫ g₂` given up to equality. -/
lemma derivedComparisonUpperStarUpperStarIso_inv_app_comp {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (derivedComparisonUpperStarUpperStarIso A g₁₂).inv.app M ≫
        (leftDerivedUpperStarCongr A hg).hom.app _ ≫
        (leftDerivedUpperStarComp A g₁ g₂).hom.app _ =
      (comparisonUpperStar A T).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app M) ≫
        (derivedComparisonUpperStarUpperStarIso A g₁).inv.app _ ≫
        (ProEtale.upperStar A g₁).leftDerivedFunctor.map
          ((derivedComparisonUpperStarUpperStarIso A g₂).inv.app M) := by
  subst hg
  simpa using derivedComparisonUpperStarUpperStarIso_compCoherence A g₁ g₂ M

/-- **`D(ν^*)` carries the section isomorphisms of étale pullbacks to those of pro-étale
pullbacks**: for a section `s` of `p : X ⟶ Y` and `K` on `Y_ét`, the square
```
Ls^* ν^* Lp^* K --(Ls^* (ν^* Lp^* ≅ Lp^* ν^*))--> Ls^* Lp^* ν^* K
      |                                               |
(Ls^* ν^* ≅ ν^* Ls^*)                         (Ls^* Lp^* ≅ 𝟭)
      v                                               v
ν^* Ls^* Lp^* K ------------(ν^* (Ls^* Lp^* ≅ 𝟭))------> ν^* K
```
commutes. -/
lemma derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso
    {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (ProEtale.upperStar A s).leftDerivedFunctor.map
          ((derivedComparisonUpperStarUpperStarIso A p).inv.app K) ≫
        (leftDerivedUpperStarCompSectionIso A s p h).hom.app
          ((comparisonUpperStar A Y).mapDerivedCategory.obj K) =
      (derivedComparisonUpperStarUpperStarIso A s).hom.app _ ≫
        (comparisonUpperStar A Y).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarCompSectionIso A s p h).hom.app K) := by
  have H := derivedComparisonUpperStarUpperStarIso_inv_app_comp A s p (𝟙 Y) h.symm K
  rw [leftDerivedUpperStarCongr_symm A h] at H
  have H2 : (leftDerivedUpperStarComp A s p).inv.app _ ≫ (leftDerivedUpperStarCongr A h).hom.app _ ≫
      (derivedComparisonUpperStarUpperStarIso A (𝟙 Y)).hom.app K =
      (ProEtale.upperStar A s).leftDerivedFunctor.map
          ((derivedComparisonUpperStarUpperStarIso A p).hom.app K) ≫
        (derivedComparisonUpperStarUpperStarIso A s).hom.app _ ≫
        (comparisonUpperStar A Y).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarComp A s p (𝟙 Y) h.symm).inv.app K) := by
    rw [← cancel_epi ((derivedComparisonUpperStarUpperStarIso A (𝟙 Y)).inv.app K ≫
      (leftDerivedUpperStarCongr A h).inv.app _ ≫ (leftDerivedUpperStarComp A s p).hom.app _)]
    simp only [Iso.symm_hom] at H
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app]
    rw [reassoc_of% H]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rfl
  have I := derivedComparisonUpperStarUpperStarIso_hom_app_id A Y K
  simp only [leftDerivedUpperStarCompSectionIso, Etale.leftDerivedUpperStarCompSectionIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← I, reassoc_of% H2]
  simp

/-- **`D(ν^*)` carries exchanges of composition isomorphisms to exchanges**: for
`g₁ ≫ g₂ = g₁' ≫ g₂'`, the pro-étale exchange `Lg₁^* Lg₂^* ≅ L(g₁ ≫ g₂)^* = L(g₁' ≫ g₂')^* ≅
Lg₁'^* Lg₂'^*` at `ν^* M` is the étale exchange at `M`, read through the commutations
`Lg^* ν^* ≅ ν^* Lg^*`. -/
lemma leftDerivedUpperStarComp_inv_app_comp_congr_comp_hom_app_comparisonUpperStar
    {T S S' R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁' : T ⟶ S') (g₂' : S' ⟶ R)
    (hg : g₁ ≫ g₂ = g₁' ≫ g₂') (M : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A g₁ g₂).inv.app _ ≫ (leftDerivedUpperStarCongr A hg).hom.app _ ≫
        (leftDerivedUpperStarComp A g₁' g₂').hom.app
          ((comparisonUpperStar A R).mapDerivedCategory.obj M) =
      (ProEtale.upperStar A g₁).leftDerivedFunctor.map
          ((derivedComparisonUpperStarUpperStarIso A g₂).hom.app M) ≫
        (derivedComparisonUpperStarUpperStarIso A g₁).hom.app _ ≫
        (comparisonUpperStar A T).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarComp A g₁ g₂).inv.app M ≫
            (Etale.leftDerivedUpperStarComp A g₁' g₂' (g₁ ≫ g₂) hg).hom.app M) ≫
        (derivedComparisonUpperStarUpperStarIso A g₁').inv.app _ ≫
        (ProEtale.upperStar A g₁').leftDerivedFunctor.map
          ((derivedComparisonUpperStarUpperStarIso A g₂').inv.app M) := by
  have H₁ := derivedComparisonUpperStarUpperStarIso_inv_app_comp A g₁ g₂ (g₁ ≫ g₂) rfl M
  have H₂ := derivedComparisonUpperStarUpperStarIso_inv_app_comp A g₁' g₂' (g₁ ≫ g₂) hg M
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app] at H₁
  erw [Category.id_comp] at H₁
  -- `H₁` expresses the pro-étale composition at `g₁ ≫ g₂` through the étale one
  rw [← cancel_epi ((leftDerivedUpperStarComp A g₁ g₂).hom.app _),
    Iso.hom_inv_id_app_assoc, ← cancel_epi ((derivedComparisonUpperStarUpperStarIso A
      (g₁ ≫ g₂)).inv.app M), H₂, reassoc_of% H₁]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc (ProEtale.upperStar A g₁).leftDerivedFunctor, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

-- the proof elaborates a long chain of naturality squares between derived categories
/-- **Sections commute with base change, on complexes of étale origin.** Let `a : P ⟶ B` have a
section `i`, let `a' : P' ⟶ B'` have a section `i'`, and let `v : P' ⟶ P` lie over
`u : B' ⟶ B` and carry `i'` to `i`. For `C` on `B_ét`, the two identifications
`Li'^* Lv^* La^* ν^* C ≅ Lu^* ν^* C` of pro-étale complexes agree: this is
`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_compSectionIso`, transported along
`D(ν^*)`. -/
lemma leftDerivedUpperStar_map_comp_compSectionIso_comparisonUpperStar {B B' P P' : Scheme.{u}}
    (u : B' ⟶ B) (a : P ⟶ B) (a' : P' ⟶ B') (v : P' ⟶ P) (i : B ⟶ P) (i' : B' ⟶ P')
    (hv : v ≫ a = a' ≫ u) (hi : i' ≫ v = u ≫ i) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B')
    (C : DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    (ProEtale.upperStar A i').leftDerivedFunctor.map
          ((leftDerivedUpperStarComp A v a).inv.app _ ≫
            (leftDerivedUpperStarCongr A hv).hom.app _ ≫
            (leftDerivedUpperStarComp A a' u).hom.app
              ((comparisonUpperStar A B).mapDerivedCategory.obj C)) ≫
        (leftDerivedUpperStarCompSectionIso A i' a' h').hom.app _ =
      ((leftDerivedUpperStarComp A i' v).inv.app _ ≫ (leftDerivedUpperStarCongr A hi).hom.app _ ≫
          (leftDerivedUpperStarComp A u i).hom.app _) ≫
        (ProEtale.upperStar A u).leftDerivedFunctor.map
          ((leftDerivedUpperStarCompSectionIso A i a h).hom.app
            ((comparisonUpperStar A B).mapDerivedCategory.obj C)) := by
  let ν := (comparisonUpperStar A B).mapDerivedCategory
  let ν' := (comparisonUpperStar A B').mapDerivedCategory
  let da := derivedComparisonUpperStarUpperStarIso A a
  let du := derivedComparisonUpperStarUpperStarIso A u
  let di := derivedComparisonUpperStarUpperStarIso A i
  let di' := derivedComparisonUpperStarUpperStarIso A i'
  let dv := derivedComparisonUpperStarUpperStarIso A v
  let E₁ := (Etale.leftDerivedUpperStarComp A v a).inv.app C ≫
    (Etale.leftDerivedUpperStarComp A a' u (v ≫ a) hv).hom.app C
  let E₂ := (Etale.leftDerivedUpperStarComp A i' v).inv.app _ ≫
    (Etale.leftDerivedUpperStarComp A u i (i' ≫ v) hi).hom.app
      ((Etale.upperStar A a).leftDerivedFunctor.obj C)
  have S₁ := leftDerivedUpperStarComp_inv_app_comp_congr_comp_hom_app_comparisonUpperStar A
    v a a' u hv C
  have S₂ := leftDerivedUpperStarComp_inv_app_comp_congr_comp_hom_app_comparisonUpperStar A
    i' v u i hi ((Etale.upperStar A a).leftDerivedFunctor.obj C)
  have K' := derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso A i' a' h'
    ((Etale.upperStar A u).leftDerivedFunctor.obj C)
  have K := derivedComparisonUpperStarUpperStarIso_inv_app_compSectionIso A i a h C
  have nε' := (leftDerivedUpperStarCompSectionIso A i' a' h').hom.naturality (du.inv.app C)
  have ndi' := di'.hom.naturality E₁
  have ndu := du.inv.naturality ((Etale.leftDerivedUpperStarCompSectionIso A i a h).hom.app C)
  have nY₁ := (leftDerivedUpperStarComp A i' v).inv.naturality (da.hom.app C)
  have nY₂ := (leftDerivedUpperStarCongr A hi).hom.naturality (da.hom.app C)
  have nY₃ := (leftDerivedUpperStarComp A u i).hom.naturality (da.hom.app C)
  have E := Etale.leftDerivedUpperStar_map_comp_compSectionIso A u a a' v i i' hv hi h h' C
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map,
    Functor.id_obj] at nε' ndi' ndu nY₁ nY₂ nY₃
  have Kr : (leftDerivedUpperStarCompSectionIso A i a h).hom.app (ν.obj C) =
      (ProEtale.upperStar A i).leftDerivedFunctor.map (da.hom.app C) ≫ di.hom.app _ ≫
        ν.map ((Etale.leftDerivedUpperStarCompSectionIso A i a h).hom.app C) := by
    rw [← K, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [S₁, Kr]
  simp only [E₁, Functor.map_comp, Category.assoc] at ndi' E S₂ ⊢
  rw [nε', reassoc_of% K', reassoc_of% ndi', ← reassoc_of% nY₃, ← reassoc_of% nY₂,
    ← reassoc_of% nY₁, reassoc_of% S₂]
  have hc {Z : _} (z : _ ⟶ Z) : (ProEtale.upperStar A u).leftDerivedFunctor.map
        (di.inv.app ((Etale.upperStar A a).leftDerivedFunctor.obj C)) ≫
      (ProEtale.upperStar A u).leftDerivedFunctor.map
        (di.hom.app ((Etale.upperStar A a).leftDerivedFunctor.obj C)) ≫ z = z := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [hc, ← ndu]
  have E' := congrArg ν'.map E
  simp only [Functor.map_comp] at E'
  rw [reassoc_of% E']

end AlgebraicGeometry.ProEtale
