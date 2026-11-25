/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension

/-!
# The exceptional adjoint on the bounded comparison class

Let `f : X ⟶ Y` be a morphism admitting a compactification `X ⟶[j] X̄ ⟶[p] Y`, and let `Λ` be a
finite ring. This file collects the statements of blueprint subsection
`theorem-existence-exceptional-inverse-image` about the pro-étale exceptional adjoint relative to
the class of bounded below objects of étale origin:

* the compact-support comparison `Rf_!(c) K ≅ ν_Y^* Rf_!^{ét}(c) G` for a bounded below `K` of
  étale origin with witness `α : ν_X^* G ≅ K`, natural in the witness (blueprint
  `proposition-comparison-immersions--4`).

## Main definitions

- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section CompactSupportComparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-comparison-immersions--4`: On the coefficient class the
compact-support functor is computed on the étale site.

Let `c = (X ⟶[j] X̄ ⟶[p] Y)` be a compactification of `f`, let `G` be a bounded below complex of
étale sheaves on `X` and let `K` be a pro-étale complex of étale origin with witness
`α : ν_X^* G ≅ K`. Then the pro-étale compact-support functor `Rf_!(c) = Rp_* j_!` attached to
`c` satisfies `Rf_!(c) K ≅ ν_Y^* (Rf_!^{ét}(c) G)`, where `Rf_!^{ét}(c) = Rp_{ét,*} j^{ét}_!` is
the étale compact-support functor attached to the same compactification. It is the
compact-support comparison
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso`
(the identification of the two extensions by zero, followed by the comparison direct image for
the proper `p`) precomposed with `Rf_!(c) α⁻¹`; it is natural in the witness
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso_naturality`). No
constructibility is used. -/
noncomputable def rightDerivedLowerShriekOfCompactificationWitnessIso (c : Compactification f)
    {G : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hG : DerivedCategory.TStructure.t.plus G)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (α : D(ν^*(X)[A]).obj G ≅ K) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K ≅
      D(ν^*(Y)[A]).obj ((Etale.rightDerivedLowerShriekOfCompactification A c).obj G) :=
  (ProEtale.rightDerivedLowerShriekOfCompactification A c).mapIso α.symm ≪≫
    (rightDerivedLowerShriekOfCompactificationComparisonIso A c).app ⟨G, hG⟩

/-- The compact-support comparison of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationWitnessIso` is natural in the
witness: for a morphism of witnesses, given by `g : G ⟶ G'` and `k : K ⟶ K'` with
`α ≫ k = ν^* g ≫ α'`, the comparison isomorphisms intertwine `Rf_!(c) k` and
`ν^* Rf_!^{ét}(c) g`. -/
lemma rightDerivedLowerShriekOfCompactificationWitnessIso_naturality (c : Compactification f)
    {G G' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hG : DerivedCategory.TStructure.t.plus G) (hG' : DerivedCategory.TStructure.t.plus G')
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (α : D(ν^*(X)[A]).obj G ≅ K) (α' : D(ν^*(X)[A]).obj G' ≅ K') (g : G ⟶ G') (k : K ⟶ K')
    (h : α.hom ≫ k = D(ν^*(X)[A]).map g ≫ α'.hom) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).map k ≫
        (rightDerivedLowerShriekOfCompactificationWitnessIso A c hG' α').hom =
      (rightDerivedLowerShriekOfCompactificationWitnessIso A c hG α).hom ≫
        D(ν^*(Y)[A]).map ((Etale.rightDerivedLowerShriekOfCompactification A c).map g) := by
  have hn := (rightDerivedLowerShriekOfCompactificationComparisonIso A c).hom.naturality
    (X := ⟨G, hG⟩) (Y := ⟨G', hG'⟩) (ObjectProperty.homMk g)
  have hk : k ≫ α'.inv = α.inv ≫ D(ν^*(X)[A]).map g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp at hn
  simp only [rightDerivedLowerShriekOfCompactificationWitnessIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hk, Functor.map_comp_assoc]
  exact congrArg _ hn

end CompactSupportComparison

section ClassAdjoint

/- The adjunction `ν^* ⊣ Rν_*` on the unbounded derived categories is obtained by deriving the
pullback via K-flat resolutions, hence the closed symmetric monoidal structure on `A`. -/
variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    DerivedCategory (Sheaf X.smallEtaleTopology A)}

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The pro-étale compact-support functor `Rf_!(c)` attached to a compactification `c` sends a
bounded below object of étale origin to a bounded below object: on `ν^* G` it is
`ν^* Rf_!^{ét}(c) G`, and the étale `Rf_!(c)` preserves bounded below objects. -/
lemma plus_rightDerivedLowerShriekOfCompactification_obj (c : Compactification f)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) :
    DerivedCategory.TStructure.t.plus
      ((ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  refine DerivedCategory.TStructure.t.plus.prop_of_iso
    (rightDerivedLowerShriekOfCompactificationWitnessIso A c hK' e).symm
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj ?_).plus
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility A c).app ⟨K', hK'⟩)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus A c).obj ⟨K', hK'⟩).property

variable (A) in
/-- Blueprint `thm-sf-ambient-adjoint-class` (2): the exceptional adjoint relative to the bounded
below comparison class, attached to a right adjoint `G = f^×` of the étale compact-support
functor `Rf_!^{ét}(c)` of a compactification `c` of `f`:

`Rf^×(c) := ν_X^* ∘ f^× ∘ Rν_{Y,*} : D(Y_proét) ⥤ D(X_proét)`.

It is right adjoint to the pro-étale `Rf_!(c)` relative to the bounded below objects of étale
origin (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfAdjunctionHomEquiv`); for the étale
adjunction of the chosen compactification it is `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`
on the nose. -/
noncomputable def rightDerivedUpperShriekOfAdjunction
    (_adj : Etale.rightDerivedLowerShriekOfCompactification A c ⊣ G) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  R(ν_*(Y)[A]) ⋙ G ⋙ D(ν^*(X)[A])

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The étale object `f^× Rν_* L` of which `Rf^×(c) L` is the comparison pullback is bounded
below when `L` is, for a functor `f^×` preserving bounded below objects. -/
lemma plus_obj_rightDerivedFunctor_comparisonLowerStar_obj
    (hG : ∀ L, DerivedCategory.TStructure.t.plus L → DerivedCategory.TStructure.t.plus (G.obj L))
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus (G.obj (R(ν_*(Y)[A]).obj L)) :=
  hG _ (plus_rightDerivedFunctor_comparisonLowerStar_obj hL)

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- `Rf^×(c)` sends a bounded below object to an object bounded below of étale origin. -/
lemma plusEtaleOrigin_rightDerivedUpperShriekOfAdjunction_obj
    (adj : Etale.rightDerivedLowerShriekOfCompactification A c ⊣ G)
    (hG : ∀ L, DerivedCategory.TStructure.t.plus L → DerivedCategory.TStructure.t.plus (G.obj L))
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.plusEtaleOrigin A X ((rightDerivedUpperShriekOfAdjunction A adj).obj L) :=
  DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
    (plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL)

variable (adj : Etale.rightDerivedLowerShriekOfCompactification A c ⊣ G)
  (hG : ∀ L, DerivedCategory.TStructure.t.plus L → DerivedCategory.TStructure.t.plus (G.obj L))

/-- The counit `ε_L : Rf_!(c) Rf^×(c) L ⟶ L` of the class adjunction at a bounded below `L`: the
composite

```
  Rf_!(c) ν_X^* f^× Rν_* L ≅ ν_Y^* Rf^{ét}_!(c) f^× Rν_* L ──ν^* ε^{ét}──▶ ν_Y^* Rν_* L ──ε^ν──▶ L
```

of the compact-support comparison, the counit of the étale adjunction and the counit of
`ν^* ⊣ Rν_*`. -/
noncomputable def rightDerivedUpperShriekOfAdjunctionCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).obj
        ((rightDerivedUpperShriekOfAdjunction A adj).obj L) ⟶ L :=
  ((rightDerivedLowerShriekOfCompactificationComparisonIso A c).app
      ⟨_, plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL⟩).hom ≫
    D(ν^*(Y)[A]).map (adj.counit.app _) ≫ (derivedComparisonAdjunction A Y).counit.app L

/-- The counit of the class adjunction is natural in the bounded below `L`. -/
@[reassoc]
lemma rightDerivedUpperShriekOfAdjunctionCounit_naturality
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (φ : L ⟶ L') :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).map
        ((rightDerivedUpperShriekOfAdjunction A adj).map φ) ≫
        rightDerivedUpperShriekOfAdjunctionCounit adj hG L' hL' =
      rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL ≫ φ := by
  have h := (rightDerivedLowerShriekOfCompactificationComparisonIso A c).hom.naturality
    (X := ⟨_, plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL⟩)
    (Y := ⟨_, plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL'⟩)
    (ObjectProperty.homMk (G.map (R(ν_*(Y)[A]).map φ)))
  dsimp at h
  simp only [rightDerivedUpperShriekOfAdjunctionCounit, rightDerivedUpperShriekOfAdjunction,
    Functor.comp_map, Iso.app_hom]
  have h2 := adj.counit_naturality (R(ν_*(Y)[A]).map φ)
  have h3 := (derivedComparisonAdjunction A Y).counit_naturality φ
  rw [reassoc_of% h, ← Functor.map_comp_assoc]
  erw [h2]
  rw [Functor.map_comp_assoc]
  erw [h3]
  simp

/-- For `K'` bounded below, `g ↦ Rf_!(c) g ≫ ε_L` sends `ν^* h`, for `h : K' ⟶ f^× Rν_* L`, to
the image of `h` under the chain of adjunction bijections, read through the compact-support
comparison at `K'`. -/
lemma rightDerivedLowerShriekOfCompactification_map_mapDerivedCategory_map_comp_counit
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (h : K' ⟶ G.obj (R(ν_*(Y)[A]).obj L)) :
    (ProEtale.rightDerivedLowerShriekOfCompactification A c).map (D(ν^*(X)[A]).map h) ≫
        rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL =
      ((rightDerivedLowerShriekOfCompactificationComparisonIso A c).app ⟨K', hK'⟩).hom ≫
        ((derivedComparisonAdjunction A Y).homEquiv _ _).symm ((adj.homEquiv _ _).symm h) := by
  have hn := (rightDerivedLowerShriekOfCompactificationComparisonIso A c).hom.naturality
    (X := ⟨K', hK'⟩) (Y := ⟨_, plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL⟩)
    (ObjectProperty.homMk h)
  dsimp at hn
  simp only [rightDerivedUpperShriekOfAdjunctionCounit, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc, Iso.app_hom]
  exact (reassoc_of% hn) _

/-- For `K'` and `L` bounded below, `g ↦ Rf_!(c) g ≫ ε_L` is a bijection
`Hom(ν^* K', Rf^×(c) L) ≃ Hom(Rf_!(c) ν^* K', L)`. -/
lemma bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit_of_plus
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective
      (fun g : D(ν^*(X)[A]).obj K' ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L ↦
        (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
          rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL) := by
  let E := (((adj.homEquiv K' _).symm.trans
    ((derivedComparisonAdjunction A Y).homEquiv _ L).symm).trans
      (((rightDerivedLowerShriekOfCompactificationComparisonIso A c).app
        ⟨K', hK'⟩).symm.homFromEquiv (Z := L)))
  have hcomp :
      (fun g : D(ν^*(X)[A]).obj K' ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L ↦
        (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
          rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL) ∘
        (fun h ↦ D(ν^*(X)[A]).map h) = ⇑E := by
    ext h
    exact rightDerivedLowerShriekOfCompactification_map_mapDerivedCategory_map_comp_counit adj hG
      hK' hL h
  have hν := bijective_comparisonUpperStar_mapDerivedCategory_map K' _
    (plus_obj_rightDerivedFunctor_comparisonLowerStar_obj hG hL)
  refine (Function.Bijective.of_comp_iff _ hν).1 ?_
  rw [hcomp]
  exact E.bijective

/-- For `K` bounded below of étale origin and `L` bounded below, `g ↦ Rf_!(c) g ≫ ε_L` is a
bijection `Hom(K, Rf^×(c) L) ≃ Hom(Rf_!(c) K, L)`. -/
lemma bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : K ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
        rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  have h : (fun g : K ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
        rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL) =
      ⇑((ProEtale.rightDerivedLowerShriekOfCompactification A c).mapIso e).homFromEquiv ∘
        (fun g : D(ν^*(X)[A]).obj K' ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L ↦
          (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
            rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL) ∘
        ⇑e.symm.homFromEquiv := by
    ext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [h]
  exact ((ProEtale.rightDerivedLowerShriekOfCompactification A c).mapIso
    e).homFromEquiv.bijective.comp
    ((bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit_of_plus adj hG hK'
      hL).comp e.symm.homFromEquiv.bijective)

/-- Blueprint `thm-sf-ambient-adjoint-class` (2): the class adjunction
`Hom(Rf_!(c) K, L) ≃ Hom(K, Rf^×(c) L)` for `K` bounded below of étale origin and `L` bounded
below. Its inverse is `g ↦ Rf_!(c) g ≫ ε_L`
(`rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply`), so it is natural in `K` and `L`. -/
noncomputable def rightDerivedUpperShriekOfAdjunctionHomEquiv
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    ((ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K ⟶ L) ≃
      (K ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L) :=
  (Equiv.ofBijective _
    (bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit adj hG hK hL)).symm

@[simp]
lemma rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L)
    (g : K ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L) :
    (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL).symm g =
      (ProEtale.rightDerivedLowerShriekOfCompactification A c).map g ≫
        rightDerivedUpperShriekOfAdjunctionCounit adj hG L hL :=
  rfl


/-- Naturality of the class adjunction in the source. -/
lemma rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_left_symm
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) (hK' : DerivedCategory.plusEtaleOrigin A X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (φ : K ⟶ K')
    (g : K' ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L) :
    (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL).symm (φ ≫ g) =
      (ProEtale.rightDerivedLowerShriekOfCompactification A c).map φ ≫
        (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK' hL).symm g := by
  rw [rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply,
    rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply, Functor.map_comp, Category.assoc]

/-- Naturality of the class adjunction in the target. -/
lemma rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_right_symm
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (g : K ⟶ (rightDerivedUpperShriekOfAdjunction A adj).obj L) (φ : L ⟶ L') :
    (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL').symm
        (g ≫ (rightDerivedUpperShriekOfAdjunction A adj).map φ) =
      (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL).symm g ≫ φ := by
  rw [rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply,
    rightDerivedUpperShriekOfAdjunctionHomEquiv_symm_apply, Functor.map_comp, Category.assoc,
    rightDerivedUpperShriekOfAdjunctionCounit_naturality adj hG hL hL', Category.assoc]

/-- Naturality of the class adjunction in the target, forward direction. -/
lemma rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_right
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (g : (ProEtale.rightDerivedLowerShriekOfCompactification A c).obj K ⟶ L) (φ : L ⟶ L') :
    rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL' (g ≫ φ) =
      rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG hK hL g ≫
        (rightDerivedUpperShriekOfAdjunction A adj).map φ := by
  rw [← Equiv.eq_symm_apply,
    rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_right_symm adj hG hK hL hL',
    Equiv.symm_apply_apply]

variable (A) in
/-- The pro-étale compact-support functor `Rf_!(c)` restricted to the bounded below objects of
étale origin, with values in the bounded below objects
(`AlgebraicGeometry.ProEtale.plus_rightDerivedLowerShriekOfCompactification_obj`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin
    (c : Compactification f) :
    (DerivedCategory.plusEtaleOrigin A X).FullSubcategory ⥤
      (DerivedCategory.TStructure.t.plus (C := DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y) A))).FullSubcategory :=
  DerivedCategory.TStructure.t.plus.lift
    ((DerivedCategory.plusEtaleOrigin A X).ι ⋙
      ProEtale.rightDerivedLowerShriekOfCompactification A c)
    (fun K ↦ plus_rightDerivedLowerShriekOfCompactification_obj c K.property)

/-- The class exceptional adjoint `Rf^×(c)` restricted to the bounded below objects, with values
in the bounded below objects of étale origin. -/
noncomputable def rightDerivedUpperShriekOfAdjunctionPlus :
    (DerivedCategory.TStructure.t.plus (C := DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y) A))).FullSubcategory ⥤
      (DerivedCategory.plusEtaleOrigin A X).FullSubcategory :=
  (DerivedCategory.plusEtaleOrigin A X).lift
    (DerivedCategory.TStructure.t.plus.ι ⋙ rightDerivedUpperShriekOfAdjunction A adj)
    (fun L ↦ plusEtaleOrigin_rightDerivedUpperShriekOfAdjunction_obj adj hG L.property)

/-- Blueprint `thm-sf-ambient-adjoint-class` (2), on full subcategories: the restrictions of
`Rf_!(c)` to the bounded below objects of étale origin and of `Rf^×(c)` to the bounded below
objects are adjoint. Its counit is `rightDerivedUpperShriekOfAdjunctionCounit`.

Blueprint `rem-ptr-weil-ambient-exceptional-adjoint-12`: Pointer to the properties of
[def-weil-ambient-exceptional-adjoint]

Blueprint `rem-sf-class-adjoint-residue` and `rem-ptr-weil-ambient-exceptional-adjoint-12`: this
is an adjunction between the bounded below objects of étale origin and the bounded below objects
only; no adjunction on arbitrary unbounded pro-étale objects is asserted, and statements
quantifying over complexes outside the class keep the ambient datum
`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint` as a hypothesis. -/
noncomputable def rightDerivedUpperShriekOfAdjunctionClassAdjunction :
    rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin A c ⊣
      rightDerivedUpperShriekOfAdjunctionPlus adj hG :=
  Adjunction.mkOfHomEquiv
    { homEquiv K L :=
        { toFun g := ObjectProperty.homMk
            (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG K.property L.property g.hom)
          invFun g := ObjectProperty.homMk
            ((rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG K.property L.property).symm g.hom)
          left_inv g := by
            ext
            exact (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG _ _).symm_apply_apply g.hom
          right_inv g := by
            ext
            exact (rightDerivedUpperShriekOfAdjunctionHomEquiv adj hG _ _).apply_symm_apply g.hom }
      homEquiv_naturality_left_symm {K K' L} φ g := by
        ext
        exact rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_left_symm adj hG _ _ _
          φ.hom g.hom
      homEquiv_naturality_right {K L L'} g φ := by
        ext
        exact rightDerivedUpperShriekOfAdjunctionHomEquiv_naturality_right adj hG _ _ _
          g.hom φ.hom }

end ClassAdjoint

section Compactifications

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  [QuasiCompact f]

/-- The compactification comparison `Rf_!(c) ≅ Rf_!(d)` of the pro-étale compact-support functors
on the bounded below objects of étale origin
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso`, transported
from the étale comparisons of blueprint `proposition-construction-independence-rf-shriek--7`), with
values in the bounded below objects. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso
    (c d : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin (ModuleCat.{u + 1} Λ) c ≅
      rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin (ModuleCat.{u + 1} Λ) d :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c d).app K))
    (fun φ ↦ by
      ext
      exact (rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c d).hom.naturality φ)

@[simp]
lemma rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_hom_app_hom
    (c d : Compactification f)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    ((rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ c d).hom.app K).hom =
      (rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ c d).hom.app K :=
  rfl

/-- The comparison of a compactification with itself is the identity. -/
@[simp]
lemma rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_refl (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ c c = Iso.refl _ := by
  ext : 2
  ext
  rw [rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_hom_app_hom,
    rightDerivedLowerShriekOfCompactificationEtaleOriginIso_refl]
  rfl

/-- The cocycle condition for the comparisons of the compact-support functors. -/
lemma rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_trans
    (c₁ c₂ c₃ : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ c₁ c₂ ≪≫
        rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ c₂ c₃ =
      rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ c₁ c₃ := by
  ext : 2
  ext
  rw [rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_hom_app_hom Λ c₁ c₃,
    ← rightDerivedLowerShriekOfCompactificationEtaleOriginIso_trans Λ c₁ c₂ c₃]
  rfl

variable [HasCompactification f] [CompactSpace Y]

/-- Blueprint `thm-sf-ambient-adjoint-class` (2): for a compactification `c` of `f`, the class
adjunction between the pro-étale `Rf_!(c)` on bounded below objects of étale origin and
`Rf^×(c) = ν_X^* f^× Rν_{Y,*}` on bounded below objects, where `f^×` is the étale exceptional
inverse image with its adjunction `Rf_!^{ét}(c) ⊣ f^×`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunctionOfCompactification`). As a functor,
`Rf^×(c)` is `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` for every `c`. -/
noncomputable def classUpperShriekAdjunction (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin (ModuleCat.{u + 1} Λ) c ⊣
      rightDerivedUpperShriekOfAdjunctionPlus
        (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)
        (Etale.plus_rightDerivedUpperShriek_obj _ f) :=
  rightDerivedUpperShriekOfAdjunctionClassAdjunction _ _

/-- Blueprint `thm-sf-ambient-adjoint-class` (3): the compactification comparison
`Rf^×(c) ≅ Rf^×(d)` of the class exceptional adjoints, the conjugate of the comparison
`Rf_!(d) ≅ Rf_!(c)` of the compact-support functors under the class adjunctions. -/
noncomputable def classUpperShriekIso (c d : Compactification f) :
    rightDerivedUpperShriekOfAdjunctionPlus
        (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)
        (Etale.plus_rightDerivedUpperShriek_obj _ f) ≅
      rightDerivedUpperShriekOfAdjunctionPlus
        (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ d)
        (Etale.plus_rightDerivedUpperShriek_obj _ f) :=
  conjugateIsoEquiv (classUpperShriekAdjunction Λ c) (classUpperShriekAdjunction Λ d)
    (rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ d c)

/-- The comparison of a compactification with itself is the identity. -/
@[simp]
lemma classUpperShriekIso_refl (c : Compactification f) :
    classUpperShriekIso Λ c c = Iso.refl _ := by
  ext : 1
  simp [classUpperShriekIso]

/-- Blueprint `thm-sf-ambient-adjoint-class` (3): the cocycle condition for the compactification
comparisons of the class exceptional adjoints. -/
lemma classUpperShriekIso_trans (c₁ c₂ c₃ : Compactification f) :
    classUpperShriekIso Λ c₁ c₂ ≪≫ classUpperShriekIso Λ c₂ c₃ = classUpperShriekIso Λ c₁ c₃ := by
  ext : 1
  rw [Iso.trans_hom]
  simp only [classUpperShriekIso, conjugateIsoEquiv_apply_hom]
  rw [conjugateEquiv_comp, ← Iso.trans_hom,
    rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso_trans]

/-- The units and counits of the class adjunctions are compatible with the compactification
comparisons: the counit for `c` is the counit for `d` transported along the comparisons. -/
lemma classUpperShriekIso_hom_counit (c d : Compactification f)
    (L : (DerivedCategory.TStructure.t.plus (C := DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactificationPlusEtaleOrigin (ModuleCat.{u + 1} Λ) d).map
        ((classUpperShriekIso Λ c d).hom.app L) ≫ (classUpperShriekAdjunction Λ d).counit.app L =
      (rightDerivedLowerShriekOfCompactificationPlusEtaleOriginIso Λ d c).hom.app _ ≫
        (classUpperShriekAdjunction Λ c).counit.app L := by
  simp [classUpperShriekIso]

end Compactifications

section Theorem

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]
  {f : X ⟶ Y} [QuasiCompact f] [HasCompactification f]
  [CompactSpace Y]

include aY

/-- Blueprint `thm-sf-ambient-adjoint-class`: The exceptional adjoint on the bounded comparison
class.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes, `k` separably closed, with a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` with `dim X̄ ≤ d`, and let `Λ` be a finite ring whose
exponent is invertible on `Y`. Then:

1. the class-restricted dimension datum `FullCD_cls(p, Λ; 2d)` holds
   (`AlgebraicGeometry.ProEtale.hasCohomologicalDimensionLEOnEtaleOrigin`);
2. with `f^×` the right adjoint of the étale compact-support functor `Rf_!^{ét}(c)`, the functor
   `Rf^×(c) = ν_X^* f^× Rν_{Y,*}` is right adjoint to `Rf_!(c)` relative to the bounded below
   comparison class: for `K` bounded below of étale origin and `L` bounded below,
   `g ↦ Rf_!(c) g ≫ ε_L` is a bijection `Hom(K, Rf^×(c) L) ≃ Hom(Rf_!(c) K, L)`
   (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekOfAdjunctionHomEquiv`, natural in `K`
   and `L`);
3. the compactification comparisons of these functors
   (`AlgebraicGeometry.ProEtale.classUpperShriekIso`, the conjugates of the compactification
   comparisons of the compact-support functors) satisfy the cocycle condition.

No adjunction on arbitrary unbounded pro-étale objects is asserted. That `f^×` preserves bounded
below objects uses that `Y` is quasi-compact
(`AlgebraicGeometry.Etale.plus_rightDerivedUpperShriek_obj`). -/
theorem hasCohomologicalDimensionLEOnEtaleOrigin_and_bijective_classAdjunction
    (c : Compactification f) (d : ℕ) (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ) c.g (2 * d) ∧
    (∀ (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (_ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
      (hL : DerivedCategory.TStructure.t.plus L),
      Function.Bijective (fun g : K ⟶ (rightDerivedUpperShriekOfAdjunction _
          (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)).obj L ↦
        (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g ≫
          rightDerivedUpperShriekOfAdjunctionCounit
            (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)
            (Etale.plus_rightDerivedUpperShriek_obj _ f) L hL)) ∧
    ∀ c₁ c₂ c₃ : Compactification f,
      classUpperShriekIso Λ c₁ c₂ ≪≫ classUpperShriekIso Λ c₂ c₃ = classUpperShriekIso Λ c₁ c₃ := by
  have := c.isProper
  have : HasInvertibleExponent Λ c.Z := HasInvertibleExponent.of_hom c.g
  exact ⟨hasCohomologicalDimensionLEOnEtaleOrigin Λ c.g (c.g ≫ aY) aY rfl d hd,
    fun K L hK hL ↦ bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit _ _ hK hL,
    classUpperShriekIso_trans Λ⟩

variable [QuasiCompact aY]

/-- Blueprint `cor-sf-ambient-adjoint-discharge`: The ambient datum relative to the bounded
comparison class.

For the bounded constructible coefficient class at a finite stage `Λ`, both halves of clause (1)
of exceptional-adjoint admissibility hold relative to the class: the vanishing half is the
class-restricted datum `FullCD_cls(p, Λ; 2d)` (blueprint
`lemma-uniform-bounds-pro-etale-affines--2`) and the existence half is the exceptional adjoint
relative to the class (blueprint `thm-sf-ambient-adjoint-class`), which restricts to an adjunction
`Rf_! ⊣ Rf^!` on the bounded constructible complexes of finite Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`). The
unrestricted ambient datum `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint` is not
asserted: it is false in general (an elliptic curve over `𝔽̄_p` with `Λ = 𝔽_r`).

This is also the content of the pointer remarks blueprint `rem-ptr-pur-conventions-5`,
`rem-ptr-pur-td-datum-6`, `rem-ptr-trf-admissibility-12` and
`rem-ptr-weil-exceptional-inverse-image-14`: on the bounded constructible and finite-Tor
categories both halves of the datum are theorems.

Blueprint `rem-ptr-pur-conventions-5`: Pointer to the properties of [def-pur-conventions]

Blueprint `rem-ptr-pur-td-datum-6`: Pointer to the properties of [def-pur-td-datum]

Blueprint `rem-ptr-trf-admissibility-12`: Pointer to the properties of
[theorem-f-shriek-finite-coefficients]

Blueprint `rem-ptr-weil-exceptional-inverse-image-14`: Pointer to the properties of
[theorem-f-shriek-finite-coefficients] -/
theorem hasCohomologicalDimensionLEOnEtaleOrigin_and_nonempty_adjunction_constructibleFiniteTor
    (d : ℕ) (hd : topologicalKrullDim (HasCompactification.compactification f).Z ≤
      (d : WithBot ℕ∞)) :
    HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification f).g (2 * d) ∧
      Nonempty ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
        (fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f K.property) ⊣
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
          rightDerivedUpperShriek Λ f)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f L.property)) :=
  ⟨(hasCohomologicalDimensionLEOnEtaleOrigin_and_bijective_classAdjunction Λ aY _ d hd).1,
    ⟨DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f⟩⟩

omit [QuasiCompact aY] in
/-- Blueprint `rem-ptr-weil-ambient-exceptional-adjoint-11`: on the coefficient class of étale
origin both halves of the ambient exceptional right adjoint datum are theorems: the vanishing
half is the class-restricted datum `FullCD_cls(p, Λ; 2d)`, with the sharp comparison bound
`M = 0` (`R^q ν_* ν^* G = 0` for `q > 0`, blueprint
`theorem-bounded-below-cohomology-comparison--1`), and the existence half, with its counit and
compactification comparisons, is blueprint `thm-sf-ambient-adjoint-class`. -/
theorem hasCohomologicalDimensionLEOnEtaleOrigin_and_comparisonBound_and_bijective
    (c : Compactification f) (d : ℕ) (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    HasCohomologicalDimensionLEOnEtaleOrigin (ModuleCat.{u + 1} Λ) c.g (2 * d) ∧
    (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), 0 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G))))) ∧
    ∀ (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (_ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
      (hL : DerivedCategory.TStructure.t.plus L),
      Function.Bijective (fun g : K ⟶ (rightDerivedUpperShriekOfAdjunction _
          (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)).obj L ↦
        (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g ≫
          rightDerivedUpperShriekOfAdjunctionCounit
            (Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c)
            (Etale.plus_rightDerivedUpperShriek_obj _ f) L hL) :=
  have h := hasCohomologicalDimensionLEOnEtaleOrigin_and_bijective_classAdjunction Λ aY c d hd
  ⟨h.1, isZero_homology_rightDerivedComparisonLowerStar Λ X, h.2.1⟩

end Theorem

end ProEtale

end AlgebraicGeometry
