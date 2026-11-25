/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.CompactPullback
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Coherences for the fibres of the lower shriek of Weil objects

For the relative Frobenius `r : X ⟶ X'` of `f = r ≫ f'` and the fibre `Z` of `f` over a point
`y` fixed by `Φ_Y`, the base change of `Rf'_!(η_r)` to `Z` is the pullback `Φ_Z^♯` on compactly
supported cohomology (`ProEtale.CondensedRing.baseChange_comp_relativeFrobenius_stalk`). This is
the core of the proof of `lemma-comparison-via-relative-frobenius--4`, item (2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The compatibility of two pullback comparisons with the composition isomorphisms, for abstract
families of pullback functors. -/
lemma pullbackSquareComparison_comp_aux {𝒞 : Type*}
    [Category 𝒞] {Z' X₁ X₂ : 𝒞} {DZ D₁ D₂ : Type*} [Category DZ] [Category D₁] [Category D₂]
    (UZZ : (Z' ⟶ Z') → DZ ⥤ DZ) (UZ₁ : (Z' ⟶ X₁) → D₁ ⥤ DZ) (UZ₂ : (Z' ⟶ X₂) → D₂ ⥤ DZ)
    (U₁₂ : (X₁ ⟶ X₂) → D₂ ⥤ D₁) (U₂₁ : (X₂ ⟶ X₁) → D₁ ⥤ D₂) (U₂₂ : (X₂ ⟶ X₂) → D₂ ⥤ D₂)
    (c₁ : ∀ (a : Z' ⟶ Z') (b : Z' ⟶ X₁), UZ₁ (a ≫ b) ≅ UZ₁ b ⋙ UZZ a)
    (c₂ : ∀ (a : Z' ⟶ X₁) (b : X₁ ⟶ X₂), UZ₂ (a ≫ b) ≅ U₁₂ b ⋙ UZ₁ a)
    (c₃ : ∀ (a : Z' ⟶ Z') (b : Z' ⟶ X₂), UZ₂ (a ≫ b) ≅ UZ₂ b ⋙ UZZ a)
    (c₄ : ∀ (a : Z' ⟶ X₂) (b : X₂ ⟶ X₁), UZ₁ (a ≫ b) ≅ U₂₁ b ⋙ UZ₂ a)
    (c₅ : ∀ (a : X₂ ⟶ X₁) (b : X₁ ⟶ X₂), U₂₂ (a ≫ b) ≅ U₁₂ b ⋙ U₂₁ a)
    (c₆ : ∀ (a : Z' ⟶ X₂) (b : X₂ ⟶ X₂), UZ₂ (a ≫ b) ≅ U₂₂ b ⋙ UZ₂ a)
    (A₁ : ∀ (a : Z' ⟶ Z') (b : Z' ⟶ X₁) (c : X₁ ⟶ X₂) (K : D₂),
      (c₂ (a ≫ b) c).hom.app K ≫ (c₁ a b).hom.app ((U₁₂ c).obj K) =
        eqToHom (congrArg (fun f ↦ (UZ₂ f).obj K) (Category.assoc a b c)) ≫
          (c₃ a (b ≫ c)).hom.app K ≫ (UZZ a).map ((c₂ b c).hom.app K))
    (A₂ : ∀ (a : Z' ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₂) (K : D₂),
      (c₂ (a ≫ b) c).hom.app K ≫ (c₄ a b).hom.app ((U₁₂ c).obj K) =
        eqToHom (congrArg (fun f ↦ (UZ₂ f).obj K) (Category.assoc a b c)) ≫
          (c₆ a (b ≫ c)).hom.app K ≫ (UZ₂ a).map ((c₅ b c).hom.app K))
    {ΦZ : Z' ⟶ Z'} {j : Z' ⟶ X₁} {p : X₁ ⟶ X₂} {r : X₂ ⟶ X₁} (w : ΦZ ≫ j = (j ≫ p) ≫ r)
    (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p) (K : D₂) :
    ((c₁ ΦZ j).inv.app ((U₁₂ p).obj K) ≫
        eqToHom (congrArg (fun f ↦ (UZ₁ f).obj ((U₁₂ p).obj K)) w) ≫
        (c₄ (j ≫ p) r).hom.app ((U₁₂ p).obj K)) ≫ (UZ₂ (j ≫ p)).map ((c₅ r p).inv.app K) =
      (UZZ ΦZ).map ((c₂ j p).inv.app K) ≫ ((c₃ ΦZ (j ≫ p)).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (UZ₂ f).obj K) hi) ≫ (c₆ (j ≫ p) (r ≫ p)).hom.app K) := by
  have a₂ : (c₄ (j ≫ p) r).hom.app ((U₁₂ p).obj K) ≫ (UZ₂ (j ≫ p)).map ((c₅ r p).inv.app K) =
      (c₂ ((j ≫ p) ≫ r) p).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (UZ₂ f).obj K) (Category.assoc (j ≫ p) r p)) ≫
        (c₆ (j ≫ p) (r ≫ p)).hom.app K := by
    rw [← cancel_epi ((c₂ ((j ≫ p) ≫ r) p).hom.app K), reassoc_of% (A₂ (j ≫ p) r p K)]
    simp [← Functor.map_comp]
  have a₁ : (UZZ ΦZ).map ((c₂ j p).inv.app K) ≫ (c₃ ΦZ (j ≫ p)).inv.app K =
      (c₁ ΦZ j).inv.app ((U₁₂ p).obj K) ≫ (c₂ (ΦZ ≫ j) p).inv.app K ≫
        eqToHom (congrArg (fun f ↦ (UZ₂ f).obj K) (Category.assoc ΦZ j p)) := by
    rw [← cancel_mono ((c₃ ΦZ (j ≫ p)).hom.app K ≫ (UZZ ΦZ).map ((c₂ j p).hom.app K))]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    rw [← A₁]
    simp
  have hcast {b b' : Z' ⟶ X₁} (e : b = b') :
      eqToHom (congrArg (fun f ↦ (UZ₁ f).obj ((U₁₂ p).obj K)) e) ≫ (c₂ b' p).inv.app K =
        (c₂ b p).inv.app K ≫ eqToHom (congrArg (fun f ↦ (UZ₂ (f ≫ p)).obj K) e) := by
    subst e
    simp
  simp only [Category.assoc]
  rw [a₂, reassoc_of% (hcast w), reassoc_of% a₁]
  simp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The pullback comparisons of the square `(j ≫ p) ≫ r = Φ_Z ≫ j` and of
`Φ_Z ≫ (j ≫ p) = (j ≫ p) ≫ (r ≫ p)` are compatible with the composition isomorphisms. -/
lemma pullbackSquareComparison_hom_app_comp_map_upperStarComp_inv_app {ΦZ : Z ⟶ Z} {j : Z ⟶ X'}
    {p : X' ⟶ X} {r : X ⟶ X'} (w : CommSq (j ≫ p) ΦZ r j)
    (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ w).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K) =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦZ).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ j p).inv.app K) ≫
      (weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app, weilUpperStarComparison_hom_app]
  exact pullbackSquareComparison_comp_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K)
    (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K) w.w.symm hi K

/-- The relative Frobenius part of `θ_f` at a fibre (blueprint
`lemma-comparison-via-relative-frobenius--4`, proof of (2)): under the base change to the fibre `Z`
of `y`, `Rf'_!(η_r)` followed by the composition isomorphisms becomes the pullback `Φ_Z^♯`. -/
lemma baseChange_comp_relativeFrobenius_stalk {p : X' ⟶ X} {f' : X' ⟶ Y}
    {r : X ⟶ X'} {ΦZ : Z ⟶ Z} {j : Z ⟶ X'} {y : RationalPoint Y} [IsProper r.left]
    [IsProper ΦZ.left] (hZ : IsPullback (j ≫ p) (toPoint Z) (r ≫ f') y)
    (hL : IsPullback j (toPoint Z) f' y) (hT : IsPullback (j ≫ p) ΦZ r j)
    (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            r).unit.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
              K))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((boundedConstructibleLowerShriek ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K)))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((boundedConstructibleLowerShriek ℓ (r ≫ f')).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K)) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K) =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hL).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ j p).inv.app K) ≫
      (compactPullback ℓ ΦZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K) := by
  have hn₁ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).naturality
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K)
  have hV := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert ℓ hT hL
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K))
  have cV := boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app ℓ hZ
    (hT.paste_vert hL) rfl (comp_toPoint ΦZ).symm rfl rfl
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K))
  have hn₂ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hL).naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      r).unit.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app _)
  have hU := map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ hT
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K)
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc] at hU
  have hU' := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint Z)).map hU
  have hn₃ := (boundedConstructibleLowerShriekCompToPoint ℓ ΦZ).hom.naturality
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      hT.toCommSq).hom.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        p).obj K))
  have hn₄ := (compactPullback ℓ ΦZ).naturality
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ j p).inv.app K)
  have hPB := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
    (pullbackSquareComparison_hom_app_comp_map_upperStarComp_inv_app ℓ hT.toCommSq hi K)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hn₁ hn₂ hn₃ hn₄ hU' hPB hV
  simp only [hn₁]
  erw [cV]
  simp only [hV]
  have hC := boundedConstructibleLowerShriekCompToPoint_hom_app ℓ ΦZ
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K)))
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y)
      ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K)))]
  simp only [Iso.inv_hom_id_app (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f')
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K)),
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hn₂, reassoc_of% hU',
    ← reassoc_of% hC, reassoc_of% hn₃]
  simp only [← reassoc_of% (compactPullback_app ℓ ΦZ
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj K))), hPB,
    ← reassoc_of% hn₄]

end AlgebraicGeometry.ProEtale.CondensedRing
