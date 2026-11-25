/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.TraceFormula.LocalTerm
public import WeilConjectures.TraceFormula.Specialization.OpenImmersionLowerShriekComp

/-!
# Purity of open immersions and composition

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. For an open immersion
`j` of separated `k`-schemes of finite type, `Rj^! ℚ̄_ℓ ≅ j^* ℚ̄_ℓ ≅ ℚ̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`). This file proves:

* `ProEtale.CondensedRing.boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_comp_hom_app`:
  the identifications `Rj^! ≅ j^*` are compatible with the composition isomorphisms of `R(-)^!`
  and of `(-)^*`, by conjugation of the corresponding statement for `Rj_! ≅ j_!`
  (`boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`);
* `ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl_comp`: hence so are
  the identifications `Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ`;
* for a morphism `f : X ⟶ Y` and an open immersion `j : Y ⟶ Z`, the comparison
  `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitCompIso_padicAlgCl`) satisfies the
  cocycle condition for composites of open immersions
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The identifications `Rj^! ≅ j^*` of open immersions are compatible with composition:
`R(a ≫ b)^! ≅ Rb^! ⋙ Ra^! ≅ b^* ⋙ a^*` is `R(a ≫ b)^! ≅ (a ≫ b)^* ≅ b^* ⋙ a^*`. It is the
conjugate of the compatibility of the identifications `Rj_! ≅ j_!` with composition. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_comp_hom (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] [IsOpenImmersion (a ≫ b).left] :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ a b).hom ≫
        Functor.whiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ b).hom
          (boundedConstructibleUpperShriek ℓ a) ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b)
          (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ a).hom =
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (a ≫ b)).hom ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b).hom := by
  have hL : Functor.whiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ a).inv
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ b) ≫
      Functor.whiskerLeft (boundedConstructibleLowerShriek ℓ a)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ b).inv ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).inv =
      (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ a
        b).inv ≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (a ≫ b)).inv := by
    refine NatTrans.ext (funext fun K ↦ ?_)
    have h := congrArg Iso.inv (Iso.ext
      (α := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).app K ≪≫
        (boundedConstructibleLowerShriek ℓ b).mapIso
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ a).app K) ≪≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ b).app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ a).obj
            K))
      (β := (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (a ≫ b)).app
          K ≪≫
        (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ a
          b).app K)
      (boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion ℓ a b K))
    have n :=
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ b).inv.naturality
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ a).inv.app K)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj] at n ⊢
    rw [reassoc_of% n]
    simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using h
  let Aa := boundedConstructibleUpperShriekAdjunction ℓ a
  let Ab := boundedConstructibleUpperShriekAdjunction ℓ b
  let Aab := boundedConstructibleUpperShriekAdjunction ℓ (a ≫ b)
  let Oa := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ a
  let Ob := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ b
  let Oab := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) ℓ (a ≫ b)
  have e₁ : (boundedConstructibleUpperShriekComp_padicAlgCl ℓ a b).hom =
      conjugateEquiv Aab (Aa.comp Ab) (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).inv :=
    rfl
  have e₂ : Functor.whiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ b).hom
      (boundedConstructibleUpperShriek ℓ a) =
      conjugateEquiv (Aa.comp Ab) (Aa.comp Ob) (Functor.whiskerLeft
        (boundedConstructibleLowerShriek ℓ a)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ b).inv) :=
    (conjugateEquiv_whiskerLeft Ab Ob Aa _).symm
  have e₃ : Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b)
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ a).hom =
      conjugateEquiv (Aa.comp Ob) (Oa.comp Ob) (Functor.whiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ a).inv
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ b)) :=
    (conjugateEquiv_whiskerRight Aa Oa Ob _).symm
  have e₄ : (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (a ≫ b)).hom =
      conjugateEquiv Aab Oab
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (a ≫ b)).inv :=
    rfl
  have e₅ : (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b).hom =
      conjugateEquiv Oab (Oa.comp Ob)
        (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ a
          b).inv := by
    rw [boundedConstructibleOpenImmersionLowerShriekComp, Iso.symm_inv,
      conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  rw [e₁, e₂, e₃, conjugateEquiv_comp, conjugateEquiv_comp]
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·) e₄.symm e₅.symm)
  rw [conjugateEquiv_comp]
  refine congrArg (conjugateEquiv Aab (Oa.comp Ob)) ?_
  exact (Category.assoc _ _ _).trans hL

/-- The identifications `Rj^! ℚ̄_ℓ ≅ ℚ̄_ℓ` of open immersions are compatible with composition:
`R(a ≫ b)^! ℚ̄_ℓ ≅ Ra^! Rb^! ℚ̄_ℓ ≅ Ra^! ℚ̄_ℓ ≅ ℚ̄_ℓ` is the identification for `a ≫ b`. -/
lemma boundedConstructibleUpperShriekUnitIso_padicAlgCl_comp (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] [IsOpenImmersion (a ≫ b).left] :
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ a b).hom.app _ ≫
        (boundedConstructibleUpperShriek ℓ a).map
          (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ b).hom ≫
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ a).hom =
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ (a ≫ b)).hom := by
  have h := congr_app (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_comp_hom ℓ a b)
    (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  have n := (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ a).hom.naturality
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b)).inv
  simp only [boundedConstructibleUpperShriekUnitIso_padicAlgCl, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n, reassoc_of% h, boundedConstructibleUpperStarComp_hom_app_unit]

/-- The comparison `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! Rj^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ` for an open immersion `j`: the
composition isomorphism of the exceptional inverse images followed by `Rf^!` of purity for `j`
(`boundedConstructibleUpperShriekUnitIso_padicAlgCl`). -/
noncomputable def boundedConstructibleUpperShriekUnitCompIso_padicAlgCl (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j.left] :
    (boundedConstructibleUpperShriek ℓ (f ≫ j)).obj
        (𝟙_ (Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f j).app _ ≪≫
    (boundedConstructibleUpperShriek ℓ f).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)

/-- **Cocycle condition** for the comparisons `R(f ≫ j)^! ℚ̄_ℓ ≅ Rf^! ℚ̄_ℓ`: for open immersions
`ι` and `j`, the comparison for `ι ≫ j` is the composite of those for `j` and for `ι`, through
`f ≫ (ι ≫ j) = (f ≫ ι) ≫ j`. -/
lemma boundedConstructibleUpperShriekUnitCompIso_padicAlgCl_comp {W : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] (f : X ⟶ Y)
    (ι : Y ⟶ Z) (j : Z ⟶ W) [IsOpenImmersion ι.left] [IsOpenImmersion j.left]
    [IsOpenImmersion (ι ≫ j).left] :
    (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ f (ι ≫ j)).hom =
      eqToHom (congrArg (fun m ↦ (boundedConstructibleUpperShriek ℓ m).obj
        (𝟙_ (Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) (Category.assoc f ι j).symm) ≫
        (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ (f ≫ ι) j).hom ≫
        (boundedConstructibleUpperShriekUnitCompIso_padicAlgCl ℓ f ι).hom := by
  have hA := boundedConstructibleUpperShriekComp_padicAlgCl_assoc ℓ f ι j
    (𝟙_ (Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
  have n := (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f ι).hom.naturality
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).hom
  simp only [Functor.comp_map] at n
  simp only [boundedConstructibleUpperShriekUnitCompIso_padicAlgCl, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% n, reassoc_of% hA, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Functor.map_comp, ← Functor.map_comp, boundedConstructibleUpperShriekUnitIso_padicAlgCl_comp]

end AlgebraicGeometry.ProEtale.CondensedRing
