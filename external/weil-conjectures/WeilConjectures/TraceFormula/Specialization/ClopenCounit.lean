/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalTerm

/-!

# The counit of an open and closed immersion

Let `j : B ⟶ F` be an open and closed immersion and `e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` the adjoint, for
`Rj_! ⊣ Rj^!`, of the purity isomorphism `ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekUnitIso_padicAlgCl`). On the summand `B`,
`e` is the inclusion of `Rj_! ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ` into `ℚ̄_ℓ`, and the unit `ℚ̄_ℓ ⟶ Rj_* Lj^* ℚ̄_ℓ` is
the projection onto it: `e` followed by the unit of `Lj^* ⊣ Rj_*` (read through
`Lj^* ℚ̄_ℓ ≅ ℚ̄_ℓ`) is `Rj_! ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ`
(`ProEtale.CondensedRing.homEquiv_symm_unitIso_inv_comp_unit`). The abstract form,
`CategoryTheory.Adjunction.homEquiv_symm_comp_conjugate_comp_unit`, holds for any transposed map
`M ⟶ j^* N ≅ j^! N`, given the comparison of `j_!° ≅ j_! ≅ j_*` with the canonical map
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {U : D ⥤ C} {L : C ⥤ D} (a : U ⊣ L)
  {O : C ⥤ D} (ao : O ⊣ U) {S : C ⥤ D} {R : D ⥤ C} (b : S ⊣ R)

/-- For an open and closed immersion (abstractly: `j_!° ⊣ j^* ⊣ j_*`, `j_! ⊣ j^!`,
`P : j_! ≅ j_!°`, `I : j_! ≅ j_*` with `j_!° ≅ j_*` canonical), the adjoint `j_! M ⟶ N` of
`M ⟶ j^* N ≅ j^! N`, followed by the unit `N ⟶ j_* j^* N`, is `I` followed by `j_*` of the
given map `M ⟶ j^* N`. -/
lemma homEquiv_symm_comp_conjugate_comp_unit [IsIso ao.unit] (P : S ≅ O) (I : S ≅ L)
    (hPI : ∀ M, ao.unit.app M ≫ U.map (P.inv.app M ≫ I.hom.app M) ≫ a.counit.app M = 𝟙 M)
    {M : C} {N : D} (g : M ⟶ U.obj N) :
    (b.homEquiv M N).symm (g ≫ (conjugateIsoEquiv b ao P.symm).inv.app N) ≫ a.unit.app N =
      I.hom.app M ≫ L.map g := by
  have hQ : (conjugateIsoEquiv b ao P.symm).inv.app N ≫
      (conjugateIsoEquiv ao b P).inv.app N = 𝟙 _ :=
    (conjugateIsoEquiv ao b P).hom_inv_id_app N
  -- the comparison on objects of the form `U N`
  have key : P.hom.app (U.obj N) ≫ ao.counit.app N ≫ a.unit.app N = I.hom.app (U.obj N) := by
    apply (a.homEquiv _ _).symm.injective
    simp only [homEquiv_counit, Functor.map_comp, Category.assoc, map_counit_eq_inv_unit ao]
    have h := hPI (U.obj N)
    rw [Functor.map_comp, Category.assoc] at h
    rw [← cancel_epi (ao.unit.app _ ≫ U.map (P.inv.app _)), Category.assoc, Category.assoc, h,
      ← U.map_comp_assoc, Iso.inv_hom_id_app, U.map_id, Category.id_comp,
      IsIso.hom_inv_id_assoc]
    exact a.left_triangle_components N
  rw [homEquiv_counit, counit_eq_conjugate ao b P, Functor.map_comp]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc ((conjugateIsoEquiv b ao P.symm).inv.app N), hQ, S.map_id,
    Category.id_comp, key]
  exact I.hom.naturality g

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {B F : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom]

/-- **The counit of an open and closed immersion is the inclusion of the summand**: for an open
and closed immersion `j`, the adjoint `e : Rj_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ`, followed by
`ℚ̄_ℓ ⟶ Rj_* Lj^* ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ`, is `Rj_! ℚ̄_ℓ ≅ Rj_* ℚ̄_ℓ`. -/
theorem homEquiv_symm_unitIso_inv_comp_unit (j : B ⟶ F) [IsOpenImmersion j.left]
    [IsProper j.left] :
    ((boundedConstructibleUpperShriekAdjunction ℓ j).homEquiv
        _ _).symm (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        j).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ j).map
        (Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).inv =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).hom.app (𝟙_ _) := by
  have h := Adjunction.homEquiv_symm_comp_conjugate_comp_unit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen ℓ j)
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)).hom
  rw [boundedConstructibleUpperShriekUnitIso_padicAlgCl, Iso.trans_inv, Iso.symm_inv,
    Iso.app_inv, boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl, reassoc_of% h,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.CondensedRing
