/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# The counit of `j^* ⊣ j_*` and structure maps along automorphisms

Let `j : U ⟶ X` be a morphism of schemes and `e_U`, `e_X` automorphisms of `U` and `X` with
`j ≫ e_X = e_U ≫ j`. A structure map `ψ : (e_U⁻¹)_* M ⟶ M` of a sheaf `M` on `U` induces a
structure map `(e_X⁻¹)_* j_* M ≅ j_* (e_U⁻¹)_* M ⟶ j_* M` of `j_* M`, and the counit
`j^* j_* M ⟶ M` intertwines the two
(`AlgebraicGeometry.ProEtale.upperStarComp_hom_app_comp_map_counit_comp_structure'`). This is the
form in which the counit is compatible with Weil structures.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The counit of `j^* ⊣ j_*` is compatible with structure maps `ψ : (e_U⁻¹)_* M ⟶ M` and the
induced structure map on `j_* M`. -/
lemma upperStarComp_hom_app_comp_map_counit_comp_structure {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (Scheme.ProEt.topology U) A)
    (ψ : (eU.inv)_*[A].obj M ⟶ M) :
    (upperStarComp A eU.hom j).hom.app ((j)_*[A].obj M) ≫
        (eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
        (upperStarIsoLowerStarInv A eU).hom.app M ≫ ψ =
      (upperStarFactor A e).hom.app ((j)_*[A].obj M) ≫
        (j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
          (lowerStarFactor A e').hom.app M ≫
          (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M ≫ (j)_*[A].map ψ) ≫
        (upperStarLowerStarAdjunction A j).counit.app M := by
  rw [reassoc_of% upperStarComp_hom_app_comp_map_counit_comp_upperStarIsoLowerStarInv A j eU eX
    e e' M]
  have n := (upperStarLowerStarAdjunction A j).counit_naturality ψ
  simp only [Functor.map_comp, Category.assoc, ← n]

/-- The factorisation isomorphism of pullbacks, evaluated at a sheaf, is the congruence
isomorphism followed by the composition isomorphism. -/
lemma upperStarFactor_hom_app_eq {P Y Z : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z} {c : Z ⟶ Y}
    (e : b ≫ c = a) (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app M =
      (upperStarCongr A e.symm).hom.app M ≫ (upperStarComp A b c).hom.app M := by
  rw [upperStarFactor, Iso.trans_hom, NatTrans.comp_app]

/-- The counit of `j^* ⊣ j_*` is compatible with structure maps `ψ : (e_U⁻¹)_* M ⟶ M` and the
induced structure map on `j_* M`, in terms of composition and congruence isomorphisms. -/
lemma upperStarComp_hom_app_comp_map_counit_comp_structure' {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (Scheme.ProEt.topology U) A)
    (ψ : (eU.inv)_*[A].obj M ⟶ M) :
    (upperStarComp A eU.hom j).hom.app ((j)_*[A].obj M) ≫
        (eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
        (upperStarIsoLowerStarInv A eU).hom.app M ≫ ψ =
      (upperStarCongr A e.symm).hom.app ((j)_*[A].obj M) ≫
        (upperStarComp A j eX.hom).hom.app ((j)_*[A].obj M) ≫
        (j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
          (lowerStarComp A j eX.inv).hom.app M ≫ (lowerStarCongr A e').hom.app M ≫
          (lowerStarComp A eU.inv j).inv.app M ≫ (j)_*[A].map ψ) ≫
        (upperStarLowerStarAdjunction A j).counit.app M := by
  rw [upperStarComp_hom_app_comp_map_counit_comp_structure A j eU eX e e' M ψ,
    upperStarFactor_hom_app_eq, ← lowerStarComp_trans_lowerStarCongr,
    ← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl, Iso.trans_refl, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc, Category.assoc]

/-- The counit of `j^* ⊣ j_*` is compatible with structure maps `ψ : (e_U⁻¹)_* M ⟶ M` and the
induced structure map on `j_* M`, in the form of a morphism of algebras over `(e_U⁻¹)_*`. -/
lemma lowerStar_map_counit_comp_structure {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (Scheme.ProEt.topology U) A)
    (ψ : (eU.inv)_*[A].obj M ⟶ M) :
    (eU.inv)_*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫ ψ =
      (upperStarIsoLowerStarInv A eU).inv.app ((j)^*[A].obj ((j)_*[A].obj M)) ≫
        (upperStarComp A eU.hom j).inv.app ((j)_*[A].obj M) ≫
        (upperStarCongr A e.symm).hom.app ((j)_*[A].obj M) ≫
        (upperStarComp A j eX.hom).hom.app ((j)_*[A].obj M) ≫
        (j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M)) ≫
        (j)^*[A].map ((lowerStarComp A j eX.inv).hom.app M) ≫
        (j)^*[A].map ((lowerStarCongr A e').hom.app M) ≫
        (j)^*[A].map ((lowerStarComp A eU.inv j).inv.app M) ≫
        (j)^*[A].map ((j)_*[A].map ψ) ≫
        (upperStarLowerStarAdjunction A j).counit.app M := by
  have S := upperStarComp_hom_app_comp_map_counit_comp_structure' A j eU eX e e' M ψ
  have n := (upperStarIsoLowerStarInv A eU).hom.naturality
    ((upperStarLowerStarAdjunction A j).counit.app M)
  rw [reassoc_of% n] at S
  simp only [Functor.map_comp, Category.assoc] at S
  rw [← S, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale
