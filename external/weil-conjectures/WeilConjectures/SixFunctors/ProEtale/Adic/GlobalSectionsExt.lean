/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSectionsComm

/-!
# Global sections of sheaves of `ℚ̄_ℓ`-modules as morphisms out of `ℤ`

For a pro-étale sheaf `M` of `ℚ̄_ℓ`-modules on `X`, morphisms `ℤ_X ⟶ M` of abelian sheaves are
the global sections `Γ(X, M)` (`AlgebraicGeometry.ProEtale.constantIntHomAddEquivΓ`), naturally
in `M`. This identifies the complex `Hom(ℤ_X, J)` computing `Ext(ℤ_X, -)` from an injective
resolution `J` with the complex of global sections `Γ(X, J)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- Morphisms `ℤ_X ⟶ M` of abelian sheaves, for a sheaf `M` of `ℚ̄_ℓ`-modules, are the global
sections `Γ(X, M)`. -/
noncomputable def constantIntHomAddEquivΓ
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M) ≃+
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj M :=
  ((constantSheafAdj _ AddCommGrpCat.{u + 1} (Scheme.ProEt.isTerminalMkId X)).homAddEquiv _ _).trans
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).trans
      ((Sheaf.ΓNatIsoSheafSections _ _
        (Scheme.ProEt.isTerminalMkId X)).app M).symm.toLinearEquiv.toAddEquiv)

lemma constantIntHomAddEquivΓ_apply
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (f : (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M) :
    constantIntHomAddEquivΓ X M f =
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).inv.app M
        (AddCommGrpCat.uliftZMultiplesAddEquiv _
          ((constantSheafAdj _ AddCommGrpCat.{u + 1} (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _
            f)) :=
  rfl

omit [Fact l.Prime] in
/-- `AddCommGrpCat.uliftZMultiplesAddEquiv` is natural. -/
lemma _root_.AddCommGrpCat.uliftZMultiplesAddEquiv_comp {G H : AddCommGrpCat.{u + 1}}
    (g : AddCommGrpCat.of (ULift ℤ) ⟶ G) (k : G ⟶ H) :
    AddCommGrpCat.uliftZMultiplesAddEquiv H (g ≫ k) =
      k (AddCommGrpCat.uliftZMultiplesAddEquiv G g) :=
  rfl

variable {X} in
lemma constantIntHomAddEquivΓ_comp {M N : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (f : (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M)
    (φ : M ⟶ N) :
    constantIntHomAddEquivΓ X N (f ≫ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).map φ) =
      (Sheaf.Γ _ _).map φ (constantIntHomAddEquivΓ X M f) := by
  have h := ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
    (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).inv.naturality φ)
  rw [constantIntHomAddEquivΓ_apply, constantIntHomAddEquivΓ_apply,
    Adjunction.homEquiv_naturality_right, AddCommGrpCat.uliftZMultiplesAddEquiv_comp]
  simp only [ConcreteCategory.comp_apply] at h
  exact h _

section Sections

variable {X}

/-- The constant abelian sheaf `ℤ_X` on the pro-étale site. -/
noncomputable abbrev constantIntSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- Morphisms `ℤ_X ⟶ N` of abelian sheaves are the sections of `N` over the terminal object. -/
noncomputable def constantIntSheafHomAddEquiv
    (N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (constantIntSheaf X ⟶ N) ≃+ N.obj.obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  ((constantSheafAdj _ AddCommGrpCat.{u + 1} (Scheme.ProEt.isTerminalMkId X)).homAddEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

lemma constantIntSheafHomAddEquiv_comp
    {N N' : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    (f : constantIntSheaf X ⟶ N) (φ : N ⟶ N') :
    constantIntSheafHomAddEquiv _ (f ≫ φ) =
      φ.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (constantIntSheafHomAddEquiv _ f) := by
  simp only [constantIntSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

variable {X' : Scheme.{u}} (g : X ⟶ X')

/-- The map `ℤ_{X'} ⟶ g_* ℤ_X` whose global section is the restriction of `1` along
`X ×_{X'} X' ≅ X`. -/
noncomputable def constantIntSheafToLowerStar :
    constantIntSheaf X' ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj (constantIntSheaf X) :=
  (constantIntSheafHomAddEquiv _).symm
    ((constantIntSheaf X).obj.map (overPullbackObjMkIdIso g).hom.op
    (constantIntSheafHomAddEquiv _ (𝟙 _)))

/-- Composing with `ℤ_{X'} ⟶ g_* ℤ_X` and pushing forward restricts the global section along
`X ×_{X'} X' ≅ X`. -/
lemma constantIntSheafHomAddEquiv_constantIntSheafToLowerStar_comp
    {N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} (f : constantIntSheaf X ⟶ N) :
    constantIntSheafHomAddEquiv _
        (constantIntSheafToLowerStar g ≫ (g)_*[AddCommGrpCat.{u + 1}].map f) =
      N.obj.map (overPullbackObjMkIdIso g).hom.op (constantIntSheafHomAddEquiv _ f) := by
  rw [constantIntSheafHomAddEquiv_comp, constantIntSheafToLowerStar, AddEquiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom (f.hom.naturality (overPullbackObjMkIdIso g).hom.op)
    (constantIntSheafHomAddEquiv _ (𝟙 _))
  simp only [ConcreteCategory.comp_apply] at h
  rw [← Category.id_comp f, constantIntSheafHomAddEquiv_comp, Category.id_comp]
  exact h


/-- Composing with `ℤ_{X'} ⟶ g_* ℤ_X` and pushing forward corresponds, on global sections of a
sheaf of `ℚ̄_ℓ`-modules, to the identification `Γ(X, M) ≅ Γ(X', g_* M)`. -/
lemma constantIntHomAddEquivΓ_constantIntSheafToLowerStar_comp
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (f : constantIntSheaf X ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M) :
    constantIntHomAddEquivΓ X' ((g)_*[WeilCoefficients.{u} l].obj M)
        (constantIntSheafToLowerStar g ≫ (g)_*[AddCommGrpCat.{u + 1}].map f) =
      (globalSectionsLowerStarIso _ g).inv.app M (constantIntHomAddEquivΓ X M f) := by
  rw [constantIntHomAddEquivΓ_apply, constantIntHomAddEquivΓ_apply,
    globalSectionsLowerStarIso_inv_app_eq_sections]
  have h := constantIntSheafHomAddEquiv_constantIntSheafToLowerStar_comp g f
  simp only [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_app_apply]
  exact congrArg _ h

end Sections

end AlgebraicGeometry.ProEtale
