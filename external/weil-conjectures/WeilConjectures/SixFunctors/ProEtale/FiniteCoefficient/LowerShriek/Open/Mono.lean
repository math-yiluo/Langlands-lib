/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!
# The comparison `j_! ⟶ j_*` is a monomorphism

For an open immersion `j : U ⟶ X` and a pro-étale sheaf `F` on `U`, the comparison
`j_! F ⟶ j_* F` (`AlgebraicGeometry.ProEtale.openImmersionLowerShriekToLowerStar`) is a
monomorphism (`AlgebraicGeometry.ProEtale.mono_openImmersionLowerShriekToLowerStar_app`).

## The argument

The extension by zero is the sheafification of the presheaf left Kan extension `L.op.lan` along
the localization functor `L : U.ProEt ⥤ X.ProEt`. A morphism of presheaves `ψ : L.op.lan P ⟶ Q`
whose transpose `P ⟶ L^* Q` is a monomorphism is a monomorphism: at a weakly étale `V ⟶ X` the
value of `L.op.lan P` is initial if `V` does not factor through `U`, and otherwise it is the
value of `P` at the terminal object `V'` of the comma category, with `L V' ≅ V`, where `ψ` is the
transpose followed by an isomorphism. Sheafification preserves monomorphisms, and the transpose
of the comparison `j_! F ⟶ j_* F` is the inverse of the counit of `j^* ⊣ j_*`.

As a consequence, a subsheaf of `j_! F` whose restriction to `U` vanishes is zero
(`AlgebraicGeometry.ProEtale.isZero_of_mono_openImmersionLowerShriek`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

variable {A j} in
/-- A morphism of presheaves `ψ : L.op.lan P ⟶ Q` out of the presheaf extension by zero along an
open immersion is a monomorphism as soon as its transpose `P ⟶ L^* Q` is. -/
lemma mono_of_mono_lanUnit_app_comp_whiskerLeft {P : U.ProEtᵒᵖ ⥤ A} {Q : X.ProEtᵒᵖ ⥤ A}
    (ψ : (openImmersionLocalization j).op.lan.obj P ⟶ Q)
    (hψ : Mono ((openImmersionLocalization j).op.lanUnit.app P ≫
      Functor.whiskerLeft (openImmersionLocalization j).op ψ)) :
    Mono ψ := by
  have (V : X.ProEtᵒᵖ) : Mono (ψ.app V) := by
    by_cases h : Nonempty (CostructuredArrow (openImmersionLocalization j).op V)
    · obtain ⟨s⟩ := h
      obtain ⟨t, ht⟩ := exists_isIso_costructuredArrow_hom j V s
      obtain ⟨hT⟩ := nonempty_isTerminal_costructuredArrow_of_isIso j V t
      have h₂ := ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        P V).isIso_ι_app_of_isTerminal t hT
      dsimp at h₂
      have key : (((openImmersionLocalization j).op.lanUnit.app P).app t.left ≫
          ((openImmersionLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V =
          ((openImmersionLocalization j).op.lanUnit.app P ≫
            Functor.whiskerLeft (openImmersionLocalization j).op ψ).app t.left ≫
            Q.map t.hom := by
        rw [Category.assoc, ψ.naturality]
        simp
      have hm : Mono ((((openImmersionLocalization j).op.lanUnit.app P).app t.left ≫
          ((openImmersionLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V) := by
        rw [key]
        infer_instance
      rw [← IsIso.inv_hom_id_assoc (((openImmersionLocalization j).op.lanUnit.app P).app t.left ≫
        ((openImmersionLocalization j).op.lan.obj P).map t.hom) (ψ.app V)]
      infer_instance
    · have : IsEmpty (CostructuredArrow (openImmersionLocalization j).op V) :=
        not_nonempty_iff.mp h
      have hP := (isColimitEquivIsInitialOfIsEmpty A _).1
        ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P V)
      exact (hP.isZero).mono _
  exact NatTrans.mono_of_mono_app ψ

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unit of `j_! ⊣ j^*` on underlying presheaves: the unit of the presheaf left Kan extension
followed by the sheafification map. -/
lemma sheafToPresheaf_map_openImmersionLowerShriekAdjunction_unit_app
    (F : Sheaf (Scheme.ProEt.topology U) A) :
    (sheafToPresheaf _ A).map ((openImmersionLowerShriekAdjunction A j).unit.app F) =
      (openImmersionLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openImmersionLocalization j).op
          (toSheafify _ ((openImmersionLocalization j).op.lan.obj F.obj)) := by
  dsimp only [openImmersionLowerShriekAdjunction, localizationLowerShriekAdjunction,
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  erw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.lanAdjunction_unit]

/-- A morphism of sheaves `φ : j_! F ⟶ N` out of an extension by zero along an open immersion
is a monomorphism as soon as its transpose `F ⟶ j^* N` is: on presheaves, the transpose of
`φ` under the sheafification adjunction is a monomorphism by
`AlgebraicGeometry.ProEtale.mono_of_mono_lanUnit_app_comp_whiskerLeft`, and sheafification
preserves monomorphisms. -/
lemma mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp
    {F : Sheaf (Scheme.ProEt.topology U) A} {N : Sheaf (Scheme.ProEt.topology X) A}
    (φ : (j)_!open[A].obj F ⟶ N)
    (hφ : Mono ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
      (openImmersionRestriction A j).map φ)) :
    Mono φ := by
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) A
  let ψ := adj.homEquiv _ _ φ
  have hψ : Mono ψ := by
    refine mono_of_mono_lanUnit_app_comp_whiskerLeft ψ ?_
    have e : (openImmersionLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openImmersionLocalization j).op ψ =
        (sheafToPresheaf _ A).map ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
          (openImmersionRestriction A j).map φ) := by
      rw [Functor.map_comp, sheafToPresheaf_map_openImmersionLowerShriekAdjunction_unit_app,
        Category.assoc]
      congr 1
    have h := (sheafToPresheaf _ A).map_mono ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
      (openImmersionRestriction A j).map φ)
    rw [← e] at h
    exact h
  have : φ = (presheafToSheaf _ A).map ψ ≫ adj.counit.app N := by
    exact ((adj.homEquiv _ _).symm_apply_apply φ).symm.trans (adj.homEquiv_counit (g := ψ))
  rw [this]
  infer_instance

/-- **The comparison `j_! F ⟶ j_* F` is a monomorphism**: its transpose under `j_! ⊣ j^*` is
the inverse of the counit of `j^* ⊣ j_*`. -/
instance mono_openImmersionLowerShriekToLowerStar_app (F : Sheaf (Scheme.ProEt.topology U) A) :
    Mono ((openImmersionLowerShriekToLowerStar A j).app F) := by
  refine mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp A j _ ?_
  rw [openImmersionLowerShriekToLowerStar_app, Functor.map_comp, ← Category.assoc]
  erw [(openImmersionLowerShriekAdjunction A j).unit_naturality, Category.assoc,
    (openImmersionLowerShriekAdjunction A j).right_triangle_components, Category.comp_id]
  infer_instance

/-- A subsheaf of an extension by zero `j_! F` whose restriction to `U` vanishes is zero. -/
lemma isZero_of_mono_openImmersionLowerShriek {S : Sheaf (Scheme.ProEt.topology X) A}
    {F : Sheaf (Scheme.ProEt.topology U) A} (i : S ⟶ (j)_!open[A].obj F) [Mono i]
    (hS : IsZero ((openImmersionRestriction A j).obj S)) : IsZero S := by
  have hc : i ≫ (openImmersionLowerShriekToLowerStar A j).app F = 0 :=
    ((openImmersionRestrictionLowerStarAdjunction A j).homEquiv _ _).symm.injective
      (hS.eq_of_src _ _)
  exact IsZero.of_mono_eq_zero i ((cancel_mono ((openImmersionLowerShriekToLowerStar A j).app F)).1
    (by rw [hc, zero_comp]))

end AlgebraicGeometry.ProEtale
