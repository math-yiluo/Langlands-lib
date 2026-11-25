/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceProof

/-!
# The comparison of the two models commutes with pullbacks, coherently

Let `E_X : AdicSheaf ℓ X ≌ Mod_{ℚ̲̄_ℓ,X}` be the equivalence of the two models of `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`). Its compatibility with the pushforward
along `f : Y ⟶ X` (`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`, with identity
underlying morphisms) gives, by uniqueness of left adjoints, an isomorphism
`f^* ⋙ E_Y⁻¹ ≅ E_X⁻¹ ⋙ f^*` between the pullbacks of the two models
(`AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso`). This file shows that these
isomorphisms are compatible with the composition isomorphisms of the pullbacks of both models
(`AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso_comp`): they form a pseudonatural
transformation.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Equivalence

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- `conjugateEquiv_whiskerLeft` for the adjunction `E⁻¹ ⊣ E` of an equivalence, stated with the
functor `E.inverse`. -/
lemma conjugateEquiv_symm_toAdjunction_comp_whiskerLeft (E : A ≌ B) {L₁ L₂ : A ⥤ C}
    {R₁ R₂ : C ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ⟶ L₁) :
    conjugateEquiv (E.symm.toAdjunction.comp adj₁) (E.symm.toAdjunction.comp adj₂)
      (Functor.whiskerLeft E.inverse τ) =
      Functor.whiskerRight (conjugateEquiv adj₁ adj₂ τ) E.functor :=
  conjugateEquiv_whiskerLeft adj₁ adj₂ E.symm.toAdjunction τ

/-- `conjugateEquiv_whiskerRight` for the adjunction `E⁻¹ ⊣ E` of an equivalence, stated with
the functor `E.inverse`. -/
lemma conjugateEquiv_comp_symm_toAdjunction_whiskerRight (E : B ≌ C) {L₁ L₂ : A ⥤ C}
    {R₁ R₂ : C ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₂ ⟶ L₁) :
    conjugateEquiv (adj₁.comp E.symm.toAdjunction) (adj₂.comp E.symm.toAdjunction)
      (Functor.whiskerRight τ E.inverse) =
      Functor.whiskerLeft E.functor (conjugateEquiv adj₁ adj₂ τ) :=
  conjugateEquiv_whiskerRight adj₁ adj₂ E.symm.toAdjunction τ

/-- `conjugateEquiv_associator_hom` with the adjunction `E⁻¹ ⊣ E` of an equivalence first. -/
lemma conjugateEquiv_associator_hom_symm_toAdjunction_left (E : B ≌ A) {L₁ : B ⥤ C}
    {R₁ : C ⥤ B} {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) :
    conjugateEquiv (E.symm.toAdjunction.comp (adj₁.comp adj₂))
      ((E.symm.toAdjunction.comp adj₁).comp adj₂) (Functor.associator E.inverse L₁ L₂).hom =
      (Functor.associator R₂ R₁ E.functor).hom :=
  conjugateEquiv_associator_hom E.symm.toAdjunction adj₁ adj₂

/-- `conjugateEquiv_associator_hom` with the adjunction `E⁻¹ ⊣ E` of an equivalence last. -/
lemma conjugateEquiv_associator_hom_symm_toAdjunction_right (E : D ≌ C) {L₁ : A ⥤ B}
    {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) :
    conjugateEquiv (adj₁.comp (adj₂.comp E.symm.toAdjunction))
      ((adj₁.comp adj₂).comp E.symm.toAdjunction) (Functor.associator L₁ L₂ E.inverse).hom =
      (Functor.associator E.functor R₂ R₁).hom :=
  conjugateEquiv_associator_hom adj₁ adj₂ E.symm.toAdjunction

/-- `conjugateEquiv_associator_inv` with the adjunction `E⁻¹ ⊣ E` of an equivalence in the
middle. -/
lemma conjugateEquiv_associator_inv_symm_toAdjunction_middle (E : C ≌ B) {L₁ : A ⥤ B}
    {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) :
    conjugateEquiv ((adj₁.comp E.symm.toAdjunction).comp adj₂)
      (adj₁.comp (E.symm.toAdjunction.comp adj₂)) (Functor.associator L₁ E.inverse L₂).inv =
      (Functor.associator R₂ E.functor R₁).inv :=
  Adjunction.conjugateEquiv_associator_inv adj₁ E.symm.toAdjunction adj₂

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The compatibility of the inverses of the comparisons `E` with the pullbacks:
`f^* ⋙ E_Y⁻¹ ≅ E_X⁻¹ ⋙ f^*`, conjugate to the compatibility
`f_* ⋙ E_X ≅ E_Y ⋙ f_*` of the comparisons with the pushforwards
(`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`). -/
noncomputable def upperStarCondensedModInverseIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ⋙
        (adicSheafEquivCondensedMod l Y).inverse ≅
      (adicSheafEquivCondensedMod l X).inverse ⋙ (f)^*ᵃ[l] :=
  (conjugateIsoEquiv ((adicSheafEquivCondensedMod l X).symm.toAdjunction.comp
      (adicUpperStarLowerStarAdjunction l f))
    ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).comp
      (adicSheafEquivCondensedMod l Y).symm.toAdjunction)).symm
    (adicLowerStarCompCondensedModIso l f)

/-- `AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso` is conjugate to the
compatibility of the comparisons with the pushforwards. -/
lemma conjugateEquiv_upperStarCondensedModInverseIso_hom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    conjugateEquiv ((adicSheafEquivCondensedMod l X).symm.toAdjunction.comp
        (adicUpperStarLowerStarAdjunction l f))
      ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).comp
        (adicSheafEquivCondensedMod l Y).symm.toAdjunction)
      (upperStarCondensedModInverseIso l f).hom = (adicLowerStarCompCondensedModIso l f).hom :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply _)

/-- The compatibility of the comparisons with the pushforwards is compatible with the composition
isomorphisms of the pushforwards of both models. -/
lemma adicLowerStarCompCondensedModIso_comp {T S X : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ X) :
    Functor.whiskerRight (adicLowerStarComp l a b).hom _ ≫
        (adicLowerStarCompCondensedModIso l (a ≫ b)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (adicLowerStarCompCondensedModIso l b).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (adicLowerStarCompCondensedModIso l a).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _
          (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) a b).hom := by
  ext M : 2
  refine Mod.hom_ext _ _ ?_
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Mod.comp_hom', Category.id_comp,
    adicLowerStarCompCondensedModIso_hom_app_hom]
  rfl

set_option hygiene false in
local notation "aN" => CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
set_option hygiene false in
local notation "aA" => adicUpperStarLowerStarAdjunction l
set_option hygiene false in
local notation "eS" Z => (adicSheafEquivCondensedMod l Z).symm.toAdjunction

/-- **The comparisons of the pullbacks of the two models are pseudonatural**: for `a : T ⟶ S`
and `b : S ⟶ X`, the comparison `(a ≫ b)^* ⋙ E⁻¹ ≅ E⁻¹ ⋙ (a ≫ b)^*` followed by the composition
isomorphism of the old pullbacks is the composition isomorphism of the new pullbacks followed by
the comparisons for `a` and `b`. -/
lemma upperStarCondensedModInverseIso_comp {T S X : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ X) :
    (upperStarCondensedModInverseIso l (a ≫ b)).hom ≫
        Functor.whiskerLeft _ (adicUpperStarComp l a b).hom =
      Functor.whiskerRight (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) a b).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (upperStarCondensedModInverseIso l a).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (upperStarCondensedModInverseIso l b).hom _ ≫
        (Functor.associator _ _ _).hom := by
  apply (conjugateEquiv ((eS X).comp ((aA b).comp (aA a))) ((aN (a ≫ b)).comp (eS T))).injective
  rw [← conjugateEquiv_comp _ ((eS X).comp (aA (a ≫ b))),
    ← conjugateEquiv_comp _ (((aN b).comp (aN a)).comp (eS T)),
    ← conjugateEquiv_comp _ ((aN b).comp ((aN a).comp (eS T))),
    ← conjugateEquiv_comp _ ((aN b).comp ((eS S).comp (aA a))),
    ← conjugateEquiv_comp _ (((aN b).comp (eS S)).comp (aA a)),
    ← conjugateEquiv_comp _ (((eS X).comp (aA b)).comp (aA a))]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_upperStarCondensedModInverseIso_hom]
  rw [Equivalence.conjugateEquiv_symm_toAdjunction_comp_whiskerLeft,
    conjugateEquiv_adicUpperStarComp_hom,
    Equivalence.conjugateEquiv_comp_symm_toAdjunction_whiskerRight,
    CondensedRing.conjugateEquiv_upperStarComp_hom_eq_lowerStarComp,
    Equivalence.conjugateEquiv_associator_hom_symm_toAdjunction_left,
    Equivalence.conjugateEquiv_associator_hom_symm_toAdjunction_right,
    Equivalence.conjugateEquiv_associator_inv_symm_toAdjunction_middle]
  simp only [Category.assoc]
  exact adicLowerStarCompCondensedModIso_comp l a b

/-- `AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso_comp`, at an object. -/
@[reassoc]
lemma upperStarCondensedModInverseIso_comp_hom_app {T S X : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ X)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :
    (upperStarCondensedModInverseIso l (a ≫ b)).hom.app M ≫
        (adicUpperStarComp l a b).hom.app ((adicSheafEquivCondensedMod l X).inverse.obj M) =
      (adicSheafEquivCondensedMod l T).inverse.map
          ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) a b).hom.app M) ≫
        (upperStarCondensedModInverseIso l a).hom.app
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M) ≫
        (a)^*ᵃ[l].map ((upperStarCondensedModInverseIso l b).hom.app M) := by
  have h := NatTrans.congr_app (upperStarCondensedModInverseIso_comp l a b) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- The comparisons of the pullbacks along equal morphisms agree, up to the transport along the
equality. -/
lemma upperStarCondensedModInverseIso_hom_app_eqToHom {S X : Scheme.{u}} {f f' : S ⟶ X}
    (h : f = f')
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :
    (adicSheafEquivCondensedMod l S).inverse.map (eqToHom (by rw [h])) ≫
        (upperStarCondensedModInverseIso l f').hom.app M =
      (upperStarCondensedModInverseIso l f).hom.app M ≫ eqToHom (by rw [h]) := by
  subst h
  simp

end AlgebraicGeometry.ProEtale
