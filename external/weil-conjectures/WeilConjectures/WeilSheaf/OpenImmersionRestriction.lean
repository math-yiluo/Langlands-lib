/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Restricting extensions along an open immersion

Let `j : U ⟶ X` be a quasi-compact open immersion of `k₀`-schemes. The restriction `j^*` of the
direct image `j_*F` and of the extension by zero `j_!F` of a Weil sheaf `F` on `U` is `F` again.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_directImage_iso`: `j^* j_* F ≅ F`, the
  counit of the adjunction `j^* ⊣ j_*`.
- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_extensionByZero_iso`: `j^* j_! F ≅ F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The restriction of the direct image along an open immersion is the identity, as a functor
on Weil sheaves: `j_* ⋙ j^* ≅ 𝟭` after the inclusion into pro-étale Weil sheaves. It is the
counit of the adjunction `j^* ⊣ j_*` of pro-étale Weil sheaves, invertible along an open
immersion. The isomorphism is assembled from isomorphisms of functors, so that the kernel never
compares two different expressions for the same object. -/
noncomputable def directImageCompUpperStarCompιIso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (directImage j ⋙ upperStar j) ⋙ (WeilSheaf.objectProperty k₀ l U).ι ≅
      𝟭 _ ⋙ (WeilSheaf.objectProperty k₀ l U).ι :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l X) (WeilSheaf.objectProperty k₀ l U)
      (ProEtaleWeilSheaf.upperStar k₀ l j)
      fun _ hF ↦ ProEtale.IsAdicConstructibleSheaf.upperStar _ hF) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l U) (WeilSheaf.objectProperty k₀ l X)
      (ProEtaleWeilSheaf.lowerStar k₀ l j) (WeilSheaf.isAdicConstructibleSheaf_lowerStar j)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (asIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The restriction of the direct image along an open immersion is the sheaf itself:
`j^* j_* F ≅ F`, compatibly with the Weil structures. This is the counit of the adjunction
`j^* ⊣ j_*` of pro-étale Weil sheaves, invertible along an open immersion. -/
theorem nonempty_upperStar_directImage_iso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) :
    Nonempty ((upperStar j).obj ((directImage j).obj F) ≅ F) :=
  ⟨ObjectProperty.isoMk _ ((directImageCompUpperStarCompιIso j).app F)⟩

omit [QuasiCompact j] in
/-- The restriction of the comparison `j_! F ⟶ j_* F` of pro-étale Weil sheaves along an open
immersion `j` is invertible: on underlying sheaves it is the restriction of the comparison
`j̄_! ⟶ j̄_*`, whose transpose under `j̄_! ⊣ j̄^*` is the inverse of the counit of
`j̄^* ⊣ j̄_*`. -/
instance isIso_upperStar_map_extensionByZeroToLowerStar_app (F : ProEtaleWeilSheaf k₀ l U) :
    IsIso ((ProEtaleWeilSheaf.upperStar k₀ l j).map
      ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j).app F)) := by
  let J := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have : IsIso ((J)^*ᵃ[l].map ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l J).app
      F.carrier)) := by
    have : IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l J).unit.app F.carrier ≫
        (J)^*ᵃ[l].map ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l J).app F.carrier)) := by
      rw [ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.adicOpenImmersionLowerShriekAdjunction l J).unit.app F.carrier) _
  have : IsIso ((Endofunctor.IsoAlgebra.forget _).map ((ProEtaleWeilSheaf.upperStar k₀ l j).map
      ((ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j).app F))) := this
  exact isIso_of_reflects_iso _ (Endofunctor.IsoAlgebra.forget _)

omit [QuasiCompact j] in
instance isIso_whiskerRight_extensionByZeroToLowerStar_upperStar :
    IsIso (Functor.whiskerRight (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j)
      (ProEtaleWeilSheaf.upperStar k₀ l j)) :=
  (NatTrans.isIso_iff_isIso_app _).2 fun F ↦
    isIso_upperStar_map_extensionByZeroToLowerStar_app j F

/-- The restriction of the extension by zero along an open immersion is the identity, as a
functor on Weil sheaves: `j_! ⋙ j^* ≅ 𝟭` after the inclusion into pro-étale Weil sheaves. The
restriction of the comparison `j_! ⟶ j_*` is invertible, and so is the counit of `j^* ⊣ j_*`. -/
noncomputable def extensionByZeroCompUpperStarCompιIso :
    (extensionByZero j ⋙ upperStar j) ⋙ (WeilSheaf.objectProperty k₀ l U).ι ≅
      𝟭 _ ⋙ (WeilSheaf.objectProperty k₀ l U).ι :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l X) (WeilSheaf.objectProperty k₀ l U)
      (ProEtaleWeilSheaf.upperStar k₀ l j)
      fun _ hF ↦ ProEtale.IsAdicConstructibleSheaf.upperStar _ hF) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l U) (WeilSheaf.objectProperty k₀ l X)
      (ProEtaleWeilSheaf.extensionByZero k₀ l j) (isAdicConstructibleSheaf_extensionByZero j)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (asIso (Functor.whiskerRight (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l j)
        (ProEtaleWeilSheaf.upperStar k₀ l j)) ≪≫
        asIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The restriction of the extension by zero along an open immersion is the sheaf itself:
`j^* j_! F ≅ F`, compatibly with the Weil structures: the restriction of the comparison
`j_! F ⟶ j_* F` is invertible, and so is the counit `j^* j_* F ⟶ F`. -/
theorem nonempty_upperStar_extensionByZero_iso (F : WeilSheaf k₀ l U) :
    Nonempty ((upperStar j).obj ((extensionByZero j).obj F) ≅ F) :=
  ⟨ObjectProperty.isoMk _ ((extensionByZeroCompUpperStarCompιIso j).app F)⟩

end AlgebraicGeometry.WeilSheaf
