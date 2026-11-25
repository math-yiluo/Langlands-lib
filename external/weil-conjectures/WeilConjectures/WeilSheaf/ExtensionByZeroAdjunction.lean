/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes. The extension by zero `j_!` and the
pullback `j^*` of pro-étale Weil sheaves are the extension by zero and the pullback along the base
change `j̄ : Ū ⟶ X̄`, with the Weil structures transported along the Frobenius exchange
isomorphisms. These exchange isomorphisms are mates under `j̄_! ⊣ j̄^*`
(`ProEtale.mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv`), so the
adjunction lifts to pro-étale Weil sheaves, with the unit and the counit of `j̄_! ⊣ j̄^*`
(`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`). Its unit is an
isomorphism: `j_!` is fully faithful.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction`: `j_! ⊣ j^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]

/-- **Mates along adjoint equivalences in the two directions.** Let `E₁ : C ≌ D` and
`E₂ : E ≌ F` be equivalences, `σ : G ⋙ E₂.functor ≅ E₁.functor ⋙ H` and
`τ : H ⋙ E₂.inverse ≅ E₁.inverse ⋙ G`. If the mate of `τ.hom` under the adjunctions
`E₁.inverse ⊣ E₁.functor` and `E₂.inverse ⊣ E₂.functor` is `σ.inv`, then the mate of `σ.hom`
under `E₁.functor ⊣ E₁.inverse` and `E₂.functor ⊣ E₂.inverse` is `τ.inv`. -/
lemma mateEquiv_toAdjunction_hom_eq_inv (E₁ : C ≌ D) (E₂ : E ≌ F) {G : C ⥤ E} {H : D ⥤ F}
    (σ : G ⋙ E₂.functor ≅ E₁.functor ⋙ H) (τ : H ⋙ E₂.inverse ≅ E₁.inverse ⋙ G)
    (h : (mateEquiv E₁.symm.toAdjunction E₂.symm.toAdjunction
      (TwoSquare.mk _ _ _ _ τ.hom)) = σ.inv) :
    (mateEquiv E₁.toAdjunction E₂.toAdjunction (TwoSquare.mk _ _ _ _ σ.hom)) =
      τ.inv := by
  rw [← cancel_mono τ.hom, Iso.inv_hom_id]
  ext d
  apply E₂.functor.map_injective
  have h₁ := mateEquiv_counit E₁.toAdjunction E₂.toAdjunction (TwoSquare.mk _ _ _ _ σ.hom) d
  have h₂ := unit_mateEquiv E₁.symm.toAdjunction E₂.symm.toAdjunction
    (TwoSquare.mk _ _ _ _ τ.hom) d
  rw [show (mateEquiv E₁.symm.toAdjunction E₂.symm.toAdjunction
      (TwoSquare.mk _ _ _ _ τ.hom)).app = σ.inv.app from congrArg NatTrans.app h] at h₂
  simp only [Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit,
    Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.symm_unit] at h₁ h₂
  rw [NatTrans.comp_app, Functor.map_comp, NatTrans.id_app, Functor.map_id]
  have e₁ : E₂.functor.map ((mateEquiv E₁.toAdjunction E₂.toAdjunction
      (TwoSquare.mk _ _ _ _ σ.hom)).app d) =
      σ.hom.app (E₁.inverse.obj d) ≫ H.map (E₁.counit.app d) ≫ E₂.counitInv.app (H.obj d) := by
    rw [← cancel_mono (E₂.counit.app (H.obj d))]
    refine h₁.trans ?_
    simp
  have e₂ : E₂.functor.map (τ.hom.app d) =
      E₂.counit.app (H.obj d) ≫ H.map (E₁.counitInv.app d) ≫ σ.inv.app (E₁.inverse.obj d) := by
    rw [← cancel_epi (E₂.counitInv.app (H.obj d))]
    refine h₂.symm.trans ?_
    simp
  rw [e₁, e₂]
  simp [← H.map_comp_assoc]

end CategoryTheory

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

/-- **The Frobenius exchange isomorphisms of `φ̄_!` and `φ̄^*` are mates**: under the adjunction
`φ̄_! ⊣ φ̄^*`, the mate of the inverse of the exchange isomorphism
`φ̄_! ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_!` of the extension by zero is the exchange isomorphism
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` of the pullback. -/
lemma mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv :
    (mateEquiv (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
      (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
      (TwoSquare.mk _ _ _ _
        (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h).inv)) =
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).hom := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius
  set b := g.geometricGaloisFrobenius
  set adjUL := adicUpperStarLowerStarAdjunction l j
  set adj := adicOpenImmersionLowerShriekAdjunction l j
  set Ea := adicLowerStarEquivalence l a.asIso.symm
  set Eb := adicLowerStarEquivalence l b.asIso.symm
  set U := adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso l φ h
  set V := adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h
  -- the mate of `U⁻¹` under the inverse Frobenius equivalences is `V⁻¹`
  have h₁ : (mateEquiv Eb.symm.toAdjunction Ea.symm.toAdjunction
      (TwoSquare.mk _ _ _ _ U.inv)) = V.inv := by
    have := iterated_mateEquiv_conjugateEquiv Eb.symm.toAdjunction Ea.symm.toAdjunction adjUL adjUL
      (TwoSquare.mk _ _ _ _ U.inv)
    rw [conjugateEquiv_adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv,
      ← mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv] at this
    exact
      ((mateEquiv _ _).injective (NatTrans.ext (funext (NatTrans.congr_app this))))
  -- hence the mate of `V` under the Frobenius equivalences is `U`
  have h₂ : (mateEquiv Eb.toAdjunction Ea.toAdjunction (TwoSquare.mk _ _ _ _ V.hom)) =
      U.hom :=
    mateEquiv_toAdjunction_hom_eq_inv Eb Ea V U.symm h₁
  -- the defining property of the exchange isomorphism of the extension by zero
  have h₃ := iterated_mateEquiv_conjugateEquiv adj adj Ea.toAdjunction Eb.toAdjunction
    (TwoSquare.mk _ _ _ _ (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h).inv)
  have h₄ : conjugateEquiv (adj.comp Eb.toAdjunction) (Ea.toAdjunction.comp adj)
      (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h).inv = U.hom := by
    have := congrArg Iso.inv ((conjugateIsoEquiv (Ea.toAdjunction.comp adj)
      (adj.comp Eb.toAdjunction)).apply_symm_apply U.symm)
    exact this
  rw [h₄, ← h₂] at h₃
  exact
    ((mateEquiv _ _).injective (NatTrans.ext (funext (NatTrans.congr_app h₃))))

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `j_! ⊣ j^*` of pro-étale Weil sheaves along an open immersion `j` of
`k₀`-schemes: the adjunction `j̄_! ⊣ j̄^*` along the base change `j̄ : Ū ⟶ X̄`, which is compatible
with the transported Weil structures. -/
noncomputable def ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j :=
  IsoAlgebra.mapOfNatIsoAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)))
    _ _ (ProEtale.mateEquiv_adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso_inv l j _)

@[simp]
lemma ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction_unit_app_hom_f (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l U) :
    ((ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).unit.app F).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app F.carrier :=
  rfl

@[simp]
lemma ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction_counit_app_hom_f (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).counit.app F).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app F.carrier :=
  rfl

/-- The unit `F ⟶ j^* j_! F` of pro-étale Weil sheaves is an isomorphism: so is the unit of
`j̄_! ⊣ j̄^*`. -/
instance ProEtaleWeilSheaf.isIso_extensionByZeroUpperStarAdjunction_unit (j : U ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.extensionByZeroUpperStarAdjunction k₀ l j).unit :=
  IsoAlgebra.isIso_mapOfNatIsoAdjunction_unit _ _ _ _

end AlgebraicGeometry
