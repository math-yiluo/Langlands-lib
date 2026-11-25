/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.TraceFormula.Specialization.Integral

/-!

# Unit classes along proper morphisms

For a proper morphism `f : X ⟶ Y` the *relative unit class* `[f] : ℚ̄_ℓ ⟶ Rf_! ℚ̄_ℓ` is the unit
of `Lf^* ⊣ Rf_*` at `ℚ̄_ℓ`, read through `Lf^* ℚ̄_ℓ ≅ ℚ̄_ℓ` and `Rf_! ≅ Rf_*`
(`ProEtale.CondensedRing.properUnitClass`). For the structure map of a proper scheme it is the
unit class `BorelMooreSection.unitClass`. Relative unit classes compose:
`[f ≫ g] = Rg_!([f]) ∘ [g]` read through `R(f ≫ g)_! ≅ Rg_! Rf_!`
(`ProEtale.CondensedRing.properUnitClass_comp`), by the composition of the units of the
adjunctions `L(·)^* ⊣ R(·)_*`. In particular, for a proper morphism `r : B ⟶ F` of proper
`k`-schemes, `[B] = Ra_{F!}([r]) ∘ [F]` read through `Ra_{B!} ≅ Ra_{F!} Rr_!`
(`ProEtale.CondensedRing.unitClass_comp_map_properUnitClass`). This is the compatibility of unit
classes needed in fact (III) of `ComponentClassReduction`, for `r` the closed immersion
`componentSpecialLift : B'' ⟶ F'`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

/-- The abstract composition of unit classes: for adjunctions `fU ⊣ fL`, `gU ⊣ gL`, `FU ⊣ FL`
with `FU ≅ gU ⋙ fU`, its conjugate `fL ⋙ gL ≅ FL`, isomorphisms `fS ≅ fL`, `gS ≅ gL`, `FS ≅ FL`
compatible with `FS ≅ fS ⋙ gS`, and unit isomorphisms `ε` compatible with `FU ≅ gU ⋙ fU`, the
unit class of `F` is the composite of those of `g` and `f`. -/
lemma unitClass_comp_aux {fU : C₂ ⥤ C₁} {fL : C₁ ⥤ C₂} (af : fU ⊣ fL) {fS : C₁ ⥤ C₂}
    (If : fS ≅ fL) {gU : C₃ ⥤ C₂} {gL : C₂ ⥤ C₃} (ag : gU ⊣ gL) {gS : C₂ ⥤ C₃} (Ig : gS ≅ gL)
    {FU : C₃ ⥤ C₁} {FL : C₁ ⥤ C₃} (aF : FU ⊣ FL) {FS : C₁ ⥤ C₃} (IF : FS ≅ FL)
    (cU : FU ≅ gU ⋙ fU) (cS : fL ⋙ gL ≅ FL)
    (hcS : cS.inv = conjugateEquiv aF (ag.comp af) cU.inv) (cL : FS ≅ fS ⋙ gS)
    (hI : ∀ K, cL.hom.app K ≫ Ig.hom.app (fS.obj K) ≫ gL.map (If.hom.app K) =
      IF.hom.app K ≫ cS.inv.app K)
    {e₁ : C₁} {e₂ : C₂} {e₃ : C₃} (εf : e₁ ≅ fU.obj e₂) (εg : e₂ ≅ gU.obj e₃)
    (εF : e₁ ≅ FU.obj e₃) (hε : cU.hom.app e₃ ≫ fU.map εg.inv ≫ εf.inv = εF.inv) :
    (ag.unit.app e₃ ≫ gL.map εg.inv ≫ Ig.inv.app e₂) ≫
        gS.map (af.unit.app e₂ ≫ fL.map εf.inv ≫ If.inv.app e₁) ≫ cL.inv.app e₁ =
      aF.unit.app e₃ ≫ FL.map εF.inv ≫ IF.inv.app e₁ := by
  have hu := unit_conjugateEquiv aF (ag.comp af) cU.inv e₃
  rw [← hcS] at hu
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at hu
  have hI' : cS.inv.app e₁ ≫ gL.map (If.inv.app e₁) ≫ Ig.inv.app (fS.obj e₁) =
      IF.inv.app e₁ ≫ cL.hom.app e₁ := by
    rw [← cancel_epi (IF.hom.app e₁), Iso.hom_inv_id_app_assoc, ← reassoc_of% (hI e₁),
      ← gL.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
  have hε' : cU.inv.app e₃ ≫ εF.inv = fU.map εg.inv ≫ εf.inv := by
    rw [← hε, Iso.inv_hom_id_app_assoc]
  have key : εg.inv ≫ af.unit.app e₂ ≫ fL.map εf.inv =
      af.unit.app _ ≫ fL.map (cU.inv.app e₃) ≫ fL.map εF.inv := by
    have h := af.unit.naturality εg.inv
    simp only [Functor.id_map, Functor.comp_map] at h
    rw [reassoc_of% h, ← fL.map_comp, ← fL.map_comp, hε']
  have hn := cS.inv.naturality εF.inv
  simp only [Functor.comp_map] at hn
  rw [← cancel_mono (cL.hom.app e₁)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [← hI', reassoc_of% hn, reassoc_of% hu, ← Ig.inv.naturality]
  have h := congrArg gL.map (key =≫ If.inv.app e₁)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  rw [reassoc_of% h]

end Abstract

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Relative

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The *relative unit class* `[f] : ℚ̄_ℓ ⟶ Rf_! ℚ̄_ℓ` of a proper morphism `f`: the unit of
`Lf^* ⊣ Rf_*` at `ℚ̄_ℓ`, read through `Lf^* ℚ̄_ℓ ≅ ℚ̄_ℓ` and `Rf_! ≅ Rf_*`. -/
noncomputable def properUnitClass (f : X ⟶ Y) [IsProper f.left] :
    𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleLowerShriek ℓ f).obj (𝟙_ _) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).unit.app
      (𝟙_ _) ≫
    (boundedConstructibleLowerStar ℓ f).map
      (Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)).inv ≫
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app (𝟙_ _)

/-- **Relative unit classes compose**: `[f ≫ g] = Rg_!([f]) ∘ [g]`, read through
`R(f ≫ g)_! ≅ Rg_! Rf_!`. -/
theorem properUnitClass_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left] [IsProper g.left]
    [IsProper (f ≫ g).left] :
    properUnitClass ℓ g ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (properUnitClass ℓ f) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app (𝟙_ _) =
      properUnitClass ℓ (f ≫ g) :=
  unitClass_comp_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f ≫ g))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (f ≫ g))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g)
    (boundedConstructibleLowerStarComp ℓ f g)
    (by rw [boundedConstructibleLowerStarComp, Iso.symm_inv, conjugateIsoEquiv_apply_hom,
      Iso.symm_hom])
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g K)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g))
    (Functor.Monoidal.εIso
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)))
    (boundedConstructibleUpperStarComp_hom_app_unit ℓ f g)

/-- `properUnitClass_comp` for a morphism equal to `f ≫ g`, read through `lowerShriekCompOfEq`. -/
theorem properUnitClass_comp_of_eq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z} (w : f ≫ g = h)
    [IsProper f.left] [IsProper g.left] [IsProper h.left] :
    properUnitClass ℓ g ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (properUnitClass ℓ f) ≫ (lowerShriekCompOfEq ℓ f g w).inv.app (𝟙_ _) =
      properUnitClass ℓ h := by
  subst w
  rw [lowerShriekCompOfEq_rfl]
  exact properUnitClass_comp ℓ f g

end Relative

/-- The unit class of a proper scheme is the relative unit class of its structure map. -/
lemma unitClass_eq_properUnitClass (X : Over (Spec (.of k))) [QuasiCompact X.hom]
    [IsProper X.hom] [IsProper (toPoint X).left] :
    BorelMooreSection.unitClass ℓ X = properUnitClass ℓ (toPoint X) :=
  rfl

/-- **Unit classes along a proper morphism**: for a proper morphism `r : B ⟶ F` of proper
`k`-schemes, `[B] = Ra_{F!}([r]) ∘ [F]`, read through `Ra_{B!} ≅ Ra_{F!} Rr_!`. -/
theorem unitClass_comp_map_properUnitClass {B F : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] [QuasiCompact F.hom] [IsProper F.hom] (r : B ⟶ F) [IsProper r.left] :
    BorelMooreSection.unitClass ℓ F ≫
        (boundedConstructibleLowerShriek ℓ (toPoint F)).map
          (properUnitClass ℓ r) ≫
        (lowerShriekCompOfEq ℓ r (toPoint F) (comp_toPoint r)).inv.app (𝟙_ _) =
      BorelMooreSection.unitClass ℓ B :=
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have : IsProper (toPoint F).left := by rw [toPoint_left]; infer_instance
  properUnitClass_comp_of_eq ℓ r (toPoint F) (comp_toPoint r)

/-- **The unit-class step (III) on a proper morphism `r : B ⟶ F` of proper schemes**: a map
`ψ : P ⟶ Rr_* Q` with `s ≫ ψ = η_r(ℚ̄_ℓ) ≫ Rr_*(ε⁻¹ ≫ σ)` for `s : ℚ̄_ℓ ⟶ P`, `σ : ℚ̄_ℓ ⟶ Q`, read
through `Ra_{F!} Rr_* ≅ Ra_{F!} Rr_! ≅ Ra_{B!}`, maps `Ra_{F!}(s) [F]` to `Ra_{B!}(σ) [B]`. For
`r = componentSpecialLift`, `ψ = ι'^* χ_{ιj} ≫ counit` and `s = σ_F ≫ Ψ_F(e)⁻¹` this is fact
(III) of `ComponentClassReduction`, reduced to the identity `s ≫ ψ = η_r ≫ Rr_*(ε⁻¹ ≫ σ_B)` on
`F'`. -/
theorem unitClass_comp_map_comp_lowerShriekCompOfEq_inv {B F : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] [QuasiCompact F.hom] [IsProper F.hom] (r : B ⟶ F)
    [IsProper r.left] {P : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {Q : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (s : 𝟙_ _ ⟶ P)
    (ψ : P ⟶ (boundedConstructibleLowerStar ℓ r).obj Q)
    (σ : 𝟙_ _ ⟶ Q)
    (h : s ≫ ψ = (boundedConstructibleUpperStarLowerStarAdjunction ℓ r).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ r).map
        ((Functor.Monoidal.εIso
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r)).inv ≫ σ)) :
    BorelMooreSection.unitClass ℓ F ≫
        (boundedConstructibleLowerShriek ℓ (toPoint F)).map
          (s ≫ ψ ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app Q) ≫
        (lowerShriekCompOfEq ℓ r (toPoint F) (comp_toPoint r)).inv.app Q =
      BorelMooreSection.unitClass ℓ B ≫
        (boundedConstructibleLowerShriek ℓ (toPoint B)).map σ := by
  have hr : s ≫ ψ ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app Q =
      properUnitClass ℓ r ≫
        (boundedConstructibleLowerShriek ℓ r).map σ := by
    rw [reassoc_of% h, properUnitClass, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc, Category.assoc,
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.naturality]
  have hn := (lowerShriekCompOfEq ℓ r (toPoint F) (comp_toPoint r)).inv.naturality σ
  simp only [Functor.comp_map] at hn
  rw [hr, CategoryTheory.Functor.map_comp, Category.assoc, hn,
    ← unitClass_comp_map_properUnitClass ℓ r]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
