/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Integral
import WeilConjectures.TraceFormula.LocalTerm

/-!

# The class of a proper open and closed component

Let `j : B ⟶ F` be an open immersion of separated `k`-schemes of finite type with `B` proper. The
*class* of `B` in `Ra_{F!} ℚ̄_ℓ` is the unit class `ℚ̄_ℓ ⟶ Ra_{B!} ℚ̄_ℓ` of `B` followed by
`Ra_{B!} ℚ̄_ℓ ≅ Ra_{F!} j_! ℚ̄_ℓ ⟶ Ra_{F!} ℚ̄_ℓ`
(`ProEtale.CondensedRing.BorelMooreSection.componentClass`). The integral over `B` of the
restriction of a Borel–Moore section `z` of `F` is the adjoint `z^♭ : Ra_{F!} ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `z`
precomposed with the class of `B`
(`ProEtale.CondensedRing.BorelMooreSection.integral_restrict`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {𝒰 𝒳 𝒮 : Type*} [Category 𝒰] [Category 𝒳] [Category 𝒮]

/-- The adjoint for `L₁ ⊣ R₁` of `s ≫ Rj(z) ≫ e^∨⁻¹`, where `e^∨ : R₁ ≅ RF ⋙ Rj` is the conjugate
of an isomorphism `e : L₁ ≅ Lj ⋙ LF`, is `LF(s^♭) ≫ z^♭` read through `e`. -/
lemma homEquiv_symm_comp_map_comp_conjugateIsoEquiv_inv {L₁ : 𝒰 ⥤ 𝒮} {R₁ : 𝒮 ⥤ 𝒰}
    {Lj : 𝒰 ⥤ 𝒳} {Rj : 𝒳 ⥤ 𝒰} {LF : 𝒳 ⥤ 𝒮} {RF : 𝒮 ⥤ 𝒳} (adj₁ : L₁ ⊣ R₁) (adjj : Lj ⊣ Rj)
    (adjF : LF ⊣ RF) (e : L₁ ≅ Lj ⋙ LF) {P' : 𝒰} {P : 𝒳} {Q : 𝒮} (s : P' ⟶ Rj.obj P)
    (z : P ⟶ RF.obj Q) :
    (adj₁.homEquiv _ _).symm
        (s ≫ Rj.map z ≫ ((conjugateIsoEquiv adj₁ (adjj.comp adjF) e.symm).inv.app Q)) =
      e.hom.app P' ≫ LF.map ((adjj.homEquiv _ _).symm s) ≫ (adjF.homEquiv _ _).symm z := by
  have h := conjugateEquiv_counit (adjj.comp adjF) adj₁ e.hom Q
  simp only [Functor.comp_obj, Adjunction.comp_counit_app] at h
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]
  rw [h, ← L₁.map_comp_assoc, e.hom.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← LF.map_comp_assoc (Lj.map (Rj.map z)), adjj.counit_naturality, LF.map_comp_assoc]

end Abstract

open Scheme

namespace BorelMooreSection

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {B F : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom]
  [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom] (j : B ⟶ F)
  [IsOpenImmersion j.left]

/-- The *class* `ℚ̄_ℓ ⟶ Ra_{F!} ℚ̄_ℓ` of a proper open subscheme `j : B ⟶ F`: the unit class of `B`,
followed by `Ra_{B!} ℚ̄_ℓ ≅ Ra_{F!} j_! ℚ̄_ℓ` and `Ra_{F!}` of the adjoint `j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of the
identification `ℚ̄_ℓ ≅ Rj^! ℚ̄_ℓ`. -/
noncomputable def componentClass :
    𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint F)).obj
        (𝟙_ _) :=
  unitClass ℓ B ≫ (lowerShriekCompOfEq ℓ j (toPoint F) (comp_toPoint j)).hom.app (𝟙_ _) ≫
    (boundedConstructibleLowerShriek ℓ (toPoint F)).map
      (((boundedConstructibleUpperShriekAdjunction ℓ j).homEquiv
        _ _).symm (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv)

variable {ℓ j}

omit [IsOpenImmersion j.left] in
/-- For a morphism `a_B` equal to `j ≫ a_F`, the `Ra_{B!} ⊣ Ra_B^!` adjoint of
`s ≫ Rj^!(z) ≫ (Rj^! Ra_F^! ℚ̄_ℓ ≅ Ra_B^! ℚ̄_ℓ)` is
`Ra_{B!} ≅ Ra_{F!} j_! ⟶ Ra_{F!}` of the adjoint of `s`, followed by the adjoint `z^♭` of `z`. -/
lemma homEquiv_symm_comp_map_comp_upperShriekUnitCompOfEq {aB : B ⟶ point k}
    (w : j ≫ toPoint F = aB)
    (s : 𝟙_ (Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleUpperShriek ℓ j).obj (𝟙_ _))
    (z : BorelMooreSection ℓ F) :
    ((boundedConstructibleUpperShriekAdjunction ℓ aB).homEquiv
        _ _).symm
        (s ≫ (boundedConstructibleUpperShriek ℓ j).map z ≫
          (upperShriekUnitCompOfEq ℓ j (toPoint F) w).hom) =
      (lowerShriekCompOfEq ℓ j (toPoint F) w).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint F)).map
          (((boundedConstructibleUpperShriekAdjunction ℓ j).homEquiv _ _).symm s) ≫
        ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint F)).homEquiv _ _).symm z := by
  subst w
  simp only [upperShriekUnitCompOfEq_rfl, lowerShriekCompOfEq_rfl, Iso.symm_hom, Iso.app_inv]
  exact homEquiv_symm_comp_map_comp_conjugateIsoEquiv_inv
    (boundedConstructibleUpperShriekAdjunction ℓ (j ≫ toPoint F))
    (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint F))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j (toPoint F)) s z

/-- The restriction of a Borel–Moore section, with the composition isomorphism of the dualizing
complexes written as `upperShriekUnitCompOfEq`. -/
lemma restrict_eq_upperShriekUnitCompOfEq (z : BorelMooreSection ℓ F) :
    z.restrict j = (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv ≫
      (boundedConstructibleUpperShriek ℓ j).map z ≫
      (upperShriekUnitCompOfEq ℓ j (toPoint F) (comp_toPoint j)).hom :=
  rfl

/-- **The integral of a restriction**: the integral over `B` of the restriction of a Borel–Moore
section `z` of `F` is `z^♭ : Ra_{F!} ℚ̄_ℓ ⟶ ℚ̄_ℓ` precomposed with the class of `B`. -/
theorem integral_restrict (z : BorelMooreSection ℓ F) :
    (z.restrict j).integral.asHom = componentClass ℓ j ≫
      ((boundedConstructibleUpperShriekAdjunction ℓ
        (toPoint F)).homEquiv _ _).symm z := by
  rw [integral_eq, componentClass, restrict_eq_upperShriekUnitCompOfEq, Category.assoc,
    Category.assoc]
  have h := homEquiv_symm_comp_map_comp_upperShriekUnitCompOfEq (comp_toPoint j)
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv z
  convert congrArg (unitClass ℓ B ≫ ·) h using 2

end BorelMooreSection

/-- A rational point `y` of `F` lying in the image of an open immersion `j : B ⟶ F` whose image
is `{y}` lifts to a rational point of `B` whose image is all of `B`. -/
theorem RationalPoint.exists_lift_of_range_eq_singleton {k : Type u} [Field k]
    {B F : Over (Spec (.of k))} (j : B ⟶ F) [IsOpenImmersion j.left] (y : RationalPoint F)
    (hj : Set.range j.left.base = {y.left.base (default : Spec (.of k))}) :
    ∃ b : RationalPoint B, b ≫ j = y ∧ Set.range b.left.base = Set.univ := by
  have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hy : Set.range y.left.base ⊆ Set.range j.left.base := by
    rintro _ ⟨x, rfl⟩
    rw [hj, Set.mem_singleton_iff]
    exact congrArg y.left.base (Subsingleton.elim _ _)
  obtain ⟨g, hg⟩ : ∃ g, g ≫ j.left = y.left := ⟨_, IsOpenImmersion.lift_fac j.left y.left hy⟩
  refine ⟨Over.homMk g ?_, ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, hg, Over.w y]
  · ext1
    exact hg
  · refine Set.eq_univ_of_forall fun x ↦
      ⟨(default : Spec (.of k)), j.left.isOpenEmbedding.injective ?_⟩
    have hx : j.left.base x ∈ Set.range j.left.base := ⟨x, rfl⟩
    rw [hj, Set.mem_singleton_iff] at hx
    have h := congrArg (fun f ↦ f.base (default : Spec (.of k))) hg
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [hx]
    exact h


/-- The cancellation behind `map_integral_restrict_eq_zero_of_sp_eq_zero`, in an arbitrary
category: if the square
```
  A' --p₁ ≫ p₂ ≫ p₃--> P B
  |                     ‖
  σ                     ‖
  v                     ‖
  P A -----P(a)-----> P B
```
commutes and `0 = p₁ ≫ p₂ ≫ p₃ ≫ P(z) ≫ σ⁻¹`, then `P(a ≫ z) = 0`. -/
private lemma map_comp_eq_zero_of_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒟]
    (P : 𝒞 ⥤ 𝒟) {A B : 𝒞} {A' A₁ A₂ : 𝒟} (σ : A' ⟶ P.obj A) [IsIso σ] (a : A ⟶ B)
    (z : B ⟶ A) (p₁ : A' ⟶ A₁) (p₂ : A₁ ⟶ A₂) (p₃ : A₂ ⟶ P.obj B)
    (hS : p₁ ≫ p₂ ≫ p₃ = σ ≫ P.map a) (h : 0 = p₁ ≫ p₂ ≫ p₃ ≫ P.map z ≫ inv σ) :
    P.map (a ≫ z) = 0 := by
  rw [← cancel_epi σ, ← cancel_mono (inv σ), comp_zero, zero_comp, P.map_comp]
  simp only [Category.assoc] at h ⊢
  rw [h, reassoc_of% hS]

namespace Correspondence.TraceSpecialization

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}
  (T : c.TraceSpecialization F c' F')
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- The compact-support exchange `ν_F` of the fixed loci *specializes the class* of a proper open
subscheme `j : B ⟶ F`: it maps the specialization `Ra_{F'!}(σ_F) [F']` of the unit class of the
proper special fixed locus `F'` to the specialization of the class of `B` in `Ra_{F!} ℚ̄_ℓ`
(`BorelMooreSection.componentClass`), through the unit `σ_s` of the point. -/
def SpecializesComponentClass [IsProper F'.F.hom]
    (νF : T.ΨF ⋙ boundedConstructibleLowerShriek ℓ
        (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] : Prop :=
  BorelMooreSection.unitClass ℓ F'.F ≫
      (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).map
        T.σF ≫ νF.app (𝟙_ _) = σpt ≫ Ψpt.map (BorelMooreSection.componentClass ℓ j)

/-- If the specialization data `T` has `θ_F` the dualizing map of `ν_F`, and `ν_F` maps the
specialization of the unit class of the proper `F'` to the specialization of the class of a proper
open subscheme `j : B ⟶ F`, then `sp(z) = 0` implies that the specialization of `∫_B z|_B`
vanishes: `∫_{F'} sp(z) = σ_s⁻¹ Ψ_s(∫_B z|_B) σ_s`. -/
theorem map_integral_restrict_eq_zero_of_sp_eq_zero [IsProper F'.F.hom]
    (νF : T.ΨF ⋙ boundedConstructibleLowerShriek ℓ
        (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    (hθ : T.θF = dualizingExchange ℓ σpt νF) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hS : T.SpecializesComponentClass σpt νF j)
    (z : BorelMooreSection ℓ F.F) (hz : T.sp z = 0) :
    Ψpt.map (z.restrict j).integral.asHom = 0 := by
  have h := T.integral_sp_eq σpt νF hθ z
  rw [hz, BorelMooreSection.integral_zero] at h
  rw [BorelMooreSection.integral_restrict]
  exact map_comp_eq_zero_of_comp_eq Ψpt σpt _ _ _ _ _ hS h

end Correspondence.TraceSpecialization

end AlgebraicGeometry.ProEtale.CondensedRing
