/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization
public import WeilConjectures.TraceFormula.Specialization.DeformationUnitClass

/-!

# Reduction of the specialization of the class of a component to the component

Let `j : B ⟶ F` be a proper open subscheme of the fixed locus with a rational point `b` whose
image is all of `B`, and `e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` the adjoint of `ℚ̄_ℓ ≅ j^! ℚ̄_ℓ` (the last factor of
`BorelMooreSection.componentClass`,
`ProEtale.CondensedRing.Correspondence.IsContractingAt.componentCounit`). The identity
`SpecializesComponentClass` for the exchange `ν_F` of the fixed loci follows from three facts:

* `Ψ_F(e)` is invertible (the complement `F ∖ B` does not meet the point `y`);
* on `j_! ℚ̄_ℓ`, `ν_F` is, through an identification
  `φ : Ra_{F'!} Ψ_F j_! ℚ̄_ℓ ⟶ Ra_{B''!} Ψ_B ℚ̄_ℓ`, the inverse proper exchange `ν_B` of the
  deformation of `B` (`deformationCompactSupportExchange`), followed by
  `Ψ_s(Ra_{B!} ≅ Ra_{F!} j_!)`;
* `φ` maps the specialization of the unit class of `F'`, corrected by `Ψ_F(e)⁻¹`, to the
  specialization `Ra_{B''!}(σ_B) [B'']` of the unit class of the special fibre `B''` of the
  deformation of `B` (`componentSpecializationUnit`).

The last step is then `unitClass_comp_map_comp_deformationCompactSupportExchange_app`. This file
contains the abstract cancellation (`comp_map_comp_app_eq_of_isIso_map`, and the forms
`comp_map_comp_app_eq_of_eq_comp`, `comp_map_comp_app_eq_of_eq_comp'` to be applied to a goal).

## Implementation notes

Instantiating the cancellation at the concrete data and closing `SpecializesComponentClass` hits
the trap described in `PointExchangeOnComponentBdc`: the `MonObj` instances of `ℚ̄_ℓ` in terms
elaborated here carry the synthesized `Precoherent Profinite` proof, those coming from the types
of earlier declarations carry `ProEtale.pointLowerStar._proof_1`, and the unifier and the kernel
then unfold the derived categories. The proof-normalizing tactic of
`pointCompactSupportExchangeOfSeparated_app_lowerStar_ambient` applied to the full goal did not
finish within 10 minutes.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {𝒞 𝒞' 𝒮 𝒮' : Type*} [Category 𝒞] [Category 𝒞'] [Category 𝒮] [Category 𝒮']

/-- The abstract reduction: for a natural `ν : Ψ ⋙ L' ⟶ L ⋙ Ψs` and `e : P ⟶ U` with `Ψ(e)`
invertible, if `ν(P) = φ ≫ ν_B ≫ Ψs(m)`, `c' ≫ L'(σ ≫ Ψ(e)⁻¹) ≫ φ = w` and
`w ≫ ν_B = σs ≫ Ψs(c)`, then `c' ≫ L'(σ) ≫ ν(U) = σs ≫ Ψs(c ≫ m ≫ L(e))`. -/
lemma comp_map_comp_app_eq_of_isIso_map {Ψ : 𝒞 ⥤ 𝒞'} {L' : 𝒞' ⥤ 𝒮'} {L : 𝒞 ⥤ 𝒮}
    {Ψs : 𝒮 ⥤ 𝒮'} (ν : Ψ ⋙ L' ⟶ L ⋙ Ψs) {P U : 𝒞} (e : P ⟶ U) [IsIso (Ψ.map e)] {u' W : 𝒮'}
    {u V : 𝒮} {U' : 𝒞'} (c' : u' ⟶ L'.obj U') (σ : U' ⟶ Ψ.obj U) (σs : u' ⟶ Ψs.obj u)
    (c : u ⟶ V) (m : V ⟶ L.obj P) (φ : L'.obj (Ψ.obj P) ⟶ W) (νB : W ⟶ Ψs.obj V) (w : u' ⟶ W)
    (h₁ : ν.app P = φ ≫ νB ≫ Ψs.map m) (h₂ : c' ≫ L'.map (σ ≫ inv (Ψ.map e)) ≫ φ = w)
    (h₃ : w ≫ νB = σs ≫ Ψs.map c) :
    c' ≫ L'.map σ ≫ ν.app U = σs ≫ Ψs.map (c ≫ m ≫ L.map e) := by
  have hn : L'.map (Ψ.map e) ≫ ν.app U = ν.app P ≫ Ψs.map (L.map e) := ν.naturality e
  have hσ : L'.map σ = L'.map (σ ≫ inv (Ψ.map e)) ≫ L'.map (Ψ.map e) := by
    rw [← L'.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hσ, Category.assoc, hn, h₁, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    Category.assoc c', h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₃]

end Abstract

section AbstractImplicit

variable {𝒞 𝒞' 𝒮 𝒮' : Type*} {_ : Category 𝒞} {_ : Category 𝒞'} {_ : Category 𝒮}
  {_ : Category 𝒮'}

/-- `comp_map_comp_app_eq_of_isIso_map` for a morphism `cls` equal to `c ≫ m ≫ L(e)`, with the
invertibility of `Ψ(e)` as an explicit hypothesis (to be applied to a goal, all of whose terms
are then taken from the goal). -/
lemma comp_map_comp_app_eq_of_eq_comp {Ψ : 𝒞 ⥤ 𝒞'} {L' : 𝒞' ⥤ 𝒮'} {L : 𝒞 ⥤ 𝒮}
    {Ψs : 𝒮 ⥤ 𝒮'} {ν : Ψ ⋙ L' ⟶ L ⋙ Ψs} {P U : 𝒞} {e : P ⟶ U} (hI : IsIso (Ψ.map e))
    {u' W : 𝒮'} {u V : 𝒮} {U' : 𝒞'} {c' : u' ⟶ L'.obj U'} {σ : U' ⟶ Ψ.obj U}
    {σs : u' ⟶ Ψs.obj u} {cls : u ⟶ L.obj U} {c : u ⟶ V} {m : V ⟶ L.obj P}
    {φ : L'.obj (Ψ.obj P) ⟶ W} {νB : W ⟶ Ψs.obj V} {w : u' ⟶ W}
    (hcls : cls = c ≫ m ≫ L.map e) (h₁ : ν.app P = φ ≫ νB ≫ Ψs.map m)
    (h₂ : c' ≫ L'.map (σ ≫ inv (Ψ.map e)) ≫ φ = w) (h₃ : w ≫ νB = σs ≫ Ψs.map c) :
    c' ≫ L'.map σ ≫ ν.app U = σs ≫ Ψs.map cls := by
  subst hcls
  exact comp_map_comp_app_eq_of_isIso_map ν e c' σ σs c m φ νB w h₁ h₂ h₃

/-- `comp_map_comp_app_eq_of_eq_comp` with the last two hypotheses merged. -/
lemma comp_map_comp_app_eq_of_eq_comp' {Ψ : 𝒞 ⥤ 𝒞'} {L' : 𝒞' ⥤ 𝒮'} {L : 𝒞 ⥤ 𝒮}
    {Ψs : 𝒮 ⥤ 𝒮'} {ν : Ψ ⋙ L' ⟶ L ⋙ Ψs} {P U : 𝒞} {e : P ⟶ U} (hI : IsIso (Ψ.map e))
    {u' W : 𝒮'} {u V : 𝒮} {U' : 𝒞'} {c' : u' ⟶ L'.obj U'} {σ : U' ⟶ Ψ.obj U}
    {σs : u' ⟶ Ψs.obj u} {cls : u ⟶ L.obj U} {c : u ⟶ V} {m : V ⟶ L.obj P}
    {φ : L'.obj (Ψ.obj P) ⟶ W} {νB : W ⟶ Ψs.obj V}
    (hcls : cls = c ≫ m ≫ L.map e) (h₁ : ν.app P = φ ≫ νB ≫ Ψs.map m)
    (h₂ : c' ≫ L'.map (σ ≫ inv (Ψ.map e)) ≫ φ ≫ νB = σs ≫ Ψs.map c) :
    c' ≫ L'.map σ ≫ ν.app U = σs ≫ Ψs.map cls :=
  comp_map_comp_app_eq_of_eq_comp hI hcls h₁ rfl (by simpa only [Category.assoc] using h₂)

end AbstractImplicit


open Scheme

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
  (νX : PointCompactSupportExchange (ℓ := ℓ) X k' (y ≫ c.c₁)) (F : c.FixedLocus)
  {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
  [IsOpenImmersion j.left]

variable {F} in
/-- The adjoint `j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ℚ̄_ℓ ≅ j^! ℚ̄_ℓ`, the last factor of the class of `B`
(`BorelMooreSection.componentClass`). -/
noncomputable abbrev componentCounit :
    (boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  ((boundedConstructibleUpperShriekAdjunction ℓ j).homEquiv
    _ _).symm (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).inv

/-- The specialization unit `σ_B : ℚ̄_ℓ ⟶ Ψ_B ℚ̄_ℓ` of the deformation of `B` along `ker b`. -/
noncomputable abbrev componentSpecializationUnit (b : RationalPoint B) :=
  NearbyCyclesModel.boundedConstructibleUnit ℓ
    ((deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel B b.left.ker k') (deformationModel_exists_comp_ε B _ k'))

end Correspondence.IsContractingAt

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
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _))

-- the objects `𝟙_ _` of the statement come with different instance paths, and checking the
-- cancellation `comp_map_comp_app_eq_of_eq_comp'` against them unfolds the derived categories
/-- **The class identity from facts (I)–(III)** (`comp_map_comp_app_eq_of_eq_comp'` for the
specialization data `T`): if `Ψ_F(e)` is invertible for the counit `e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of the
component (fact (I)), if `ν_F` on `j_! ℚ̄_ℓ` factors as `φ ≫ ν_B ≫ Ψ_s(Ra_{B!} ≅ Ra_{F!} j_!)` (fact
(II)), and if `φ` maps `Ra_{F'!}(σ_F ≫ Ψ_F(e)⁻¹) [F']` to an element that `ν_B` sends to
`σ_s Ψ_s([B])` (fact (III) with the unit class identity of `ν_B`), then `ν_F` specializes the class
of `B`. In the concrete situation of `IsContractingAt.specializesComponentClass_deformation` this
reduction elaborates in seconds, unlike the cancellation applied to the goal directly. -/
theorem specializesComponentClass_of_eq [IsProper F'.F.hom]
    (νF : T.ΨF ⋙ boundedConstructibleLowerShriek ℓ (toPoint F'.F) ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F.F) ⋙ Ψpt)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] (hI : IsIso (T.ΨF.map (IsContractingAt.componentCounit (ℓ := ℓ) j)))
    {W : Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleLowerShriek ℓ (toPoint F'.F)).obj
      (T.ΨF.obj ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _))) ⟶ W)
    (νB : W ⟶ Ψpt.obj ((boundedConstructibleLowerShriek ℓ (toPoint B)).obj (𝟙_ _)))
    (h₁ : νF.app ((boundedConstructibleLowerShriek ℓ j).obj (𝟙_ _)) = φ ≫ νB ≫
      Ψpt.map ((lowerShriekCompOfEq ℓ j (toPoint F.F) (comp_toPoint j)).hom.app (𝟙_ _)))
    (h₂ : BorelMooreSection.unitClass ℓ F'.F ≫ (boundedConstructibleLowerShriek ℓ
        (toPoint F'.F)).map (T.σF ≫ inv (T.ΨF.map (IsContractingAt.componentCounit (ℓ := ℓ) j))) ≫
        φ ≫ νB = σpt ≫ Ψpt.map (BorelMooreSection.unitClass ℓ B)) :
    T.SpecializesComponentClass σpt νF j :=
  comp_map_comp_app_eq_of_eq_comp' hI (c := BorelMooreSection.unitClass ℓ B)
    (m := (lowerShriekCompOfEq ℓ j (toPoint F.F) (comp_toPoint j)).hom.app (𝟙_ _))
    (BorelMooreSection.componentClass.eq_1 ℓ j) h₁ h₂

end Correspondence.TraceSpecialization

end AlgebraicGeometry.ProEtale.CondensedRing
