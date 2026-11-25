/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The dualizing maps along a proper morphism of trait models: the formal inputs

Let `D` be a family of dualizing maps of nearby cycles over generic bases
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`), and `i : Z' ⟶ Z` a morphism of proper
trait models over a generic base, over proper morphisms `i₁ : Y₁ ⟶ X₁` (generic) and
`i₂ : Y' ⟶ X'` (special), e.g. a closed immersion of trait models. Let
`ν_i : Ri₂_! Ψ_{Z'} ⟶ Ψ_Z Ri₁_!` invert the proper exchange `χ_i` under `Ri_! ≅ Ri_*`, and
`β_i : Ψ_{Z'} Ri₁^! ⟶ Ri₂^! Ψ_Z` be its exceptional adjoint
(`ProEtale.CondensedRing.exceptionalExchange`). The closed-immersion law of blueprint
`sec-Base-change-for-nearby-cycles` (4) (`lemma-nearby-duality-slice--1`, "the map `θ`") is
```
θ_{Z'} ∘ Ψ_{Z'}(ρ) = ρ' ∘ Ri₂^!(θ_Z) ∘ β_i(ω_{X₁})
```
for the composition isomorphisms `ρ : Ri₁^! ω_{X₁} ≅ ω_{Y₁}`, `ρ' : Ri₂^! ω_{X'} ≅ ω_{Y'}`. Both
sides are maps to the dualizing complex of the proper `Y'`, hence determined by their traces
(`NearbyCyclesModel.eq_of_map_comp_trace_eq`), and the traces are compared after the invertible
proper exchange `χ_{Z'}`. This file provides the ingredients of that comparison:

* the counit of a composite adjunction through conjugate composition isomorphisms
  (`CategoryTheory.Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app`), and the abstract
  composition of traces
  (`CategoryTheory.map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app`);
* the composition of traces `tr_Y ∘ Rb_*(ρ) = tr_X ∘ Ra_*(Ri_* Ri^! ω_X ⟶ ω_X)` for
  `b = i ≫ a` proper
  (`ProEtale.CondensedRing.lowerStar_map_upperShriekUnitCompOfEq_hom_comp_counit`)
  and the naturality of the trace of `i`
  (`ProEtale.CondensedRing.lowerStar_map_upperShriek_map_comp_counit`);
* the exceptional adjunction defining `β_i`: `ε_{i₂} ∘ Ri₂_*(β_i) ∘ χ_i = Ψ_Z(ε_{i₁})`
  (`CategoryTheory.app_comp_map_mateEquiv_app_comp_inv_app_comp_counit_app`);
* the diagram chase assembling these with the trace identities of `θ_Z`, `θ_{Z'}` and the
  composition law of the proper exchanges (`CategoryTheory.closedImmersionLaw_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section Abstract

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- The counit of a composite adjunction through a conjugate composition isomorphism: if
`u : Rb ≅ Ra ⋙ Ri` is the conjugate of `c : Lb ≅ Li ⋙ La`, the counit of `Lb ⊣ Rb` after
`Lb(u⁻¹)` is `c` followed by the counits of `Li ⊣ Ri` and `La ⊣ Ra`. -/
lemma Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app {Li : C ⥤ D} {Ri : D ⥤ C}
    {La : D ⥤ E} {Ra : E ⥤ D} {Lb : C ⥤ E} {Rb : E ⥤ C} (adji : Li ⊣ Ri) (adja : La ⊣ Ra)
    (adjb : Lb ⊣ Rb) (c : Lb ≅ Li ⋙ La) (N : E) :
    Lb.map ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N) ≫ adjb.counit.app N =
      c.hom.app _ ≫ La.map (adji.counit.app (Ra.obj N)) ≫ adja.counit.app N := by
  have := conjugateEquiv_counit (adji.comp adja) adjb c.hom N
  rw [Adjunction.comp_counit_app] at this
  exact this

/-- **Composition of traces, abstractly**: for adjunctions `Li ⊣ Ri`, `La ⊣ Ra`, `Lb ⊣ Rb`, a
composition isomorphism `c : Lb ≅ Li ⋙ La` with conjugate `u : Rb ≅ Ra ⋙ Ri`, and identifications
`e : L ≅ S` of the left adjoints with functors `S` compatible with `c` and a composition
isomorphism `s : Si ⋙ Sa ≅ Sb`, the "trace" `Sb Rb N ≅ Lb Rb N ⟶ N` after `Sb(u⁻¹)` is the
composite of the traces of `Si` and `Sa`. -/
lemma map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app {Li : C ⥤ D} {Ri : D ⥤ C}
    {La : D ⥤ E} {Ra : E ⥤ D} {Lb : C ⥤ E} {Rb : E ⥤ C} (adji : Li ⊣ Ri) (adja : La ⊣ Ra)
    (adjb : Lb ⊣ Rb) (c : Lb ≅ Li ⋙ La) {Si : C ⥤ D} {Sa : D ⥤ E} {Sb : C ⥤ E} (ei : Li ≅ Si)
    (ea : La ≅ Sa) (eb : Lb ≅ Sb) (s : Si ⋙ Sa ≅ Sb)
    (hcomp : ∀ K, c.hom.app K ≫ ea.hom.app (Li.obj K) ≫ Sa.map (ei.hom.app K) =
      eb.hom.app K ≫ s.inv.app K) (N : E) :
    Sb.map ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N) ≫ eb.inv.app _ ≫
        adjb.counit.app N =
      s.inv.app _ ≫ Sa.map (ei.inv.app _ ≫ adji.counit.app (Ra.obj N)) ≫ ea.inv.app _ ≫
        adja.counit.app N := by
  have hc : eb.inv.app (Ri.obj (Ra.obj N)) ≫ c.hom.app _ =
      s.inv.app _ ≫ Sa.map (ei.inv.app _) ≫ ea.inv.app _ := by
    rw [← cancel_mono (ea.hom.app _), ← cancel_mono (Sa.map (ei.hom.app _))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, ← Sa.map_comp,
      CategoryTheory.Functor.map_id]
    rw [hcomp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  have hn := eb.inv.naturality ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N)
  have hn' := ea.inv.naturality (adji.counit.app (Ra.obj N))
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn hn' ⊢
  rw [reassoc_of% hn, Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app,
    reassoc_of% hc, Functor.map_comp, Category.assoc, reassoc_of% hn']

/-- **The exceptional adjoint of an inverse proper exchange, abstractly**: if `ν : Ψ' ⋙ L₂ ⟶
L₁ ⋙ Ψ` inverts `χ : S₁ ⋙ Ψ ⟶ Ψ' ⋙ S₂` under identifications `e₁ : L₁ ≅ S₁`, `e₂ : L₂ ≅ S₂`, then
its mate `β` for `L₁ ⊣ R₁`, `L₂ ⊣ R₂` satisfies `ε₂ ∘ S₂(β) ∘ χ(R₁) = Ψ(ε₁)`, where
`εⱼ : Sⱼ Rⱼ ≅ Lⱼ Rⱼ ⟶ 𝟭` are the counits read through `eⱼ`. -/
lemma app_comp_map_mateEquiv_app_comp_inv_app_comp_counit_app {C' D' : Type*} [Category C']
    [Category D'] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'} {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) {Ψ' : C ⥤ C'} {Ψ : D ⥤ D'} (ν : Ψ' ⋙ L₂ ⟶ L₁ ⋙ Ψ) {S₁ : C ⥤ D}
    {S₂ : C' ⥤ D'} (e₁ : L₁ ≅ S₁) (e₂ : L₂ ≅ S₂) (χ : S₁ ⋙ Ψ ⟶ Ψ' ⋙ S₂)
    (hν : ∀ M, χ.app M ≫ e₂.inv.app (Ψ'.obj M) ≫ ν.app M = Ψ.map (e₁.inv.app M)) (N : D) :
    χ.app (R₁.obj N) ≫ S₂.map ((mateEquiv adj₁ adj₂ ν).app N) ≫ e₂.inv.app _ ≫
        adj₂.counit.app (Ψ.obj N) =
      Ψ.map (e₁.inv.app (R₁.obj N) ≫ adj₁.counit.app N) := by
  have hn := e₂.inv.naturality ((mateEquiv adj₁ adj₂ ν).app N)
  have hm := mateEquiv_counit adj₁ adj₂ ν N
  have hν' := hν (R₁.obj N)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn hm hν' ⊢
  rw [reassoc_of% hn, hm, reassoc_of% hν', Functor.map_comp]

/-- The diagram chase of the closed-immersion law `θ_{Z'} ∘ Ψ_{Z'}(ρ) = ρ' ∘ Ri₂^!(θ_Z) ∘ β_i`
of the dualizing maps (blueprint `sec-Base-change-for-nearby-cycles` (4)), for
functors `S` (specialization of the point), `B`, `A` (global sections on the two special
fibres): the traces of `θ' ∘ Ψ'(ρ)` and of `ρ' ∘ i₂^!(θ) ∘ β` agree after the proper exchange
`χA`, by the naturality squares `h₁, h₅, h₆, h₇, h₁₀`, the trace identities `h₂, h₁₁` of `θ'`
and `θ`, the composition of traces `h₃, h₄` on both fibres, the composition law `h₉` of the
proper exchanges and the exceptional adjunction `h₈`. -/
lemma closedImmersionLaw_aux {C₀ CS CB CA : Type*} [Category C₀] [Category CS] [Category CB]
    [Category CA] (S : CS ⥤ C₀) (B : CB ⥤ C₀) (A : CA ⥤ C₀)
    {U : C₀} {P₁ P₂ P₃ P₄ P₅ : CB} {Q₀ Q₆ Q₇ Q₈ W : CS}
    {R₉ R₁₀ R₁₁ R₁₂ R₁₃ R₁₄ : CA}
    (χA : S.obj Q₀ ⟶ B.obj P₁) (mρ : P₁ ⟶ P₂) (mθ' : P₂ ⟶ P₃) (tr' : B.obj P₃ ⟶ U)
    (mβ : P₁ ⟶ P₄) (mθ₂ : P₄ ⟶ P₅) (mρ₂ : P₅ ⟶ P₃)
    (sρ : Q₀ ⟶ Q₆) (χω : S.obj Q₆ ⟶ B.obj P₂) (strY : Q₆ ⟶ W) (σinv : S.obj W ⟶ U)
    (sE : Q₀ ⟶ Q₇) (sε₁ : Q₇ ⟶ Q₈) (strX : Q₈ ⟶ W)
    (e₅ : B.obj P₅ ⟶ A.obj R₉) (aε₂ : R₉ ⟶ R₁₀) (trX' : A.obj R₁₀ ⟶ U)
    (e₄ : B.obj P₄ ⟶ A.obj R₁₁) (aiθ : R₁₁ ⟶ R₉) (e₁ : B.obj P₁ ⟶ A.obj R₁₂)
    (aiβ : R₁₂ ⟶ R₁₁) (aε₂Ψ : R₁₁ ⟶ R₁₃) (aθ : R₁₃ ⟶ R₁₀) (aχi : R₁₄ ⟶ R₁₂)
    (aΨε₁ : R₁₄ ⟶ R₁₃) (χZi : S.obj Q₇ ⟶ A.obj R₁₄) (χZω : S.obj Q₈ ⟶ A.obj R₁₃)
    (h₁ : χA ≫ B.map mρ = S.map sρ ≫ χω)
    (h₂ : χω ≫ B.map mθ' ≫ tr' = S.map strY ≫ σinv)
    (h₃ : sρ ≫ strY = sE ≫ sε₁ ≫ strX) (h₄ : B.map mρ₂ ≫ tr' = e₅ ≫ A.map aε₂ ≫ trX')
    (h₅ : B.map mθ₂ ≫ e₅ = e₄ ≫ A.map aiθ) (h₆ : B.map mβ ≫ e₄ = e₁ ≫ A.map aiβ)
    (h₇ : aiθ ≫ aε₂ = aε₂Ψ ≫ aθ) (h₈ : aχi ≫ aiβ ≫ aε₂Ψ = aΨε₁)
    (h₉ : χA ≫ e₁ = S.map sE ≫ χZi ≫ A.map aχi)
    (h₁₀ : χZi ≫ A.map aΨε₁ = S.map sε₁ ≫ χZω)
    (h₁₁ : χZω ≫ A.map aθ ≫ trX' = S.map strX ≫ σinv) :
    χA ≫ B.map (mρ ≫ mθ') ≫ tr' = χA ≫ B.map (mβ ≫ mθ₂ ≫ mρ₂) ≫ tr' := by
  have h₃' := congrArg S.map h₃
  have h₇' := congrArg A.map h₇
  have h₈' := congrArg A.map h₈
  simp only [Functor.map_comp, Category.assoc] at h₃' h₇' h₈' ⊢
  rw [h₄, reassoc_of% h₅, reassoc_of% h₆, reassoc_of% h₇', reassoc_of% h₉, reassoc_of% h₈',
    reassoc_of% h₁₀, h₁₁, ← reassoc_of% h₃', ← h₂, reassoc_of% h₁]

end Abstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Trace

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y P : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **Composition of traces** for proper morphisms `i : Y ⟶ X`, `a_X : X ⟶ P` and `a_Y = i ≫ a_X`:
the trace `Ra_{Y*} Ra_Y^! ℚ̄_ℓ ≅ Ra_{Y!} Ra_Y^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` after the composition isomorphism
`Ri^! Ra_X^! ℚ̄_ℓ ≅ Ra_Y^! ℚ̄_ℓ` is the trace of `a_X` after `Ra_{X*}` of the trace
`Ri_* Ri^! ⟶ 𝟭` of `i`. -/
lemma lowerStar_map_upperShriekUnitCompOfEq_hom_comp_counit (i : Y ⟶ X) (aX : X ⟶ P)
    {aY : Y ⟶ P} (w : i ≫ aX = aY) [IsProper i.left] [IsProper aX.left] [IsProper aY.left] :
    (boundedConstructibleLowerStar ℓ aY).map (upperShriekUnitCompOfEq ℓ i aX w).hom ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aY).inv.app
          ((boundedConstructibleUpperShriek ℓ aY).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ aY).counit.app (𝟙_ _) =
      (boundedConstructibleLowerStarCompOfEq ℓ i aX w).inv.app
          ((boundedConstructibleUpperShriek ℓ i).obj
            ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
        (boundedConstructibleLowerStar ℓ aX).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).inv.app
              ((boundedConstructibleUpperShriek ℓ i).obj
                ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
            (boundedConstructibleUpperShriekAdjunction ℓ i).counit.app
              ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aX).inv.app
          ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ aX).counit.app (𝟙_ _) := by
  subst w
  have e : (boundedConstructibleLowerStarCompOfEq ℓ i aX rfl).inv.app
      ((boundedConstructibleUpperShriek ℓ i).obj
        ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) =
      (boundedConstructibleLowerStarComp ℓ i aX).inv.app
        ((boundedConstructibleUpperShriek ℓ i).obj
          ((boundedConstructibleUpperShriek ℓ aX).obj (𝟙_ _))) := by
    simp [boundedConstructibleLowerStarCompOfEq]
  rw [e, upperShriekUnitCompOfEq_rfl]
  exact map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app
    (boundedConstructibleUpperShriekAdjunction ℓ i)
    (boundedConstructibleUpperShriekAdjunction ℓ aX)
    (boundedConstructibleUpperShriekAdjunction ℓ (i ≫ aX))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ i aX)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ aX)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (i ≫ aX))
    (boundedConstructibleLowerStarComp ℓ i aX)
    (fun K ↦ boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ i aX K) (𝟙_ _)

/-- The trace `Rf_* Rf^! ⟶ 𝟭` of a proper morphism (the counit of `Rf_! ⊣ Rf^!` read through
`Rf_! ≅ Rf_*`) is natural. -/
lemma lowerStar_map_upperShriek_map_comp_counit (f : Y ⟶ X) [IsProper f.left]
    {M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (θ : M ⟶ N) :
    (boundedConstructibleLowerStar ℓ f).map ((boundedConstructibleUpperShriek ℓ f).map θ) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
          ((boundedConstructibleUpperShriek ℓ f).obj N) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app N =
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app
          ((boundedConstructibleUpperShriek ℓ f).obj M) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ f).counit.app M) ≫ θ := by
  have hc := (boundedConstructibleUpperShriekAdjunction ℓ f).counit_naturality θ
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.naturality
    ((boundedConstructibleUpperShriek ℓ f).map θ)
  dsimp only [Functor.id_obj, Functor.comp_obj] at hc hn ⊢
  rw [Category.assoc, ← hc, reassoc_of% hn]

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
