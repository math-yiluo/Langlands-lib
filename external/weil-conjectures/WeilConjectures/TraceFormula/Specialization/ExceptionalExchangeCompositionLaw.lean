/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Specialization.BoundedConstructiblePushforwardExchangeComp
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingCompositionLaw

/-!

# The composition law of the exceptional exchanges along proper morphisms of models

For proper morphisms of proper trait models over a common generic base, the compact-support
exchange `ν_φ` is the inverse of the proper exchange `χ_φ`, read through `Rf_! ≅ Rf_*`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.properCompactSupportExchange`), and the exceptional
exchange `β_φ` is its mate for `Rf_! ⊣ Rf^!` (`ProEtale.CondensedRing.exceptionalExchange`).
The proper exchanges compose
(`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_comp_app_of_eq`) and the
identifications `Rf_! ≅ Rf_*` are compatible with composition
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`), so the
compact-support exchanges compose, which is the hypothesis of the conditional composition law
`ProEtale.CondensedRing.exceptionalExchange_comp_app`. This gives the composition law
`β_{gf} = f_s^! β_g ∘ β_f(g_η^!)` of blueprint `lemma-composition-exceptional-base-change-maps`
(E.9) for proper morphisms of models.

## Main results

- `ProEtale.CondensedRing.invExchange_comp_app`: the inverse exchanges of composable invertible
  exchanges compose, in an abstract setting.
- `IsTraitModelOfGenericBase.properCompactSupportExchange_comp_app` (in
  `ProEtale.CondensedRing.NearbyCyclesModel`):
  the compact-support exchanges of proper morphisms of models compose.
- `IsTraitModelOfGenericBase.exceptionalExchange_properCompactSupportExchange_comp_app` (in
  `ProEtale.CondensedRing.NearbyCyclesModel`):
  the composition law of the exceptional exchanges.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {A B C A' B' C' : Type*} [Category* A] [Category* B] [Category* C] [Category* A']
  [Category* B'] [Category* C'] {ΨA : A ⥤ A'} {ΨB : B ⥤ B'} {ΨC : C ⥤ C'}
  {Sd Rd : A ⥤ B} {Sa Ra : B ⥤ C} {Sda Rda : A ⥤ C}
  {Sd' Rd' : A' ⥤ B'} {Sa' Ra' : B' ⥤ C'} {Sda' Rda' : A' ⥤ C'}

/-- **Composition of inverse exchanges**: let `χ_d`, `χ_a`, `χ_{da}` be invertible exchanges
`R ⋙ Ψ ⟶ Ψ ⋙ R'` satisfying the composition law under isomorphisms `cR : Rd ⋙ Ra ≅ Rda`, and let
`S ≅ R` be identifications compatible with composition isomorphisms `cS : Sda ≅ Sd ⋙ Sa`. Then
the inverse exchanges `ν = invExchange` satisfy the composition law under `cS`. -/
lemma invExchange_comp_app (id : Sd ≅ Rd) (ia : Sa ≅ Ra) (ida : Sda ≅ Rda) (id' : Sd' ≅ Rd')
    (ia' : Sa' ≅ Ra') (ida' : Sda' ≅ Rda') (cS : Sda ≅ Sd ⋙ Sa) (cS' : Sda' ≅ Sd' ⋙ Sa')
    (cR : Rd ⋙ Ra ≅ Rda) (cR' : Rd' ⋙ Ra' ≅ Rda')
    (χd : Rd ⋙ ΨB ⟶ ΨA ⋙ Rd') (χa : Ra ⋙ ΨC ⟶ ΨB ⋙ Ra') (χda : Rda ⋙ ΨC ⟶ ΨA ⋙ Rda')
    [IsIso χd] [IsIso χa] [IsIso χda]
    (hχ : ∀ K, χda.app K ≫ cR'.inv.app (ΨA.obj K) =
      ΨC.map (cR.inv.app K) ≫ χa.app (Rd.obj K) ≫ Ra'.map (χd.app K))
    (hc : ∀ K, cS.hom.app K ≫ ia.hom.app (Sd.obj K) ≫ Ra.map (id.hom.app K) =
      ida.hom.app K ≫ cR.inv.app K)
    (hc' : ∀ K, cS'.hom.app K ≫ ia'.hom.app (Sd'.obj K) ≫ Ra'.map (id'.hom.app K) =
      ida'.hom.app K ≫ cR'.inv.app K) (K : A) :
    (invExchange ida ida' χda).app K ≫ ΨC.map (cS.hom.app K) =
      cS'.hom.app (ΨA.obj K) ≫ Sa'.map ((invExchange id id' χd).app K) ≫
        (invExchange ia ia' χa).app (Sd.obj K) := by
  have hinv {F G : A ⥤ C'} (τ : F ⟶ G) [IsIso τ] (X : A) : (inv τ).app X = inv (τ.app X) :=
    NatIso.isIso_inv_app τ X
  have hinv' {F G : B ⥤ C'} (τ : F ⟶ G) [IsIso τ] (X : B) : (inv τ).app X = inv (τ.app X) :=
    NatIso.isIso_inv_app τ X
  have hinv'' {F G : A ⥤ B'} (τ : F ⟶ G) [IsIso τ] (X : A) : (inv τ).app X = inv (τ.app X) :=
    NatIso.isIso_inv_app τ X
  have key : inv (χda.app K) ≫ ΨC.map (cR.inv.app K) =
      cR'.inv.app (ΨA.obj K) ≫ Ra'.map (inv (χd.app K)) ≫ inv (χa.app (Rd.obj K)) := by
    rw [IsIso.inv_comp_eq, reassoc_of% (hχ K)]
    simp
  have hS : cS.hom.app K = ida.hom.app K ≫ cR.inv.app K ≫ Ra.map (id.inv.app K) ≫
      ia.inv.app (Sd.obj K) := by
    rw [← reassoc_of% (hc K)]
    simp
  have hS' : cS'.hom.app (ΨA.obj K) ≫ ia'.hom.app (Sd'.obj (ΨA.obj K)) =
      ida'.hom.app (ΨA.obj K) ≫ cR'.inv.app (ΨA.obj K) ≫
        Ra'.map (id'.inv.app (ΨA.obj K)) := by
    rw [← reassoc_of% (hc' (ΨA.obj K))]
    simp [← Functor.map_comp]
  have hχa := (inv χa).naturality (id.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hχa
  simp only [invExchange, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hinv, hinv', hinv'', Category.assoc, Functor.map_comp]
  have nat := ia'.hom.naturality
    (id'.hom.app (ΨA.obj K) ≫ inv (χd.app K) ≫ ΨB.map (id.inv.app K))
  simp only [Functor.map_comp, Category.assoc] at nat
  rw [reassoc_of% nat, reassoc_of% hS', ← Ra'.map_comp_assoc, Iso.inv_hom_id_app, Ra'.map_id,
    Category.id_comp, hS]
  simp only [hinv', Functor.map_comp, ← Functor.map_comp_assoc ΨC,
    Iso.inv_hom_id_app] at hχa ⊢
  simp only [Category.assoc]
  erw [ΨC.map_id, Category.id_comp]
  rw [reassoc_of% hχa, reassoc_of% key]

end Abstract
open Scheme

namespace NearbyCyclesModel.IsTraitModelOfGenericBase

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {W₁ Y₁ X₁ : Over (Spec (.of F))} [LocallyOfFiniteType W₁.hom] [QuasiCompact W₁.hom]
  [IsSeparated W₁.hom] [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  {W' Y' X' : Over (Spec (.of k'))} [LocallyOfFiniteType W'.hom] [QuasiCompact W'.hom]
  [IsSeparated W'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {L : NearbyCyclesModel W₁.left W'.left} {qL : L.total ⟶ trait k'}
  {gL : L.generic ⟶ Spec (.of (traitGenericField k'))}
  {N : NearbyCyclesModel Y₁.left Y'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hL : L.IsTraitModelOfGenericBase W₁ ι qL gL) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
  (hM : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper qL] [IsProper qN]
  (hLgen : IsPullback L.ε gL W₁.hom (traitGenericPointToSpec k' ≫ ι))
  (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
  (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
  (d₁ : W₁ ⟶ Y₁) (d₂ : W' ⟶ Y') (i₁ : Y₁ ⟶ X₁) (i₂ : Y' ⟶ X') [IsProper d₁.left]
  [IsProper d₂.left] [IsProper i₁.left] [IsProper i₂.left] [IsProper (d₁ ≫ i₁).left]
  [IsProper (d₂ ≫ i₂).left]
  (φ : L.Hom N d₁.left d₂.left) (ψ : N.Hom M i₁.left i₂.left)
  (χ : L.Hom M (d₁ ≫ i₁).left (d₂ ≫ i₂).left)
  (hqφ : qL = φ.total ≫ qN) (hgφ : gL = φ.generic ≫ gN) (hqψ : qN = ψ.total ≫ q)
  (hgψ : gN = ψ.generic ≫ g) (hqχ : qL = χ.total ≫ q) (hgχ : gL = χ.generic ≫ g)
  (htot : φ.total ≫ ψ.total = χ.total) (hgen : φ.generic ≫ ψ.generic = χ.generic)

include htot hgen in
/-- **Composition of the compact-support exchanges of proper morphisms of models**: for proper
morphisms of proper trait models `φ : L ⟶ N` and `ψ : N ⟶ M` over a common generic base, with
composite `χ`, the compact-support exchanges `ν`, inverse to the proper exchanges, compose under
the composition isomorphisms of the lower shrieks. -/
theorem properCompactSupportExchange_comp_app
    (K : Dᵇc(W₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (properCompactSupportExchange ℓ hM hL hMgen hLgen (d₁ ≫ i₁) (d₂ ≫ i₂) χ hqχ hgχ).app K ≫
        (boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ d₁ i₁).hom.app K) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ d₂ i₂).hom.app
          ((boundedConstructibleNearbyCycles (hL.preservesBoundedConstructible (ℓ := ℓ))).obj K) ≫
        (boundedConstructibleLowerShriek ℓ i₂).map
          ((properCompactSupportExchange ℓ hN hL hNgen hLgen d₁ d₂ φ hqφ hgφ).app K) ≫
        (properCompactSupportExchange ℓ hM hN hMgen hNgen i₁ i₂ ψ hqψ hgψ).app
          ((boundedConstructibleLowerShriek ℓ d₁).obj K) := by
  have := isIso_boundedConstructiblePushforwardExchange ℓ hN hL hNgen hLgen d₁ d₂ φ hqφ hgφ
  have := isIso_boundedConstructiblePushforwardExchange ℓ hM hN hMgen hNgen i₁ i₂ ψ hqψ hgψ
  have := isIso_boundedConstructiblePushforwardExchange ℓ hM hL hMgen hLgen (d₁ ≫ i₁) (d₂ ≫ i₂)
    χ hqχ hgχ
  have hcomp (f : W₁ ⟶ Y₁) (f' : Y₁ ⟶ X₁) : boundedConstructibleLowerStarCompOfEq ℓ f f' rfl =
      boundedConstructibleLowerStarComp ℓ f f' := by
    simp [boundedConstructibleLowerStarCompOfEq]
  have hcomp' (f : W' ⟶ Y') (f' : Y' ⟶ X') : boundedConstructibleLowerStarCompOfEq ℓ f f' rfl =
      boundedConstructibleLowerStarComp ℓ f f' := by
    simp [boundedConstructibleLowerStarCompOfEq]
  exact invExchange_comp_app _ _ _ _ _ _ _ _ (boundedConstructibleLowerStarCompOfEq ℓ d₁ i₁ rfl)
    (boundedConstructibleLowerStarCompOfEq ℓ d₂ i₂ rfl) _ _ _
    (Hom.boundedConstructiblePushforwardExchange_comp_app_of_eq ℓ φ ψ χ rfl rfl htot hgen _ _ _)
    (fun K ↦ by
      rw [hcomp]
      exact boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ d₁ i₁ K)
    (fun K ↦ by
      rw [hcomp']
      exact boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ d₂ i₂ K) K

include htot hgen in
/-- **The composition law of the exceptional exchanges along proper morphisms of models**
(blueprint `lemma-composition-exceptional-base-change-maps` (E.9), `β_{gf} = f_s^! β_g ∘
β_f(g_η^!)`, for proper morphisms of proper trait models over a common generic base): for
`φ : L ⟶ N` and `ψ : N ⟶ M` with composite `χ`, the exceptional exchange of `χ` is the composite of
those of `φ` and `ψ` under the composition isomorphisms of the exceptional inverse images, the
exceptional exchanges being the mates of the compact-support exchanges inverse to the proper
exchanges. -/
theorem exceptionalExchange_properCompactSupportExchange_comp_app
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ (d₁ ≫ i₁) (d₂ ≫ i₂)
          (properCompactSupportExchange ℓ hM hL hMgen hLgen (d₁ ≫ i₁) (d₂ ≫ i₂) χ hqχ hgχ)).app
          K ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ d₂ i₂).hom.app
          ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj K) =
      (boundedConstructibleNearbyCycles (hL.preservesBoundedConstructible (ℓ := ℓ))).map
          ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ d₁ i₁).hom.app K) ≫
        (exceptionalExchange ℓ d₁ d₂
            (properCompactSupportExchange ℓ hN hL hNgen hLgen d₁ d₂ φ hqφ hgφ)).app
          ((boundedConstructibleUpperShriek ℓ i₁).obj K) ≫
        (boundedConstructibleUpperShriek ℓ d₂).map
          ((exceptionalExchange ℓ i₁ i₂
            (properCompactSupportExchange ℓ hM hN hMgen hNgen i₁ i₂ ψ hqψ hgψ)).app K) :=
  exceptionalExchange_comp_app ℓ d₁ i₁ d₂ i₂ _ _ _
    (properCompactSupportExchange_comp_app ℓ hL hN hM hLgen hNgen hMgen d₁ d₂ i₁ i₂ φ ψ χ hqφ
      hgφ hqψ hgψ hqχ hgχ htot hgen) K

end NearbyCyclesModel.IsTraitModelOfGenericBase

end AlgebraicGeometry.ProEtale.CondensedRing
