/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionComp
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# Retractions of the pullback exchange of a composite of morphisms of models

Let `χ : M'' ⟶ M` be the composite of morphisms of models `ρ : M'' ⟶ M₁` and `ψ : M₁ ⟶ M` over
`𝟙 X`. If the pullback exchange of `ψ` is invertible and that of `ρ` is a split
monomorphism whose idempotent, times `n`, is a sum of natural endomorphisms of the nearby cycles
of `M''` (the inclusion of the invariants of a finite group), then so is the pullback exchange of
`χ` (`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp`). This is the formal part of
the generic-slicing identification of nearby cycles with invariants (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Facts about traits", identification (2)).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-- The diagram chase behind
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`, for abstract
functors: the pullback exchange `αχ` of a composite `ρ ≫ ψ` of morphisms of models over `𝟙 X`
(`hx`, the composition law) is split by `c₀ ≫ r ≫ (Lf αψ)⁻¹ ≫ c₁⁻¹` if `αψ` is invertible and
`αρ` is split by `r`, with idempotent the conjugate of that of `αρ` by `c₀`. -/
private lemma retraction_of_comp_aux {DX DM DT DS : Type*} [Category DX] [Category DM]
    [Category DT] [Category DS] {L₀ : DX ⥤ DX} {Lfg : DM ⥤ DS} {Lg : DM ⥤ DT} {Lf : DT ⥤ DS}
    {ΨM : DX ⥤ DM} {Ψ₁ : DX ⥤ DT} {Ψ : DX ⥤ DS}
    (αχ : ΨM ⋙ Lfg ⟶ L₀ ⋙ Ψ) (αψ : ΨM ⋙ Lg ⟶ L₀ ⋙ Ψ₁) (αρ : Ψ₁ ⋙ Lf ⟶ L₀ ⋙ Ψ)
    (c₀ : L₀ ≅ L₀ ⋙ L₀) (c₁ : Lfg ≅ Lg ⋙ Lf) (A : DX)
    (hx : αχ.app A ≫ Ψ.map (c₀.hom.app A) =
      c₁.hom.app (ΨM.obj A) ≫ Lf.map (αψ.app A) ≫ αρ.app (L₀.obj A))
    (ψinv : (L₀ ⋙ Ψ₁).obj A ⟶ (ΨM ⋙ Lg).obj A) (hψ₁ : αψ.app A ≫ ψinv = 𝟙 _)
    (hψ₂ : ψinv ≫ αψ.app A = 𝟙 _)
    (r : (L₀ ⋙ Ψ).obj (L₀.obj A) ⟶ (Ψ₁ ⋙ Lf).obj (L₀.obj A))
    (hr : αρ.app (L₀.obj A) ≫ r = 𝟙 _) :
    αχ.app A ≫ Ψ.map (c₀.hom.app A) ≫ r ≫ Lf.map ψinv ≫ c₁.inv.app (ΨM.obj A) =
      𝟙 _ ∧
    (Ψ.map (c₀.hom.app A) ≫ r ≫ Lf.map ψinv ≫ c₁.inv.app (ΨM.obj A)) ≫ αχ.app A =
      Ψ.map (c₀.hom.app A) ≫ (r ≫ αρ.app (L₀.obj A)) ≫ Ψ.map (c₀.inv.app A) := by
  have hχ : αχ.app A = c₁.hom.app (ΨM.obj A) ≫ Lf.map (αψ.app A) ≫ αρ.app (L₀.obj A) ≫
      Ψ.map (c₀.inv.app A) := by
    rw [← reassoc_of% hx, ← Ψ.map_comp, Iso.hom_inv_id_app, Ψ.map_id, Category.comp_id]
  have k₁ : Ψ.map (c₀.inv.app A) ≫ Ψ.map (c₀.hom.app A) = 𝟙 _ := by
    rw [← Ψ.map_comp, Iso.inv_hom_id_app]
    exact Ψ.map_id _
  have k₂ : Lf.map (αψ.app A) ≫ Lf.map ψinv = 𝟙 _ := by
    rw [← Lf.map_comp, hψ₁, Lf.map_id]
  have k₃ : Lf.map ψinv ≫ Lf.map (αψ.app A) = 𝟙 _ := by
    rw [← Lf.map_comp, hψ₂, Lf.map_id]
  constructor
  · rw [hχ]
    simp only [Category.assoc, reassoc_of% k₁, reassoc_of% hr, reassoc_of% k₂,
      Iso.hom_inv_id_app]
    rfl
  · rw [hχ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, reassoc_of% k₃]

/-- A natural endomorphism `act` of `Ψ` is conjugate to itself along `Ψ(c)` for an isomorphism
`c : C ≅ C'`. -/
private lemma conj_eq_of_naturality_aux {DX DS : Type*} [Category DX] [Category DS] {Ψ : DX ⥤ DS}
    (act : ∀ C, Ψ.obj C ⟶ Ψ.obj C)
    (hact : ∀ {C C' : DX} (g : C ⟶ C'), act C ≫ Ψ.map g = Ψ.map g ≫ act C') {C C' : DX}
    (c : C ≅ C') : Ψ.map c.hom ≫ act C' ≫ Ψ.map c.inv = act C := by
  rw [← reassoc_of% (hact c.hom), ← Ψ.map_comp, Iso.hom_inv_id, Ψ.map_id, Category.comp_id]

/-- Conjugating an identity `n • e = ∑ i, f i` by `c`, `c'`. -/
private lemma nsmul_conj_aux {D : Type*} [Category D] [Preadditive D] {X Y : D} (c : X ⟶ Y)
    (c' : Y ⟶ X) (e : Y ⟶ Y) (n : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → (Y ⟶ Y)) (g : ι → (X ⟶ X)) (he : n • e = ∑ i ∈ s, f i)
    (hg : ∀ i, c ≫ f i ≫ c' = g i) : n • (c ≫ e ≫ c') = ∑ i ∈ s, g i := by
  rw [← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, he, Preadditive.sum_comp,
    Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hg i

/-- Triviality of a natural endomorphism `act` of `Ψ` transfers along an isomorphism
`c : L₀ A ≅ L₀ (L₀ A)`. -/
lemma eq_id_of_naturality_of_iso {DX DS : Type*} [Category DX] [Category DS] {Ψ : DX ⥤ DS}
    (act : ∀ C, Ψ.obj C ⟶ Ψ.obj C)
    (hact : ∀ {C C' : DX} (g : C ⟶ C'), act C ≫ Ψ.map g = Ψ.map g ≫ act C') {C C' : DX}
    (c : C ≅ C') (h : act C' = 𝟙 _) : act C = 𝟙 _ := by
  rw [← cancel_mono (Ψ.map c.hom), hact, h, Category.comp_id, Category.id_comp]


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

-- the exchanges of the three models are large terms
/-- **Exchanges of a composite and inclusions of invariants**: let `χ : M'' ⟶ M` be the composite
of `ρ : M'' ⟶ M₁` and `ψ : M₁ ⟶ M`, both over `𝟙 X`. If the pullback exchange of
`ψ` at `A` is invertible and that of `ρ` at `L(𝟙)^* A` is split with `n` times its idempotent a
sum of natural endomorphisms `act i` of `Ψ_{M''}`, then so is the pullback exchange of `χ` at
`A`. -/
lemma exists_retraction_pullbackExchange_of_comp {X X'' X₁ X' : Scheme.{u}}
    {M'' : NearbyCyclesModel X X''} {M₁ : NearbyCyclesModel X X₁} {M : NearbyCyclesModel X X'}
    {g'' : X'' ⟶ X₁} {g' : X₁ ⟶ X'} {gχ : X'' ⟶ X'} (ρ : M''.Hom M₁ (𝟙 X) g'')
    (ψ : M₁.Hom M (𝟙 X) g') (χ : M''.Hom M (𝟙 X) gχ) (hspec : g'' ≫ g' = gχ)
    (htot : ρ.total ≫ ψ.total = χ.total) (hgen : ρ.generic ≫ ψ.generic = χ.generic)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hψ : IsIso ((ψ.pullbackExchange Λ).app A)) {ι : Type*} (s : Finset ι) (n : ℕ)
    (act : ι → ∀ C, (M''.nearbyCycles Λ).obj C ⟶ (M''.nearbyCycles Λ).obj C)
    (hact : ∀ i {C C'} (g : C ⟶ C'),
      act i C ≫ (M''.nearbyCycles Λ).map g = (M''.nearbyCycles Λ).map g ≫ act i C')
    (r : (L((𝟙 X)^*⟦Λ⟧) ⋙ M''.nearbyCycles Λ).obj (L((𝟙 X)^*⟦Λ⟧).obj A) ⟶
      (M₁.nearbyCycles Λ ⋙ L((g'')^*⟦Λ⟧)).obj (L((𝟙 X)^*⟦Λ⟧).obj A))
    (hr : (ρ.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj A) ≫ r = 𝟙 _)
    (havg : n • (r ≫ (ρ.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj A)) =
      ∑ i ∈ s, act i (L((𝟙 X)^*⟦Λ⟧).obj (L((𝟙 X)^*⟦Λ⟧).obj A))) :
    ∃ r', (χ.pullbackExchange Λ).app A ≫ r' = 𝟙 _ ∧
      n • (r' ≫ (χ.pullbackExchange Λ).app A) = ∑ i ∈ s, act i (L((𝟙 X)^*⟦Λ⟧).obj A) := by
  have := hψ
  have hx := ρ.pullbackExchange_comp_app_of_eq Λ ψ χ (Category.id_comp (𝟙 X))
    hspec htot hgen A
  have k := retraction_of_comp_aux (χ.pullbackExchange Λ) (ψ.pullbackExchange Λ)
    (ρ.pullbackExchange Λ) (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X)))
    (leftDerivedUpperStarCompOfEq Λ hspec) A hx (inv ((ψ.pullbackExchange Λ).app A))
    (IsIso.hom_inv_id _) (IsIso.inv_hom_id _) r hr
  refine ⟨_, k.1, ?_⟩
  refine (congrArg (n • ·) k.2).trans ?_
  exact nsmul_conj_aux
    ((M''.nearbyCycles Λ).map
      ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X))).hom.app A))
    ((M''.nearbyCycles Λ).map
      ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X))).inv.app A))
    (r ≫ (ρ.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj A)) n s _ _ havg
    fun i ↦ conj_eq_of_naturality_aux _ (hact i)
    ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X))).app A)


end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
