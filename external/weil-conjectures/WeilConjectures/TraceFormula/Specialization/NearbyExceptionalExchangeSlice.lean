/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersionGenericBase
public import WeilConjectures.TraceFormula.Specialization.BoundedConstructiblePushforwardExchangeComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.Tactic.TransportExact

/-!

# The exchanges of a morphism of models and slicing

Let `φ : N ⟶ M` be a morphism of models over `i₁ : Y₁ ⟶ X₁` and `i₂ : Y' ⟶ X'`, and let
`φ'' : N'' ⟶ M''` be a morphism of models over `i₁'' : Y₂ ⟶ X₂` and `i₂'' : Y'' ⟶ X''` which is
compatible with morphisms of models `s_M : M'' ⟶ M` (over `c_M`, `p_M`) and `s_N : N'' ⟶ N`
(over `c_N`, `p_N`), that is `s_N ≫ φ = φ'' ≫ s_M` (e.g. the generic slices of `M` and `N`
along compatible coordinates, `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom`).
Write `α_M : p_M^* Ψ_M ⟶ Ψ_{M''} c_M^*` and `α_N` for the pullback exchanges of `s_M` and `s_N`
(the slice exchanges, `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange`).

This file proves that the exchanges of `φ` and of `φ''` are compatible with `α_M` and `α_N`
(blueprint `lemma-nearby-duality-slice--1`, "the map `θ`"):

* the **pushforward exchanges** `χ_φ : Ψ_M Ri₁_* ⟶ Ri₂_* Ψ_N` and `χ_{φ''}`, through the base
  change morphisms of `Ri₁_*` and `Ri₂_*`
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_slice_app`):
  ```
  p_M^* Ψ_M Ri₁_* K --p_M^* χ_φ--> p_M^* Ri₂_* Ψ_N K --bc--> Ri₂''_* p_N^* Ψ_N K
        |α_M                                                  |Ri₂''_* α_N
        v                                                     v
  Ψ_{M''} c_M^* Ri₁_* K --Ψ(bc)--> Ψ_{M''} Ri₁''_* c_N^* K --χ_{φ''}--> Ri₂''_* Ψ_{N''} c_N^* K
  ```
* for proper `i₁, i₂, i₁'', i₂''`, cartesian squares of bases and of special fibres and invertible
  `χ_φ`, `χ_{φ''}`, the **exceptional exchanges** `β_φ : Ψ_N Ri₁^! ⟶ Ri₂^! Ψ_M` and `β_{φ''}`
  (`ProEtale.CondensedRing.exceptionalExchange` of the compact-support exchanges inverse to `χ`),
  through the base change maps `γ` of the exceptional inverse images
  (`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`)
  (`NearbyCyclesModel.Hom.exceptionalExchange_slice_app`):
  ```
  p_N^* Ψ_N Ri₁^! K --p_N^* β_φ--> p_N^* Ri₂^! Ψ_M K --γ--> Ri₂''^! p_M^* Ψ_M K
        |α_N                                                  |Ri₂''^! α_M
        v                                                     v
  Ψ_{N''} c_N^* Ri₁^! K --Ψ_{N''}(γ)--> Ψ_{N''} Ri₁''^! c_M^* K --β_{φ''}--> Ri₂''^! Ψ_{M''} c_M^* K
  ```

## Proofs

Both squares are cubes of mates (`CategoryTheory.mateEquiv_app_cube`). For the pushforward
exchanges the cube of left adjoints is the square law of the pullback exchanges for the two
factorizations `s_N ≫ φ = φ'' ≫ s_M` (`NearbyCyclesModel.Hom.pullbackExchange_square`); the base
change morphisms are the mates of the pullback comparisons
(`CategoryTheory.Adjunction.exchangeRight_eq_mateEquiv`). For the exceptional exchanges the
adjunctions are `Ri_* ⊣ Ri^!`, the exceptional exchanges are the mates of `χ⁻¹`
(`CategoryTheory.mateEquiv_ofNatIsoLeft_ofNatIsoLeft_app`), the maps `γ` the mates of the inverse
proper base change morphisms, and the cube of left adjoints is the pushforward square inverted.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section Abstract

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- The mate for two adjunctions transported along isomorphisms of left adjoints `e₁ : L₁ ≅ L₁'`,
`e₂ : L₂ ≅ L₂'` is the mate of the square conjugated by `e₁` and `e₂`. -/
lemma mateEquiv_ofNatIsoLeft_ofNatIsoLeft_app {G : A ⥤ C} {H : B ⥤ D} {L₁ L₁' : A ⥤ B}
    {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (α : G ⋙ L₂' ⟶ L₁' ⋙ H)
    (ν : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hν : ∀ X, ν.app X = e₂.hom.app (G.obj X) ≫ α.app X ≫ H.map (e₁.inv.app X)) (X : B) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α).app X =
      (mateEquiv adj₁ adj₂ ν).app X := by
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit, hν]

/-- Inverting the morphisms of a commutative square of composites. -/
lemma comp_inv_comp_inv_eq_of_comp {a b c d e f : C} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d)
    (u : a ⟶ e) (v : e ⟶ f) (w : f ⟶ d) [IsIso x] [IsIso y] [IsIso v] [IsIso w]
    (h : x ≫ y ≫ z = u ≫ v ≫ w) :
    z ≫ inv w ≫ inv v = inv y ≫ inv x ≫ u := by
  rw [← cancel_epi (x ≫ y)]
  simp only [Category.assoc, reassoc_of% h, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
    Category.comp_id]

end Abstract

section Cube

variable {DY DX DY' DX' EY EX EY' EX' : Type*} [Category* DY] [Category* DX] [Category* DY']
  [Category* DX'] [Category* EY] [Category* EX] [Category* EY'] [Category* EX']
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
  {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
  {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}

/-- `CategoryTheory.mateEquiv_app_cube` with the four mates as variables characterized by their
definitions, so that it can be instantiated without unfolding them. -/
lemma mateEquiv_app_cube_of_eq (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf)
    (bf' : Mf' ⊣ Sf') (σr : Gr ⋙ Lf' ⟶ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ⟶ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ⟶ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ⟶ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ⟶ Gr ⋙ PY') (αg' : PX ⋙ Hs ⟶ Hr ⋙ PX')
    (h : ∀ M, Mf'.map (αg.app M) ≫ αf'.app (Gr.obj M) ≫ PX'.map (σr.app M) =
      σs.app (PY.obj M) ≫ Hs.map (αf.app M) ≫ αg'.app (Lf.obj M))
    (βr : Rf ⋙ Gr ⟶ Hr ⋙ Rf') (hβr : βr = (mateEquiv af af' σr))
    (βs : Sf ⋙ Gs ⟶ Hs ⋙ Sf') (hβs : βs = (mateEquiv bf bf' σs))
    (χ : Rf ⋙ PY ⟶ PX ⋙ Sf) (hχ : χ = (mateEquiv af bf αf))
    (χ' : Rf' ⋙ PY' ⟶ PX' ⋙ Sf') (hχ' : χ' = (mateEquiv af' bf' αf')) (K : DX) :
    αg.app (Rf.obj K) ≫ PY'.map (βr.app K) ≫ χ'.app (Hr.obj K) =
      Gs.map (χ.app K) ≫ βs.app (PX.obj K) ≫ Sf'.map (αg'.app K) := by
  subst hβr hβs hχ hχ'
  exact mateEquiv_app_cube af af' bf bf' σr σs αf αf' αg αg' h K


/-- The square of the pushforward exchanges and slicing with the invertible exchanges and base
change morphisms inverted: the cube of left adjoints for the exceptional exchanges. -/
lemma inv_square_app_of_square {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'} {Mf : EY ⥤ EX}
    {Mf' : EY' ⥤ EX'} (bc₁ : Lf ⋙ Hr ⟶ Gr ⋙ Lf') (bc₂ : Mf ⋙ Hs ⟶ Gs ⋙ Mf')
    (χ : Lf ⋙ PX ⟶ PY ⋙ Mf) (χ' : Lf' ⋙ PX' ⟶ PY' ⋙ Mf') [IsIso bc₁] [IsIso bc₂] [IsIso χ]
    [IsIso χ'] (αg : PY ⋙ Gs ⟶ Gr ⋙ PY') (αg' : PX ⋙ Hs ⟶ Hr ⋙ PX')
    (h : ∀ L, Hs.map (χ.app L) ≫ bc₂.app (PY.obj L) ≫ Mf'.map (αg.app L) =
      αg'.app (Lf.obj L) ≫ PX'.map (bc₁.app L) ≫ χ'.app (Gr.obj L)) (L : DY) :
    Mf'.map (αg.app L) ≫ (inv χ').app (Gr.obj L) ≫ PX'.map ((inv bc₁).app L) =
      (inv bc₂).app (PY.obj L) ≫ Hs.map ((inv χ).app L) ≫ αg'.app (Lf.obj L) := by
  simp only [NatIso.isIso_inv_app, Functor.map_inv]
  exact comp_inv_comp_inv_eq_of_comp _ _ _ _ _ _ (h L)

end Cube

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### The pushforward exchanges and slicing, on the ambient derived categories -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ Y₁ X' Y' X₂ Y₂ X'' Y'' : Scheme.{u}}
  {M : NearbyCyclesModel X₁ X'} {N : NearbyCyclesModel Y₁ Y'}
  {M'' : NearbyCyclesModel X₂ X''} {N'' : NearbyCyclesModel Y₂ Y''}
  {i₁ : Y₁ ⟶ X₁} {i₂ : Y' ⟶ X'} {i₁'' : Y₂ ⟶ X₂} {i₂'' : Y'' ⟶ X''}
  {cM : X₂ ⟶ X₁} {pM : X'' ⟶ X'} {cN : Y₂ ⟶ Y₁} {pN : Y'' ⟶ Y'}

/-- **The pushforward exchanges and slicing**, on the ambient derived categories: for morphisms
of models `φ : N ⟶ M`, `φ'' : N'' ⟶ M''`, `s_M : M'' ⟶ M` and `s_N : N'' ⟶ N` with
`s_N ≫ φ = φ'' ≫ s_M`,
`Ri₂''_*(α_N) ∘ bc ∘ Lp_M^*(χ_φ) = χ_{φ''} ∘ Ψ_{M''}(bc) ∘ α_M`. -/
lemma Hom.pushforwardExchange_slice_app (φ : N.Hom M i₁ i₂) (φ'' : N''.Hom M'' i₁'' i₂'')
    (sM : M''.Hom M cM pM) (sN : N''.Hom N cN pN)
    (htot : sN.total ≫ φ.total = φ''.total ≫ sM.total)
    (hgen : sN.generic ≫ φ.generic = φ''.generic ≫ sM.generic)
    (hb : cN ≫ i₁ = i₁'' ≫ cM) (hs : pN ≫ i₂ = i₂'' ≫ pM)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y₁) Ab.{u + 1})
      (condensedRingObj Λ Y₁))) :
    L((pM)^*⟦Λ⟧).map ((φ.pushforwardExchange Λ).app K) ≫
        (baseChangeMap Λ (⟨hs⟩ : CommSq pN i₂'' i₂ pM)).app ((N.nearbyCycles Λ).obj K) ≫
        R((i₂'')_*⟦Λ⟧).map ((sN.pullbackExchange Λ).app K) =
      (sM.pullbackExchange Λ).app (R((i₁)_*⟦Λ⟧).obj K) ≫
        (M''.nearbyCycles Λ).map ((baseChangeMap Λ (⟨hb⟩ : CommSq cN i₁'' i₁ cM)).app K) ≫
        (φ''.pushforwardExchange Λ).app (L((cN)^*⟦Λ⟧).obj K) := by
  have hsq := fun C ↦ (sN.pullbackExchange_square Λ φ φ'' sM htot hgen hb hs C).symm
  have hr : baseChangeMap Λ (⟨hb⟩ : CommSq cN i₁'' i₁ cM) =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ i₁)
        (derivedUpperStarLowerStarAdjunction Λ i₁'')
        (pullbackSquareComparison Λ (⟨hb⟩ : CommSq cN i₁'' i₁ cM)).hom) :=
    Adjunction.exchangeRight_eq_mateEquiv _ _ _
  have hs' : baseChangeMap Λ (⟨hs⟩ : CommSq pN i₂'' i₂ pM) =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ i₂)
        (derivedUpperStarLowerStarAdjunction Λ i₂'')
        (pullbackSquareComparison Λ (⟨hs⟩ : CommSq pN i₂'' i₂ pM)).hom) :=
    Adjunction.exchangeRight_eq_mateEquiv _ _ _
  have h := mateEquiv_app_cube_of_eq (derivedUpperStarLowerStarAdjunction Λ i₁)
    (derivedUpperStarLowerStarAdjunction Λ i₁'') (derivedUpperStarLowerStarAdjunction Λ i₂)
    (derivedUpperStarLowerStarAdjunction Λ i₂'')
    (pullbackSquareComparison Λ (⟨hb⟩ : CommSq cN i₁'' i₁ cM)).hom
    (pullbackSquareComparison Λ (⟨hs⟩ : CommSq pN i₂'' i₂ pM)).hom
    (φ.pullbackExchange Λ) (φ''.pullbackExchange Λ) (sM.pullbackExchange Λ)
    (sN.pullbackExchange Λ) hsq _ hr _ hs' (φ.pushforwardExchange Λ) rfl
    (φ''.pushforwardExchange Λ) rfl K
  exact h.symm

end Ambient

/-! ### The pushforward exchanges and slicing, on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₁' k₂ k₂' : Type u} [Field k₁] [Field k₁'] [Field k₂]
  [Field k₂'] [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₁').Prime]
  [Fact (ringChar k₁' ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  [Fact (ringChar k₂').Prime] [Fact (ringChar k₂' ≠ ℓ)]
  {X₁ Y₁ : Over (Spec (.of k₁))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  {X' Y' : Over (Spec (.of k₁'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {X₂ Y₂ : Over (Spec (.of k₂))} [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom]
  [IsSeparated X₂.hom] [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  {X'' Y'' : Over (Spec (.of k₂'))} [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom]
  [IsSeparated X''.hom] [LocallyOfFiniteType Y''.hom] [QuasiCompact Y''.hom]
  [IsSeparated Y''.hom]
  {M : NearbyCyclesModel X₁.left X'.left} {N : NearbyCyclesModel Y₁.left Y'.left}
  {M'' : NearbyCyclesModel X₂.left X''.left} {N'' : NearbyCyclesModel Y₂.left Y''.left}
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hM'' : M''.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN'' : N''.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {i₁ : Y₁ ⟶ X₁} {i₂ : Y' ⟶ X'} {i₁'' : Y₂ ⟶ X₂} {i₂'' : Y'' ⟶ X''}
  {cM : X₂.left ⟶ X₁.left} {pM : X''.left ⟶ X'.left} {cN : Y₂.left ⟶ Y₁.left}
  {pN : Y''.left ⟶ Y'.left}
  (φ : N.Hom M i₁.left i₂.left) (φ'' : N''.Hom M'' i₁''.left i₂''.left)
  (sM : M''.Hom M cM pM) (sN : N''.Hom N cN pN)
  (htot : sN.total ≫ φ.total = φ''.total ≫ sM.total)
  (hgen : sN.generic ≫ φ.generic = φ''.generic ≫ sM.generic)
  (αM : boundedConstructibleNearbyCycles hM ⋙
      boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') pM ⟶
    boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := X₂) cM ⋙
      boundedConstructibleNearbyCycles hM'')
  (hαM : ∀ K, (αM.app K).hom = (sM.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj)
  (αN : boundedConstructibleNearbyCycles hN ⋙
      boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := Y'') pN ⟶
    boundedConstructibleUpperStarOfMap ℓ (X := Y₁) (Y := Y₂) cN ⋙
      boundedConstructibleNearbyCycles hN'')
  (hαN : ∀ K, (αN.app K).hom = (sN.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj)

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

include hαM hαN in
/-- `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_slice_app` for arbitrary ambient
base change morphisms `bc₁`, `bc₂` satisfying the ambient identity, restricted to bounded
constructible complexes by `NearbyCyclesModel.liftExchange`: kept abstract, so that elaboration
never unfolds the base change morphisms. -/
private lemma boundedConstructiblePushforwardExchange_slice_app_aux
    (bc₁ : R((i₁.left)_*⟦𝐐⟧) ⋙ L((cM)^*⟦𝐐⟧) ⟶ L((cN)^*⟦𝐐⟧) ⋙ R((i₁''.left)_*⟦𝐐⟧))
    (bc₂ : R((i₂.left)_*⟦𝐐⟧) ⋙ L((pM)^*⟦𝐐⟧) ⟶ L((pN)^*⟦𝐐⟧) ⋙ R((i₂''.left)_*⟦𝐐⟧))
    (key : ∀ K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y₁.left) Ab.{u + 1})
        (condensedRingObj 𝐐 Y₁.left)),
      L((pM)^*⟦𝐐⟧).map ((φ.pushforwardExchange 𝐐).app K₀) ≫
        bc₂.app ((N.nearbyCycles 𝐐).obj K₀) ≫
        R((i₂''.left)_*⟦𝐐⟧).map ((sN.pullbackExchange 𝐐).app K₀) =
      (sM.pullbackExchange 𝐐).app (R((i₁.left)_*⟦𝐐⟧).obj K₀) ≫
        (M''.nearbyCycles 𝐐).map (bc₁.app K₀) ≫
        (φ''.pushforwardExchange 𝐐).app (L((cN)^*⟦𝐐⟧).obj K₀))
    (K : Dᵇc(Y₁.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') pM).map
        ((φ.boundedConstructiblePushforwardExchange ℓ hN hM).app K) ≫
        (NearbyCyclesModel.liftExchange bc₂
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ i₂ K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ i₂'' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ pM K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ pN K.obj K.property) :
            boundedConstructibleLowerStar ℓ i₂ ⋙
                boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') pM ⟶
              boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := Y'') pN ⋙
                boundedConstructibleLowerStar ℓ i₂'').app
          ((boundedConstructibleNearbyCycles hN).obj K) ≫
        (boundedConstructibleLowerStar ℓ i₂'').map (αN.app K) =
      αM.app ((boundedConstructibleLowerStar ℓ i₁).obj K) ≫
        (boundedConstructibleNearbyCycles hM'').map
          ((NearbyCyclesModel.liftExchange bc₁
            (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ i₁ K)
            (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ i₁'' K)
            (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ cM K.obj K.property)
            (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ cN K.obj
              K.property) :
              boundedConstructibleLowerStar ℓ i₁ ⋙
                  boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := X₂) cM ⟶
                boundedConstructibleUpperStarOfMap ℓ (X := Y₁) (Y := Y₂) cN ⋙
                  boundedConstructibleLowerStar ℓ i₁'').app K) ≫
        (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'').app
          ((boundedConstructibleUpperStarOfMap ℓ (X := Y₁) (Y := Y₂) cN).obj K) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarOfMap_map,
    ObjectProperty.homMk_hom, Hom.boundedConstructiblePushforwardExchange_app_hom,
    liftExchange_app_hom, boundedConstructibleLowerStar_map_hom,
    boundedConstructibleNearbyCycles_map_hom, hαM, hαN]
  transport_exact key K.obj

include htot hgen hαM hαN in
/-- **The pushforward exchanges and slicing** (blueprint `lemma-nearby-duality-slice--1`, "the map
`θ`"): for morphisms of models `φ : N ⟶ M`, `φ'' : N'' ⟶ M''`, `s_M : M'' ⟶ M` and
`s_N : N'' ⟶ N` with `s_N ≫ φ = φ'' ≫ s_M`, and the pullback exchanges `α_M`, `α_N` of `s_M`,
`s_N` on bounded constructible complexes,
`Ri₂''_*(α_N) ∘ bc ∘ p_M^*(χ_φ) = χ_{φ''} ∘ Ψ_{M''}(bc) ∘ α_M`, where `bc` are the base change
morphisms of `Ri₂_*` along `p_M` and of `Ri₁_*` along `c_M`. -/
theorem Hom.boundedConstructiblePushforwardExchange_slice_app
    (hb : CommSq cN i₁''.left i₁.left cM) (hs : CommSq pN i₂''.left i₂.left pM)
    (K : Dᵇc(Y₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') pM).map
        ((φ.boundedConstructiblePushforwardExchange ℓ hN hM).app K) ≫
        (boundedConstructibleBaseChangeOfMap ℓ hs).app
          ((boundedConstructibleNearbyCycles hN).obj K) ≫
        (boundedConstructibleLowerStar ℓ i₂'').map (αN.app K) =
      αM.app ((boundedConstructibleLowerStar ℓ i₁).obj K) ≫
        (boundedConstructibleNearbyCycles hM'').map
          ((boundedConstructibleBaseChangeOfMap ℓ hb).app K) ≫
        (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'').app
          ((boundedConstructibleUpperStarOfMap ℓ (X := Y₁) (Y := Y₂) cN).obj K) := by
  have key := boundedConstructiblePushforwardExchange_slice_app_aux ℓ hM hN hM'' hN'' φ φ'' sM
    sN αM hαM αN hαN (baseChangeMap _ hb) (baseChangeMap _ hs)
    (fun K₀ ↦ by
      cast_proofs Hom.pushforwardExchange_slice_app _ φ φ'' sM sN htot hgen hb.w hs.w K₀) K
  unfold boundedConstructibleBaseChangeOfMap
  cast_proofs key

include htot hgen hαM hαN in
/-- The square of `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_slice_app` with
the invertible proper exchanges and base change morphisms inverted. -/
lemma Hom.boundedConstructiblePushforwardExchange_slice_inv_app
    (hb : CommSq cN i₁''.left i₁.left cM) (hs : CommSq pN i₂''.left i₂.left pM)
    [IsIso (boundedConstructibleBaseChangeOfMap ℓ hb)]
    [IsIso (boundedConstructibleBaseChangeOfMap ℓ hs)]
    [IsIso (φ.boundedConstructiblePushforwardExchange ℓ hN hM)]
    [IsIso (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'')]
    (L : Dᵇc(Y₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ i₂'').map (αN.app L) ≫
      (inv (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'')).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := Y₁) (Y := Y₂) cN).obj L) ≫
      (boundedConstructibleNearbyCycles hM'').map
        ((inv (boundedConstructibleBaseChangeOfMap ℓ hb)).app L) =
      (inv (boundedConstructibleBaseChangeOfMap ℓ hs)).app
          ((boundedConstructibleNearbyCycles hN).obj L) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') pM).map
          ((inv (φ.boundedConstructiblePushforwardExchange ℓ hN hM)).app L) ≫
        αM.app ((boundedConstructibleLowerStar ℓ i₁).obj L) := by
  have h := Hom.boundedConstructiblePushforwardExchange_slice_app ℓ hM hN hM'' hN'' φ φ'' sM sN
    htot hgen αM hαM αN hαN hb hs
  exact inv_square_app_of_square (boundedConstructibleBaseChangeOfMap ℓ hb)
    (boundedConstructibleBaseChangeOfMap ℓ hs) (φ.boundedConstructiblePushforwardExchange ℓ hN hM)
    (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'') αN αM (by cast_proofs h) L

section Exceptional

variable [IsProper i₁.left] [IsProper i₂.left] [IsProper i₁''.left] [IsProper i₂''.left]

omit [IsProper i₁''.left] [IsProper i₂''.left] in
/-- The exceptional exchange `β_φ` of a compact-support exchange `ν` inverse to an invertible
proper exchange `χ_φ` (through `Ri_! ≅ Ri_*`) is the mate of `χ_φ⁻¹` under the adjunctions
`Ri_* ⊣ Ri^!`. -/
lemma exceptionalExchange_app_eq_mateEquiv_inv
    [IsIso (φ.boundedConstructiblePushforwardExchange ℓ hN hM)]
    (ν : boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerShriek ℓ i₂ ⟶
      boundedConstructibleLowerShriek ℓ i₁ ⋙ boundedConstructibleNearbyCycles hM)
    (hν : ∀ K, (φ.boundedConstructiblePushforwardExchange ℓ hN hM).app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles hN).obj K) ≫ ν.app K =
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K))
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ i₁ i₂ ν).app K =
      (mateEquiv (lowerStarUpperShriekAdjunction ℓ i₁) (lowerStarUpperShriekAdjunction ℓ i₂)
        (inv (φ.boundedConstructiblePushforwardExchange ℓ hN hM))).app K := by
  refine (mateEquiv_ofNatIsoLeft_ofNatIsoLeft_app _ _ _ _ _ ν (fun X ↦ ?_) K).symm
  rw [NatIso.isIso_inv_app,
    ← cancel_epi ((φ.boundedConstructiblePushforwardExchange ℓ hN hM).app X ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles hN).obj X)), Category.assoc, hν X]
  simp

include htot hgen hαM hαN in
/-- **The exceptional exchanges and slicing** (blueprint `lemma-nearby-duality-slice--1`, "the map
`θ`"): in the situation of
`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_slice_app`, for proper
`i₁, i₂, i₁'', i₂''`, cartesian squares of bases and of special fibres, invertible proper
exchanges `χ_φ`, `χ_{φ''}` and compact-support exchanges `ν`, `ν''` inverse to them, the
exceptional exchanges `β_φ`, `β_{φ''}` of `ν`, `ν''` satisfy
`Ri₂''^!(α_M) ∘ γ ∘ p_N^*(β_φ) = β_{φ''} ∘ Ψ_{N''}(γ) ∘ α_N`, where `γ` are the base change maps
of the exceptional inverse images `p_N^* Ri₂^! ⟶ Ri₂''^! p_M^*` and `c_N^* Ri₁^! ⟶ Ri₁''^! c_M^*`
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`). -/
theorem Hom.exceptionalExchange_slice_app
    (hb : IsPullback cN i₁''.left i₁.left cM) (hs : IsPullback pN i₂''.left i₂.left pM)
    [IsIso (φ.boundedConstructiblePushforwardExchange ℓ hN hM)]
    [IsIso (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'')]
    (ν : boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerShriek ℓ i₂ ⟶
      boundedConstructibleLowerShriek ℓ i₁ ⋙ boundedConstructibleNearbyCycles hM)
    (hν : ∀ K, (φ.boundedConstructiblePushforwardExchange ℓ hN hM).app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles hN).obj K) ≫ ν.app K =
        (boundedConstructibleNearbyCycles hM).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K))
    (ν'' : boundedConstructibleNearbyCycles hN'' ⋙ boundedConstructibleLowerShriek ℓ i₂'' ⟶
      boundedConstructibleLowerShriek ℓ i₁'' ⋙ boundedConstructibleNearbyCycles hM'')
    (hν'' : ∀ K, (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'').app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂'').inv.app
        ((boundedConstructibleNearbyCycles hN'').obj K) ≫ ν''.app K =
        (boundedConstructibleNearbyCycles hM'').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁'').inv.app K))
    (K : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := Y'') pN).map
        ((exceptionalExchange ℓ i₁ i₂ ν).app K) ≫
        (upperShriekBaseChangeOfMap ℓ hs).app ((boundedConstructibleNearbyCycles hM).obj K) ≫
        (boundedConstructibleUpperShriek ℓ i₂'').map (αM.app K) =
      αN.app ((boundedConstructibleUpperShriek ℓ i₁).obj K) ≫
        (boundedConstructibleNearbyCycles hN'').map ((upperShriekBaseChangeOfMap ℓ hb).app K) ≫
        (exceptionalExchange ℓ i₁'' i₂'' ν'').app
          ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := X₂) cM).obj K) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ hb
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ hs
  exact (mateEquiv_app_cube_of_eq (lowerStarUpperShriekAdjunction ℓ i₁)
    (lowerStarUpperShriekAdjunction ℓ i₁'') (lowerStarUpperShriekAdjunction ℓ i₂)
    (lowerStarUpperShriekAdjunction ℓ i₂'')
    (inv (boundedConstructibleBaseChangeOfMap ℓ hb.toCommSq))
    (inv (boundedConstructibleBaseChangeOfMap ℓ hs.toCommSq))
    (inv (φ.boundedConstructiblePushforwardExchange ℓ hN hM))
    (inv (φ''.boundedConstructiblePushforwardExchange ℓ hN'' hM'')) αN αM
    (Hom.boundedConstructiblePushforwardExchange_slice_inv_app ℓ hM hN hM'' hN'' φ φ'' sM sN htot
      hgen αM hαM αN hαN hb.toCommSq hs.toCommSq)
    (upperShriekBaseChangeOfMap ℓ hb)
    (NatTrans.ext (funext (upperShriekBaseChangeOfMap_app_eq ℓ hb)))
    (upperShriekBaseChangeOfMap ℓ hs)
    (NatTrans.ext (funext (upperShriekBaseChangeOfMap_app_eq ℓ hs)))
    (exceptionalExchange ℓ i₁ i₂ ν)
    (NatTrans.ext (funext (exceptionalExchange_app_eq_mateEquiv_inv ℓ hM hN φ ν hν)))
    (exceptionalExchange ℓ i₁'' i₂'' ν'')
    (NatTrans.ext (funext (exceptionalExchange_app_eq_mateEquiv_inv ℓ hM'' hN'' φ'' ν'' hν'')))
    K).symm

end Exceptional

end BoundedConstructible

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
