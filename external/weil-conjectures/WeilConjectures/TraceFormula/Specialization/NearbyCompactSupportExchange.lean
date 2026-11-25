/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeRefinement
public import WeilConjectures.TraceFormula.Specialization.OpenProperLowerShriek
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelRefinement
public import WeilConjectures.Mathlib.CategoryTheory.NatIsoInvApp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The compact-support exchange of a trait model over the base

Let `N` be a trait model over the base of a separated `k`-scheme `Y` of finite type, with special
fibre `Y'`, over the strictly henselian trait `S = Spec k'⟦t⟧`. For a compactification `C` of `N`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification`: `N ⊆ P` open in a trait model over the
base with proper total space, over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`), the compact-support exchange of
the structure morphism `a : Y ⟶ Spec k` (blueprint `prose-E-15` (3)) is
```
ν_C = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) : Ra'_! Ψ_N ⟶ Ψ_S Ra_!
```
through `Ra_! ≅ ι_! ⋙ Ra_{P*}`, with `ν_ι` the adjoint of `α_ι⁻¹`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange`, an instance of
`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).

It does not depend on the compactification: for a refinement `C₃ ⟶ C₁` it is unchanged
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq_of_refinement`),
and any two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`), so
`ν_{C₁} = ν_{C₂}`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq`) and the
compact-support exchange `ν_a` of the trait model is well defined
(`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`). This is the independence
statement of blueprint `prose-E-15`.

## The refinement identity

The independence of `ν_C` from the compactification (blueprint `prose-E-15`) is
proved along a refinement `π : P₃ ⟶ P₁` over a proper `p : X₃ ⟶ X₁` with `ι₁ = ι₃ ≫ p` and `N`
cartesian over `P₁` (any two compactifications have a common refinement,
`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`). Its key identity
```
χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rp'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}
```
for the identifications `E : ι₁! ≅ Rp_* ι₃!` (`ProEtale.CondensedRing.openProperLowerShriekIso`)
is `NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_pushforwardExchange`, from the composition
law of the pullback exchanges and the description of the adjoint of `E` as the inverse of the
extension-by-zero base change. The remaining assembly is the formal
`ProEtale.CondensedRing.compactSupportExchangeAux_lift_eq_of_refinement`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

/-- The composition isomorphism `Rp_* ⋙ Ra₁_* ≅ Ra₃_*` on bounded constructible complexes, for
`p ≫ a₁ = a₃`, is the conjugate of the composition isomorphism of the derived pullbacks. -/
lemma boundedConstructibleLowerStarCompOfEq_hom_app_hom (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u}
    [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (p : X ⟶ Y) (a₁ : Y ⟶ Z) (a₃ : X ⟶ Z) (wa : p ≫ a₁ = a₃)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerStarCompOfEq ℓ p a₁ wa).hom.app M).hom =
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction _ a₃.left)
        ((derivedUpperStarLowerStarAdjunction _ a₁.left).comp
          (derivedUpperStarLowerStarAdjunction _ p.left))
        (leftDerivedUpperStarCompOfEq _ (congrArg CommaMorphism.left wa)).symm).inv.app
          M.obj := by
  subst wa
  have h := boundedConstructibleLowerStarComp_inv_app_hom ℓ p a₁ M
  have e : (boundedConstructibleLowerStarCompOfEq ℓ p a₁ rfl).hom.app M =
      (boundedConstructibleLowerStarComp ℓ p a₁).hom.app M := by
    simp [boundedConstructibleLowerStarCompOfEq]
  rw [e]
  have h2 : ((boundedConstructibleLowerStarComp ℓ p a₁).hom.app M).hom ≫
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction _ (p ≫ a₁).left)
        ((derivedUpperStarLowerStarAdjunction _ a₁.left).comp
          (derivedUpperStarLowerStarAdjunction _ p.left))
        (leftDerivedUpperStarCompOfEq _ (Over.comp_left _ _ _ p a₁).symm).symm).hom.app M.obj =
        𝟙 ((R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
          R((a₁.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj M.obj) := by
    rw [← h, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    rfl
  exact Iso.eq_inv_app_of_comp_hom_app_eq_id
    (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction _ (p ≫ a₁).left)
      ((derivedUpperStarLowerStarAdjunction _ a₁.left).comp
        (derivedUpperStarLowerStarAdjunction _ p.left))
      (leftDerivedUpperStarCompOfEq _ (Over.comp_left _ _ _ p a₁).symm).symm) M.obj h2

section Refinement

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {Y X₃ X₁ : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  {Y' X₃' X₁' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X₃'.hom] [QuasiCompact X₃'.hom] [IsSeparated X₃'.hom]
  [LocallyOfFiniteType X₁'.hom] [QuasiCompact X₁'.hom] [IsSeparated X₁'.hom]
  {ι₃ : Y ⟶ X₃} {p : X₃ ⟶ X₁} {ι₁ : Y ⟶ X₁} [IsOpenImmersion ι₃.left] [IsProper p.left]
  [IsOpenImmersion ι₁.left] {ι₃' : Y' ⟶ X₃'} {p' : X₃' ⟶ X₁'} {ι₁' : Y' ⟶ X₁'}
  [IsOpenImmersion ι₃'.left] [IsProper p'.left] [IsOpenImmersion ι₁'.left]
  {N : NearbyCyclesModel Y.left Y'.left} {P₃ : NearbyCyclesModel X₃.left X₃'.left}
  {P₁ : NearbyCyclesModel X₁.left X₁'.left}

-- the abstract identity is instantiated on the ambient derived categories of `ℚ̄_ℓ`-modules
/-- **The key identity of the refinement step for models** (blueprint `prose-E-15`,
proof): for open immersions `φ₃ : N ⟶ P₃`, `φ₁ : N ⟶ P₁` of models and a morphism
`π : P₃ ⟶ P₁` over proper `p`, `p'` with `ι₁ = ι₃ ≫ p`, `φ₁ = φ₃ ≫ π` and `Y`, `Y'` cartesian,
the identifications `E : ι₁! ≅ ι₃! ⋙ Rp_*` (`ProEtale.CondensedRing.openProperLowerShriekIso`)
intertwine the exchanges `ν_ι` (adjoint to `α_ι⁻¹`) through the pushforward exchange `χ_π`:
`χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rp'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}`. The morphisms `E_K`,
`E'_{Ψ_N K}` are read on the ambient derived categories. -/
theorem NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_pushforwardExchange
    (φ₃ : N.Hom P₃ ι₃.left ι₃'.left) (φ₁ : N.Hom P₁ ι₁.left ι₁'.left)
    (π : P₃.Hom P₁ p.left p'.left) [IsIso (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    [IsIso (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (w : ι₃ ≫ p = ι₁) (w' : ι₃' ≫ p' = ι₁') (htot : φ₃.total ≫ π.total = φ₁.total)
    (hgen : φ₃.generic ≫ π.generic = φ₁.generic)
    (sq : IsPullback ι₃.left (𝟙 Y.left) p.left ι₁.left)
    (sq' : IsPullback ι₃'.left (𝟙 Y'.left) p'.left ι₁'.left)
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι₁.left)
        (openImmersionAdjunction ℓ ι₁'.left)
        (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
          M.obj ≫
      (P₁.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        (X := D((ι₁.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          M.obj)
        (Y := R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            M.obj))
        ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app M).hom ≫
      (π.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app
        (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj M.obj) =
    CategoryStruct.comp
      (X := D((ι₁'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj M.obj))
      (Y := R((p'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (D((ι₃'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj M.obj)))
      ((openProperLowerShriekIso ℓ ι₃' p' ι₁' w').hom.app
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj M)).hom
      (R((p'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι₃.left)
          (openImmersionAdjunction ℓ ι₃'.left)
          (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
            M.obj)) := by
  have hι : ι₃.left ≫ p.left = ι₁.left := congrArg CommaMorphism.left w
  have hι' : ι₃'.left ≫ p'.left = ι₁'.left := congrArg CommaMorphism.left w'
  have := isIso_map_openProperLowerShriekIso_comp_counit ℓ ι₃' p' ι₁' w' sq'
      (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj M)
  apply lowerShriekExchangeOfInv_app_comp_map_comp_pushforwardExchange_app
    (adjπ := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left)
    (adjπ' := derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p'.left)
    (c := leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hι)
    (c' := leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hι')
    (adj₁ := openImmersionAdjunction ℓ ι₁.left) (adj₃ := openImmersionAdjunction ℓ ι₃.left)
    (adj₁' := openImmersionAdjunction ℓ ι₁'.left) (adj₃' := openImmersionAdjunction ℓ ι₃'.left)
  case hχπ => exact π.map_pushforwardExchange_app_comp_counit_app (Profinite.padicAlgClRingObj ℓ)
  case hα =>
    intro A
    rw [← reassoc_of% φ₃.pullbackExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) π φ₁ hι hι'
          htot hgen A,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  case hE => exact unit_comp_upperStarComp_comp_map_openProperLowerShriekIso ℓ ι₃ p ι₁ w sq M
  case hE' =>
    exact unit_comp_upperStarComp_comp_map_openProperLowerShriekIso ℓ ι₃' p' ι₁' w' sq'
      (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj M)
  case hEb' => exact this


section General

variable [IsProper (toPoint X₃).left] [IsProper (toPoint X₁).left]
  [IsProper (toPoint X₃').left] [IsProper (toPoint X₁').left]
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {T : NearbyCyclesModel (point k).left (point k').left}
  (hS : T.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- **The identifications `E` and `Ra_! ≅ ι_! ⋙ Ra_*` are compatible**: on the underlying
complexes, the identification `Ra₁_! K ≅ Ra₁_* ι₁! K` followed by `Ra₁_*(E_K)` for
`E : ι₁! ≅ Rp_* ι₃!` (`ProEtale.CondensedRing.openProperLowerShriekIso`) and the composition
`Ra₁_* Rp_* ≅ Ra₃_*` (the conjugate of `L(p ≫ a₁)^* ≅ Lp^* La₁^*`) is the identification
`Ra₃_! K ≅ Ra₃_* ι₃! K`. The identifications are written with the restricted functors as lifts of
the ambient ones, as in `compactSupportExchangeOfCompactification_eq_lift`. -/
lemma compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom
    (w : ι₃ ≫ p = ι₁)
    (ha : p.left ≫ (toPoint X₁).left = (toPoint X₃).left)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ (toPoint Y))
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((ι₁.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₁).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R(((toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₁)).obj K).property))
        (compactificationLowerShriekIso ℓ ι₁ (toPoint X₁) (comp_toPoint ι₁))).app K).hom ≫
      R(((toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app K).hom ≫
      (conjugateIsoEquiv
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint X₃).left)
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
          (toPoint X₁).left).comp
          (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left))
        (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) ha).symm).inv.app
          (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj) =
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ (toPoint Y))
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₃).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R(((toPoint X₃).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₃)).obj K).property))
        (compactificationLowerShriekIso ℓ ι₃ (toPoint X₃) (comp_toPoint ι₃))).app K).hom := by
  have h := congrArg (fun f ↦ f.hom)
    (compactificationLowerShriekIso_hom_app_comp_map_openProperLowerShriekIso ℓ ι₃ p ι₁
      (toPoint X₁) (toPoint X₃) w (comp_toPoint p) (comp_toPoint ι₁) (comp_toPoint ι₃) K)
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleLowerStar_map_hom,
    boundedConstructibleLowerStarCompOfEq_hom_app_hom] at h
  exact h

/-- `compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom` on the
restriction `K = Ψ M` of a functor `Ψ` preserving bounded constructible complexes. -/
lemma compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom_lift
    (w : ι₃ ≫ p = ι₁)
    (ha : p.left ≫ (toPoint X₁).left = (toPoint X₃).left) {Z : Scheme.{u}}
    (Ψ : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hΨ : ∀ K : Dᵇc(Z)⟦Profinite.padicAlgClRingObj ℓ⟧,
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
        (Ψ.obj K.obj))
    (M : Dᵇc(Z)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ (toPoint Y))
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((ι₁.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₁).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R(((toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₁)).obj K).property))
        (compactificationLowerShriekIso ℓ ι₁ (toPoint X₁) (comp_toPoint ι₁))).app
          (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom ≫
      R(((toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (X := (boundedConstructible _).ι.obj (((boundedConstructible _).lift
          ((boundedConstructible _).ι ⋙ D((ι₁.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
          (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₁).obj K).property)).obj
            (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)))
        (Y := R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj (Ψ.obj M.obj)))
        ((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app
          (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom ≫
      (conjugateIsoEquiv
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint X₃).left)
        ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
          (toPoint X₁).left).comp
          (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left))
        (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) ha).symm).inv.app
          (D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj (Ψ.obj M.obj)) =
    ((Iso.hom (X := boundedConstructibleLowerShriek ℓ (toPoint Y))
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₃).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R(((toPoint X₃).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₃)).obj K).property))
        (compactificationLowerShriekIso ℓ ι₃ (toPoint X₃) (comp_toPoint ι₃))).app
          (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙ Ψ) hΨ).obj M)).hom :=
  compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom ℓ w ha _

omit [IsProper p.left] [IsProper p'.left] [IsOpenImmersion ι₁.left] [IsOpenImmersion ι₁'.left] in
/-- Unfolding `compactSupportExchangeOfCompactification` into `compactSupportExchangeAux`, with
all the restricted functors written as lifts of the ambient ones and their compatibilities with
the inclusions as `ObjectProperty.liftCompιIso`. -/
lemma compactSupportExchangeOfCompactification_eq_lift (φ₃ : N.Hom P₃ ι₃.left ι₃'.left)
    [IsIso (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (a₃ : P₃.Hom T (toPoint X₃).left (toPoint X₃').left)
    (ha₃ : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      X₃.left)).ι (a₃.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))) :
    compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint ι₃) (comp_toPoint ι₃') φ₃ a₃
        ha₃ =
      compactSupportExchangeAux
        (Sp := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property)
        (Ts := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          T.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
            fun K ↦ hS K.obj K.property)
        (OLS := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          D((ι₃.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₃).obj K).property)
        (OLS' := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          D((ι₃'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι₃').obj K).property)
        (LStp := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          R(((toPoint X₃).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₃)).obj K).property)
        (LStp' := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          R(((toPoint X₃').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint X₃')).obj K).property)
        (ObjectProperty.fullyFaithfulι _)
        (compactificationLowerShriekIso ℓ ι₃' (toPoint X₃') (comp_toPoint ι₃'))
        (compactificationLowerShriekIso ℓ ι₃ (toPoint X₃) (comp_toPoint ι₃))
        (ObjectProperty.liftCompιIso _ _ _) (ObjectProperty.liftCompιIso _ _ _)
        (ObjectProperty.liftCompιIso _ _ _) (ObjectProperty.liftCompιIso _ _ _)
        (ObjectProperty.liftCompιIso _ _ _) (ObjectProperty.liftCompιIso _ _ _)
        (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι₃.left)
          (openImmersionAdjunction ℓ ι₃'.left)
          (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
        (invOnSubcategory _ _ ha₃) :=
  rfl


/-- **The compact-support exchange of a compactification is unchanged along a refinement**
(blueprint `prose-E-15`, proof): for compactifications `N ⊆ P₃` and `N ⊆ P₁` of a
model `N`, with structure morphisms `a₃`, `a₁` to the trait, and a morphism of models
`π : P₃ ⟶ P₁` over proper `p`, `p'` with `ι₁ = ι₃ ≫ p`, `a₃ = π ≫ a₁` and `N` cartesian over
`P₁`, the compact-support exchanges `ν = χ_a⁻¹ ∘ Ra'_*(ν_ι)` of the two compactifications agree. -/
theorem compactSupportExchangeOfCompactification_eq_of_refinement
    (φ₃ : N.Hom P₃ ι₃.left ι₃'.left) (φ₁ : N.Hom P₁ ι₁.left ι₁'.left)
    [IsIso (φ₃.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    [IsIso (φ₁.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (a₃ : P₃.Hom T (toPoint X₃).left (toPoint X₃').left)
    (a₁ : P₁.Hom T (toPoint X₁).left (toPoint X₁').left)
    (ha₃ : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      X₃.left)).ι (a₃.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
    (ha₁ : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      X₁.left)).ι (a₁.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
    (π : P₃.Hom P₁ p.left p'.left) (w : ι₃ ≫ p = ι₁) (w' : ι₃' ≫ p' = ι₁')
    (htot : φ₃.total ≫ π.total = φ₁.total) (hgen : φ₃.generic ≫ π.generic = φ₁.generic)
    (hatot : π.total ≫ a₁.total = a₃.total) (hagen : π.generic ≫ a₁.generic = a₃.generic)
    (sq : IsPullback ι₃.left (𝟙 Y.left) p.left ι₁.left)
    (sq' : IsPullback ι₃'.left (𝟙 Y'.left) p'.left ι₁'.left) :
    compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint ι₃) (comp_toPoint ι₃') φ₃ a₃
        ha₃ =
      compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint ι₁) (comp_toPoint ι₁') φ₁ a₁
        ha₁ := by
  have ha : p.left ≫ (toPoint X₁).left = (toPoint X₃).left :=
    congrArg CommaMorphism.left (comp_toPoint p)
  have ha' : p'.left ≫ (toPoint X₁').left = (toPoint X₃').left :=
    congrArg CommaMorphism.left (comp_toPoint p')
  rw [compactSupportExchangeOfCompactification_eq_lift,
    compactSupportExchangeOfCompactification_eq_lift]
  apply compactSupportExchangeAux_lift_eq_of_refinement
    (χ₁ := a₁.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
    (χ₃ := a₃.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
    (conj := conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint X₃).left)
      ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (toPoint X₁).left).comp
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left))
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) ha).symm)
    (conj' := conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) (toPoint X₃').left)
      ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (toPoint X₁').left).comp
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p'.left))
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) ha').symm)
    (χπ := π.pushforwardExchange (Profinite.padicAlgClRingObj ℓ))
  case hχ =>
    intro A
    rw [← reassoc_of% π.pushforwardExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) a₁
      a₃ ha ha' hatot hagen A, Iso.hom_inv_id_app, Category.comp_id]
  case H =>
    intro M
    refine ⟨((openProperLowerShriekIso ℓ ι₃ p ι₁ w).hom.app M).hom,
      ((openProperLowerShriekIso ℓ ι₃' p' ι₁' w').hom.app
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj M)).hom,
      ?_, ?_, ?_⟩
    · cast_proofs NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_pushforwardExchange ℓ φ₃
        φ₁ π w w' htot hgen sq sq' hN M
    · cast_proofs
        compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom_lift
        ℓ w' ha' (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) (fun K ↦ hN K.obj K.property) M
    · have h := compactificationLowerShriekIso_hom_app_hom_comp_map_openProperLowerShriekIso_hom ℓ
        w ha M
      rw [← Functor.map_comp]
      congr 1
      rw [← cancel_epi ((compactificationLowerShriekIso ℓ ι₁ (toPoint X₁)
        (comp_toPoint ι₁)).hom.app M).hom]
      refine comp_comp_eq_comp_of_comp_eq _ _ _ ((compactificationLowerShriekIso ℓ ι₃ (toPoint X₃)
        (comp_toPoint ι₃)).hom.app M).hom _ ?_ ?_ ?_
      · cast_proofs h
      · rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
        rfl
      · rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
        rfl


end General

end Refinement

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))} {h : N.IsTraitModelOfBase k q g}

namespace Compactification

variable (C : h.Compactification)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_P` of the structure morphism of a
compactification is invertible on bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`). -/
lemma isIsoOn_pushforwardExchange :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) C.X.left)).ι
      (C.isTraitModelOfBase.toTrait.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) :=
  fun K ↦ C.isTraitModelOfBase.isIso_pushforwardExchange_app_ambient ℓ C.isPullback_ε _ K.property

instance : IsIso (C.hom.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
  C.hom.isIso_pullbackExchange_of_isOpenImmersion _ C.isPullback_hom_j

/-- **The compact-support exchange of a compactification** (blueprint `prose-E-15`
(3)): for the structure morphisms `a : Y ⟶ Spec k`, `a' : Y' ⟶ Spec k'` and a compactification
`N ⊆ P` over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`, the exchange `ν = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) :
Ra'_! Ψ_N ⟶ Ψ_S Ra_!` (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`). -/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙ traitSpecialization k k' (ℓ := ℓ) :=
  compactSupportExchangeOfCompactification ℓ (h.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) (comp_toPoint C.ι) (comp_toPoint C.ι') C.hom
    C.isTraitModelOfBase.toTrait (C.isIsoOn_pushforwardExchange ℓ)


/-- **The compact-support exchange is unchanged along a refinement** (blueprint
`prose-E-15`, proof: "compatibility of `ν_h` and `χ_q⁻¹ Rq_{s*}(ν_{h''})`"): an
instance of `ProEtale.CondensedRing.compactSupportExchangeOfCompactification_eq_of_refinement`. -/
theorem compactSupportExchange_eq_of_refinement {C₃ C₁ : h.Compactification}
    (r : C₃.Refinement C₁) : C₃.compactSupportExchange ℓ = C₁.compactSupportExchange ℓ :=
  compactSupportExchangeOfCompactification_eq_of_refinement ℓ (h.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) C₃.hom C₁.hom C₃.isTraitModelOfBase.toTrait
    C₁.isTraitModelOfBase.toTrait (C₃.isIsoOn_pushforwardExchange ℓ)
    (C₁.isIsoOn_pushforwardExchange ℓ) r.π r.ι_comp r.ι'_comp r.hom_total_comp
    r.hom_generic_comp r.qc_eq.symm r.gc_eq.symm r.isPullback_ι r.isPullback_ι'

/-- **The compact-support exchange does not depend on the compactification** (blueprint
`prose-E-15`): two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`), along which the
compact-support exchange is unchanged
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq_of_refinement`).
-/
theorem compactSupportExchange_eq (C₁ C₂ : h.Compactification) :
    C₁.compactSupportExchange ℓ = C₂.compactSupportExchange ℓ := by
  obtain ⟨C₃, ⟨r₁⟩, ⟨r₂⟩⟩ := C₁.exists_refinement C₂
  rw [← compactSupportExchange_eq_of_refinement ℓ r₁, compactSupportExchange_eq_of_refinement ℓ r₂]

end Compactification

variable (h) in
/-- The compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism of a
trait model over the base (blueprint `prose-E-15` (3)): the exchange of any
compactification (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange`),
which does not depend on it
(`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange_eq_compactSupportExchange`). -/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙ traitSpecialization k k' (ℓ := ℓ) :=
  h.nonempty_compactification.some.compactSupportExchange ℓ

/-- The compact-support exchange of a trait model over the base is that of any of its
compactifications. -/
lemma compactSupportExchange_eq_compactSupportExchange (C : h.Compactification) :
    h.compactSupportExchange ℓ = C.compactSupportExchange ℓ :=
  Compactification.compactSupportExchange_eq ℓ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase
