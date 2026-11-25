/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.TraceFormula.Specialization.PointExchange

/-!

# The inverse proper exchange specializes the unit class

Let `φ : M ⟶ S` be a morphism of nearby cycles models from a model `M` of a proper `k`-scheme `B`
with proper special fibre `B'` to the trait `S`, over the structure maps, with proper morphism of
total spaces and cartesian squares of special and of geometric generic fibres. The pushforward
exchange `χ_a : Ψ_s Ra_* ⟶ Ra'_* Ψ_M` is invertible (blueprint `prose-E-03`),
and its inverse, read through `Ra_! ≅ Ra_*`, is a compact-support exchange
`ν_a : Ra'_! Ψ_M ⟶ Ψ_s Ra_!` (`NearbyCyclesModel.Hom.properCompactSupportExchange`). It maps the
specialization of the unit class of `B'` to the specialization of the unit class of `B`:
```
ν_a(ℚ̄_ℓ) ∘ Ra'_!(σ_M) ∘ [B'] = Ψ_s([B]) ∘ σ_s
```
(`NearbyCyclesModel.Hom.unitClass_comp_map_comp_properCompactSupportExchange_app`), by the unit
identity of the pushforward exchange. This is step (D) of the proof of
`proposition-specialization-trace-class` for the class of a proper component of the fixed locus.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {Cs Cs' CB CB' : Type*} [Category Cs] [Category Cs'] [Category CB] [Category CB']
  {La : Cs ⥤ CB} {Ra LSa : CB ⥤ Cs} {La' : Cs' ⥤ CB'} {Ra' LSa' : CB' ⥤ Cs'} {Ψs : Cs ⥤ Cs'}
  {ΨM : CB ⥤ CB'}

/-- The compact-support exchange `ΨM ⋙ LSa' ≅ ΨM ⋙ Ra' ⟶ Ra ⋙ Ψs ≅ LSa ⋙ Ψs` given by the inverse
of an invertible exchange `χ : Ra ⋙ Ψs ⟶ ΨM ⋙ Ra'` and isomorphisms `LSa ≅ Ra`, `LSa' ≅ Ra'`. -/
noncomputable def invExchange (is : LSa ≅ Ra) (is' : LSa' ≅ Ra') (χ : Ra ⋙ Ψs ⟶ ΨM ⋙ Ra')
    [IsIso χ] : ΨM ⋙ LSa' ⟶ LSa ⋙ Ψs :=
  Functor.whiskerLeft ΨM is'.hom ≫ inv χ ≫ Functor.whiskerRight is.inv Ψs

/-- The unit-class identity for the inverse exchange: if
`χ(La u) ∘ Ψs(η u) ∘ σs = Ra'(Ψ_M(εa) ∘ σ_M ∘ εa'⁻¹) ∘ η' u'`, then the inverse exchange maps
`LSa'(σ_M) ∘ is'⁻¹ ∘ Ra'(εa'⁻¹) ∘ η' u'` to `Ψs(is⁻¹ ∘ Ra(εa⁻¹) ∘ η u) ∘ σs`. -/
lemma unitClass_comp_invExchange_app (adj : La ⊣ Ra) (adj' : La' ⊣ Ra') (is : LSa ≅ Ra)
    (is' : LSa' ≅ Ra') (χ : Ra ⋙ Ψs ⟶ ΨM ⋙ Ra') [IsIso χ] {u : Cs} {u' : Cs'} {v : CB} {v' : CB'}
    (εa : v ≅ La.obj u) (εa' : v' ≅ La'.obj u') (σs : u' ⟶ Ψs.obj u) (σM : v' ⟶ ΨM.obj v)
    (hunit : σs ≫ Ψs.map (adj.unit.app u) ≫ χ.app (La.obj u) =
      adj'.unit.app u' ≫ Ra'.map (εa'.inv ≫ σM ≫ ΨM.map εa.hom)) :
    (adj'.unit.app u' ≫ Ra'.map εa'.inv ≫ is'.inv.app v') ≫ LSa'.map σM ≫
        (invExchange is is' χ).app v =
      σs ≫ Ψs.map (adj.unit.app u ≫ Ra.map εa.inv ≫ is.inv.app v) := by
  have hχ : Ψs.map (Ra.map εa.inv) ≫ χ.app v = χ.app (La.obj u) ≫ Ra'.map (ΨM.map εa.inv) :=
    χ.naturality εa.inv
  have key : adj'.unit.app u' ≫ Ra'.map (εa'.inv ≫ σM) ≫ inv (χ.app v) =
      σs ≫ Ψs.map (adj.unit.app u) ≫ Ψs.map (Ra.map εa.inv) := by
    rw [← Category.assoc, IsIso.comp_inv_eq, Category.assoc, Category.assoc, hχ,
      reassoc_of% hunit, ← Ra'.map_comp]
    simp
  have hinv : (inv χ).app v = inv (χ.app v) := NatIso.isIso_inv_app χ v
  have hn := is'.inv.naturality σM
  simp only [invExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, hinv, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc, ← reassoc_of% key, Ra'.map_comp_assoc]

/-- A transformation `χ` between functors preserving full subcategories which is invertible on the
objects of the subcategory restricts to an isomorphism. -/
lemma isIso_liftExchange_of_isIso_app {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'} {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z))
    (h : ∀ Z : PX.FullSubcategory, IsIso (χ.app Z.obj)) :
    IsIso (NearbyCyclesModel.liftExchange χ hR hR' hN hM) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  have : IsIso (PY'.ι.map ((NearbyCyclesModel.liftExchange χ hR hR' hN hM).app Z)) := h Z
  exact isIso_of_reflects_iso _ PY'.ι

end Abstract

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {B : Over (Spec (.of k))} [IsProper B.hom] {B' : Over (Spec (.of k'))} [IsProper B'.hom]
  {M : NearbyCyclesModel B.left B'.left}
  (φ : M.Hom (traitModel k k') (toPoint B).left (toPoint B').left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : (traitModel k k').PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hMt : M.IsTraitModel)
  [IsProper φ.total] (hi : IsPullback M.i (toPoint B').left φ.total (traitModel k k').i)
  (hε : IsPullback M.ε φ.generic (toPoint B).left (traitModel k k').ε)

include hMt hi hε in
/-- The pushforward exchange `χ_a : Ψ_s Ra_* ⟶ Ra'_* Ψ_M` of a proper morphism of models to the
trait with cartesian squares of special and of generic fibres is invertible on bounded
constructible complexes (blueprint `prose-E-03` (2)). -/
lemma isIso_boundedConstructiblePushforwardExchange_of_isProper :
    IsIso (φ.boundedConstructiblePushforwardExchange ℓ hM hN) := by
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have : IsNoetherian (point k).left := inferInstanceAs (IsNoetherian (Spec (.of k)))
  rw [boundedConstructiblePushforwardExchange_eq_liftExchange]
  exact isIso_liftExchange_of_isIso_app _ _ _ _ _
    fun K ↦ φ.isIso_pushforwardExchange_app_of_isProper (point k).hom hMt.exists_over
      (isTraitModel_traitModel k k').exists_over hi hε K.property

/-- **The compact-support exchange of a proper model over the trait** (blueprint
`prose-E-15` (3) for a proper morphism): the inverse of the pushforward exchange
`χ_a`, read through `Ra_! ≅ Ra_*` and `Ra'_! ≅ Ra'_*`. -/
noncomputable def properCompactSupportExchange :
    boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleLowerShriek ℓ (toPoint B') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint B) ⋙
        boundedConstructibleNearbyCycles hN :=
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have : IsProper (toPoint B').left := by rw [toPoint_left]; infer_instance
  have := φ.isIso_boundedConstructiblePushforwardExchange_of_isProper hM hN hMt hi hε
  invExchange (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B'))
    (φ.boundedConstructiblePushforwardExchange ℓ hM hN)

variable (ℓ) in
omit [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] in
/-- The unit class, with the properness of `toPoint X` given as an instance. -/
lemma unitClass_eq (X : Over (Spec (.of k))) [IsProper X.hom] [IsProper (toPoint X).left] :
    BorelMooreSection.unitClass ℓ X =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint X)).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ (toPoint X)).map
          (Functor.Monoidal.εIso
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))).inv ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.app (𝟙_ _) :=
  rfl

/-- **The inverse proper exchange specializes the unit class**:
`ν_a(ℚ̄_ℓ) ∘ Ra'_!(σ_M) ∘ [B'] = Ψ_s([B]) ∘ σ_s`, by the unit identity of `χ_a`. -/
theorem unitClass_comp_map_comp_properCompactSupportExchange_app :
    BorelMooreSection.unitClass ℓ B' ≫
        (boundedConstructibleLowerShriek ℓ (toPoint B')).map
          (boundedConstructibleUnit ℓ hM) ≫
        (φ.properCompactSupportExchange hM hN hMt hi hε).app (𝟙_ _) =
      boundedConstructibleUnit ℓ hN ≫
        (boundedConstructibleNearbyCycles hN).map (BorelMooreSection.unitClass ℓ B) := by
  have : IsProper (toPoint B).left := by rw [toPoint_left]; infer_instance
  have : IsProper (toPoint B').left := by rw [toPoint_left]; infer_instance
  have hu := φ.boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app ℓ hM hN
  have := φ.isIso_boundedConstructiblePushforwardExchange_of_isProper hM hN hMt hi hε
  refine (fun h ↦ ?_) (unitClass_comp_invExchange_app
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint B))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint B'))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B'))
    (φ.boundedConstructiblePushforwardExchange ℓ hM hN) (u := 𝟙_ _) (u' := 𝟙_ _) (v := 𝟙_ _)
    (v' := 𝟙_ _)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint B)))
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint B')))
    (boundedConstructibleUnit ℓ hN) (boundedConstructibleUnit ℓ hM) ?_)
  · rw [unitClass_eq ℓ B, unitClass_eq ℓ B', properCompactSupportExchange]
    exact h
  · exact hu

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
