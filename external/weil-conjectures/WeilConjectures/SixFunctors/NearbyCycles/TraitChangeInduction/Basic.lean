/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Slice
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates
public import WeilConjectures.SixFunctors.NearbyCycles.RestrictOpens
public import WeilConjectures.SixFunctors.NearbyCycles.ProperTraitChange
public import WeilConjectures.SixFunctors.NearbyCycles.TraitCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.BasicCharts
import WeilConjectures.Tactic.ExactModProofs

/-!

# Deligne's induction for the change of strictly henselian trait

This file proves `NearbyCyclesModel.TraitChangeInvariance T m` for every `m`
(`NearbyCyclesModel.traitChangeInvariance`), i.e. SGA 4½, [Th. finitude], Prop. 3.7, with
coefficients a finite ring `T`, by induction on the dimension `m` of the affine spaces into
which the total space locally embeds.

1. **Proper models** (`NearbyCyclesModel.traitChangeInvariance_of_isProper`). The exchange is a
   morphism of complexes of étale origin on the special fibre `X'`, a scheme of finite type over
   the separably closed field `κ`. Its global cohomology `Rp₂_*` is invertible by step (B)
   (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_isProper_trait`), and it is invertible
   after pullback to the slice over the generic point of every coordinate line of every chart
   (step (A), `NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`, using the induction
   hypothesis). Every non-closed point of `X'` lies over such a generic point
   (`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), so the
   closed-point criterion
   (`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) applies.
2. **Charts** (`NearbyCyclesModel.traitChangeInvariance_of_isImmersion`): a model with an
   immersion into `𝔸(ι; S₁)` is open in its closure in `ℙ(ι; S₁)`, a proper model locally embedding
   into `𝔸(ι; S₁)` (`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`), and the exchange
   is invertible once it is for the compactification
   (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`).
3. **General models**: invertibility of the exchange is local on the total space
   (`NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- A restatement of
`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens` in
which the special fibre `M.i⁻¹(φ⁻¹ V)` of the restriction is elaborated as in the type of
`NearbyCyclesModel.Hom.restrictOpens`, so that it applies syntactically to the outputs of lemmas
about the restricted morphism of models (the two elaborations are definitionally equal, but
unifying them at a concrete coefficient ring times out). -/
theorem Hom.isIso_leftDerivedUpperStar_comp_map_pullbackExchange_app_of_restrictOpens
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (φ : M.Hom N f f') (V : N.total.Opens)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    {W : Scheme.{u}} (h : W ⟶ pullback M.i (φ.total ⁻¹ᵁ V : M.total.Opens).ι)
    (H : IsIso (L((h)^*⟦Λ⟧).map (((φ.restrictOpens V).toGeneric.pullbackExchange Λ).app
      (L(((N.restrictOpensHom V).generic)^*⟦Λ⟧).obj K)))) :
    IsIso (L((h ≫ pullback.fst M.i (φ.total ⁻¹ᵁ V : M.total.Opens).ι)^*⟦Λ⟧).map
      ((φ.toGeneric.pullbackExchange Λ).app K)) :=
  φ.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens Λ V K h H

/-- **The witnesses of the closed-point criterion for a chart** (SGA 4½, [Th. finitude], proof
of 3.7, step (A)). In the situation of `NearbyCyclesModel.TraitChangeInvariance`, assume that the
total space of `N` has an immersion `e : 𝒳_N ⟶ 𝔸(n; S₁)` over `S₁` with `|n| ≤ m`, and the
invariance in chart dimension smaller than `m`. Every non-closed point `x` of the special fibre
`X'` of `M` is in the image of a morphism `h : W ⟶ X'` along which the pullback of the exchange
of `φ.toGeneric` is invertible: the induced immersion `X' ⟶ 𝔸(n; κ)` has a coordinate sending `x`
to the generic point of `𝔸¹_κ`, and one slices along it
(`NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`). -/
theorem Hom.exists_isIso_map_pullbackExchange_of_isImmersion {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [LocallyOfFiniteType q₁] [QuasiCompact q₁] [IsSeparated q₁] {n : Type u} [Finite n]
    (e : N.total ⟶ 𝔸(n; Spec (.of R₁))) [IsImmersion e]
    (he : e ≫ 𝔸(n; Spec (.of R₁)) ↘ Spec (.of R₁) = q₁) (hn : Nat.card n ≤ m)
    (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K))
    (x : X') (hx : ¬ IsClosed ({x} : Set X')) :
    ∃ (W : Scheme.{u}) (h : W ⟶ X') (w : W), h w = x ∧
      IsIso ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map
        ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) := by
  have hA₂ := AffineSpace.isPullback_map (n := n) (Spec.map (CommRingCat.ofHom ι))
  have hbι : IsPullback (M.i ≫ φ.total) p₂ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact hMi.paste_horiz hφ
  -- the charts of the total space and of the special fibre of `M`
  let eM := hA₂.lift (φ.total ≫ e) q₂ (by rw [Category.assoc, he, hφ.w])
  let eX := (AffineSpace.isPullback_map (n := n)
    (Spec.map (CommRingCat.ofHom (b₂.comp ι)))).lift ((M.i ≫ φ.total) ≫ e) p₂
    (by rw [Category.assoc, he, hbι.w])
  have : IsImmersion eX := AffineSpace.isImmersion_lift_isPullback_map hbι e he
  have hXM : eX ≫ AffineSpace.map n (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ eM := by
    refine hA₂.hom_ext ?_ ?_
    · rw [Category.assoc, ← AffineSpace.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        IsPullback.lift_fst]
      simp [eM]
    · rw [Category.assoc, AffineSpace.map_over, IsPullback.lift_snd_assoc, Category.assoc,
        IsPullback.lift_snd, hMi.w]
  obtain ⟨i, hi⟩ := AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed eX hx
  have hcard : Nat.card {j : n // j ≠ i} < Nat.card n := Finite.card_subtype_lt (x := i) (by simp)
  have hm {S' : Scheme.{u}} (σ : S' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))) :
      (pullback.snd (e ≫ AffineSpace.reindex (fun _ ↦ i) _) σ).LocallyEmbedsInAffineSpace
        (m - 1) := by
    obtain ⟨c', hc', hc'σ⟩ := exists_isImmersion_pullback_reindex e i σ
    exact (Scheme.Hom.LocallyEmbedsInAffineSpace.of_isImmersion c' hc'σ).mono (by omega)
  obtain ⟨W, h, hcov, hiso⟩ := φ.exists_isIso_map_pullbackExchange_slice T
    (ih (m - 1) (by omega)) hι hun p hp hpT ha₁ ha₂ halg₁ halg₂ hc hb₂ q₁ g₁ hNj p₁ hNi q₂ g₂
    hMj p₂ hMi hφ hgen hs (e ≫ AffineSpace.reindex (fun _ ↦ i) _) (by simp [he])
    hm (eM ≫ AffineSpace.reindex (fun _ ↦ i) _)
    (by rw [Category.assoc, ← AffineSpace.map_reindex, hA₂.lift_fst_assoc, Category.assoc])
    (by simp [eM]) (eX ≫ AffineSpace.reindex (fun _ ↦ i) _)
    (by rw [Category.assoc, ← AffineSpace.map_reindex, reassoc_of% hXM])
    (by simp [eX]) K hK
  obtain ⟨w, hw⟩ := hcov x hi
  exact ⟨W, h, w, hw, hiso⟩

/-- **The witnesses of the closed-point criterion** (SGA 4½, [Th. finitude], proof of 3.7,
step (A)). In the situation of `NearbyCyclesModel.TraitChangeInvariance` in chart dimension `m`,
assuming it in smaller chart dimension, every non-closed point `x` of the special fibre `X'` of
`M` is in the image of a morphism `h : W ⟶ X'` along which the pullback of the exchange of
`φ.toGeneric` is invertible: choose a chart `V ⟶ 𝔸(ι; S₁)` of `N` around the image of `x`, a
coordinate sending `x` to the generic point of `𝔸¹_κ`
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), and slice the
restriction of `φ` to `V` along it (`NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`,
`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens`). -/
theorem Hom.exists_isIso_map_pullbackExchange_of_not_isClosed {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [LocallyOfFiniteType q₁] [QuasiCompact q₁] [IsSeparated q₁]
    (hm : q₁.LocallyEmbedsInAffineSpace m) (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K))
    (x : X') (hx : ¬ IsClosed ({x} : Set X')) :
    ∃ (W : Scheme.{u}) (h : W ⟶ X') (w : W), h w = x ∧
      IsIso ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map
        ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) := by
  obtain ⟨U, hU, hxU, n, _, e, hn, he, heq⟩ := hm.exists_isAffineOpen (φ.total (M.i x))
  have : IsAffine U := hU
  have : LocallyOfFiniteType q₂ := MorphismProperty.of_isPullback hφ inferInstance
  have : LocallyOfFiniteType p₂ := MorphismProperty.of_isPullback hMi inferInstance
  have : JacobsonSpace X' := LocallyOfFiniteType.jacobsonSpace p₂
  obtain ⟨xU, rfl⟩ : x ∈ Set.range (pullback.fst M.i (φ.total ⁻¹ᵁ U).ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hxU
  obtain ⟨W, h, w, hw, hiso⟩ :=
    (φ.restrictOpens U).exists_isIso_map_pullbackExchange_of_isImmersion T ih hι hun p hp hpT
      ha₁ ha₂ halg₁ halg₂ hc hb₂ (U.ι ≫ q₁) e heq hn (pullback.fst _ _ ≫ g₁)
      (isPullback_restrictOpens_j N U hNj) (pullback.fst _ _ ≫ p₁)
      (isPullback_restrictOpens_i N U hNi) ((φ.total ⁻¹ᵁ U).ι ≫ q₂) (pullback.fst _ _ ≫ g₂)
      (isPullback_restrictOpens_j M _ hMj) (pullback.fst _ _ ≫ p₂)
      (isPullback_restrictOpens_i M _ hMi) (φ.isPullback_restrictOpens_total U hφ)
      (φ.restrictOpens_generic_comp_eq U hgen) (by simp [hs])
      (L(((N.restrictOpensHom U).generic)^*⟦Profinite.continuousMapRingObj T⟧).obj K)
      (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T _
        hK) xU (not_isClosed_singleton_of_isOpenImmersion _ hx)
  have key := φ.isIso_leftDerivedUpperStar_comp_map_pullbackExchange_app_of_restrictOpens
    (Profinite.continuousMapRingObj T) U K h (by exact_mod_proofs hiso)
  exact ⟨W, h ≫ pullback.fst M.i (φ.total ⁻¹ᵁ U : M.total.Opens).ι, w,
    by rw [Scheme.Hom.comp_apply, hw], by exact_mod_proofs key⟩

/-- **Proper models** (SGA 4½, [Th. finitude], proof of 3.7). In the situation of
`NearbyCyclesModel.TraitChangeInvariance` with `q₁` proper, assuming the invariance in smaller
chart dimension, the exchange is invertible: its global cohomology is invertible by step (B), and
it is invertible over every non-closed point of the special fibre by step (A)
(`NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_of_not_isClosed`); conclude with the
closed-point criterion. -/
theorem traitChangeInvariance_of_isProper {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [IsProper q₁] (hm : q₁.LocallyEmbedsInAffineSpace m) (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K) := by
  have : IsProper q₂ := MorphismProperty.of_isPullback hφ ‹_›
  have : LocallyOfFiniteType p₂ := MorphismProperty.of_isPullback hMi inferInstance
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed T p₂ _
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T f'
      (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
        N.toGeneric.i (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj
          T N.toGeneric.j
          (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
            N.toGeneric.ε hK))))
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
      M.toGeneric.i (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj
        T M.toGeneric.j
        (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
          M.toGeneric.ε
          (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
            φ.generic hK))))
    (fun x hx ↦ φ.exists_isIso_map_pullbackExchange_of_not_isClosed T ih hι hun p hp hpT ha₁ ha₂
      halg₁ halg₂ hc hb₂ q₁ hm g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen hs K hK x hx) ?_
  exact φ.isIso_map_pullbackExchange_app_of_isProper_trait T hc (RingHom.id_comp _) hb₂ q₁ g₁
    hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen (by simpa using hs) K hK

/-- The pullback exchange of the morphism of models `NearbyCyclesModel.ofOverTraitHom` is that of
the induced morphism of the models of the geometric generic fibres: these models have `ε = 𝟙`. -/
theorem isIso_ofOverTraitHom_pullbackExchange_app_of_toGeneric
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A₁ A₂ B₁ B₂ C₁ C₂ : Type u} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [CommRing C₁] [CommRing C₂] (a₁ : A₁ →+* B₁) (b₁ : A₁ →+* C₁) (a₂ : A₂ →+* B₂)
    (b₂ : A₂ →+* C₂) (ι : A₁ →+* A₂) (c : B₁ →+* B₂) (d : C₁ →+* C₂)
    (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι) {Z₁ Z₂ : Scheme.{u}}
    (q₁ : Z₁ ⟶ Spec (.of A₁)) (q₂ : Z₂ ⟶ Spec (.of A₂)) (v : Z₂ ⟶ Z₁)
    (hv : v ≫ q₁ = q₂ ≫ Spec.map (CommRingCat.ofHom ι))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (pullback q₁ (Spec.map (CommRingCat.ofHom a₁)))) Ab.{u + 1})
      (condensedRingObj Λ (pullback q₁ (Spec.map (CommRingCat.ofHom a₁))))))
    (H : IsIso (((ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd q₁ q₂ v hv).toGeneric.pullbackExchange
      Λ).app L)) :
    IsIso (((ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd q₁ q₂ v hv).pullbackExchange Λ).app L) := by
  have e : (ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd q₁ q₂ v hv).toGeneric.pullbackExchange Λ =
      (ofOverTraitHom a₁ b₁ a₂ b₂ ι c d hc hd q₁ q₂ v hv).pullbackExchange Λ := rfl
  rw [← e]
  exact H

/-- **Charts** (SGA 4½, [Th. finitude], proof of 3.7). In the situation of
`NearbyCyclesModel.TraitChangeInvariance`, assume that the total space of `N` has an immersion
`e : 𝒳_N ⟶ 𝔸(n; S₁)` over `S₁` with `|n| ≤ m`, and the invariance in chart dimension smaller
than `m`. Then the exchange is invertible: the closure of `𝒳_N` in `ℙ(n; S₁)` is a proper model
locally embedding into `𝔸(n; S₁)`
(`AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`), to
which one reduces (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`), and
which is handled by `NearbyCyclesModel.traitChangeInvariance_of_isProper`. -/
theorem traitChangeInvariance_of_isImmersion {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [QuasiCompact q₁] {n : Type u} [Finite n] (e : N.total ⟶ 𝔸(n; Spec (.of R₁))) [IsImmersion e]
    (he : e ≫ 𝔸(n; Spec (.of R₁)) ↘ Spec (.of R₁) = q₁) (hn : Nat.card n ≤ m)
    (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K) := by
  refine φ.isIso_pullbackExchange_app_of_compactification T (b₁ := b₂.comp ι) (d := RingHom.id κ)
    hc (RingHom.id_comp _) q₁ g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen (by simpa using hs)
    (Compactification.ofIsImmersionAffineSpace e he) (fun L hL ↦ ?_) K hK
  have key := traitChangeInvariance_of_isProper T ih hι hun p hp hpT ha₁ ha₂ halg₁ halg₂ hc hb₂
    (ofOverTraitHom a₁ (b₂.comp ι) a₂ b₂ ι c (RingHom.id κ) hc (RingHom.id_comp _)
      (Compactification.ofIsImmersionAffineSpace e he).g (pullback.snd _ _) (pullback.fst _ _)
      pullback.condition)
    (Compactification.ofIsImmersionAffineSpace e he).g
    ((Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace e he).mono hn)
    _ (IsPullback.of_hasPullback _ _) _ (IsPullback.of_hasPullback _ _) _ _
    (IsPullback.of_hasPullback _ _) _ (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) (pullback.lift_snd _ _ _) (by simp) L hL
  have bb := isIso_ofOverTraitHom_pullbackExchange_app_of_toGeneric
    (Profinite.continuousMapRingObj T) a₁ (b₂.comp ι) a₂ b₂ ι c (RingHom.id κ) hc
    (RingHom.id_comp _) (Compactification.ofIsImmersionAffineSpace e he).g (pullback.snd _ _)
    (pullback.fst _ _) pullback.condition L (by exact_mod_proofs key)
  exact_mod_proofs bb

/-- **Deligne's induction** (SGA 4½, [Th. finitude], Prop. 3.7, coefficients a finite ring): the
invariance of nearby cycles under change of strictly henselian trait holds in every chart
dimension. By strong induction on `m`: invertibility is local on the total space
(`NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`), so one may assume
an immersion `N ⟶ 𝔸(ι; S₁)` with `|ι| ≤ m`; the closure in `ℙ(ι; S₁)` is a proper model locally
embedding into `𝔸(ι; S₁)` (`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`,
`AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`), to
which one reduces (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`), and
the proper case is `NearbyCyclesModel.traitChangeInvariance_of_isProper`. -/
theorem traitChangeInvariance (m : ℕ) : TraitChangeInvariance.{u} T m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  refine ⟨fun R₁ R₂ _ _ _ _ _ _ _ _ ι _ hι hun p _ hp hpT Ω₁ Ω₂ _ _ _ _ a₁ a₂ c ha₁ ha₂ halg₁
    halg₂ hc κ _ _ b₂ hb₂ X X' Y Y' M N f f' φ q₁ _ _ _ hm g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen
    hs K hK ↦ ?_⟩
  suffices H : ∀ x : X', ∃ V : N.total.Opens, φ.total (M.i x) ∈ V ∧
      IsIso (((φ.restrictOpens V).toGeneric.pullbackExchange
        (Profinite.continuousMapRingObj T)).app
        (L(((N.restrictOpensHom V).generic)^*⟦Profinite.continuousMapRingObj T⟧).obj K)) by
    have key := φ.isIso_toGeneric_pullbackExchange_app_of_restrictOpens
      (Profinite.continuousMapRingObj T) K (by exact_mod_proofs H)
    exact_mod_proofs key
  intro x
  obtain ⟨U, hU, hxU, n, _, e, hn, he, heq⟩ := hm.exists_isAffineOpen (φ.total (M.i x))
  have : IsAffine U := hU
  refine ⟨U, hxU, ?_⟩
  exact traitChangeInvariance_of_isImmersion T ih hι hun p hp hpT ha₁ ha₂ halg₁ halg₂ hc hb₂
    (φ.restrictOpens U) (U.ι ≫ q₁) e heq hn (pullback.fst _ _ ≫ g₁)
    (isPullback_restrictOpens_j N U hNj) (pullback.fst _ _ ≫ p₁)
    (isPullback_restrictOpens_i N U hNi) ((φ.total ⁻¹ᵁ U).ι ≫ q₂) (pullback.fst _ _ ≫ g₂)
    (isPullback_restrictOpens_j M _ hMj) (pullback.fst _ _ ≫ p₂)
    (isPullback_restrictOpens_i M _ hMi) (φ.isPullback_restrictOpens_total U hφ)
    (φ.restrictOpens_generic_comp_eq U hgen) (by simp [hs])
    (L(((N.restrictOpensHom U).generic)^*⟦Profinite.continuousMapRingObj T⟧).obj K)
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T _ hK)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
