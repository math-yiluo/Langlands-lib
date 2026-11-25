/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.UpperStarPreservesLimits

/-!
# Derived complete `𝒪_E`-complexes in the condensed formalism

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`. A complex `K` of `𝒪_{E,X}`-module objects on `X_proét` is *derived complete*
(`ProEtale.derivedCompleteIntegers`) if every morphism to `K` from a complex `Z` whose first
derived reduction `Z ⊗ᴸ 𝔽_E` vanishes, i.e. on which a uniformizer acts invertibly, is zero
(Bhatt–Scholze, §3.4 and §6.5; Stacks, Tag 091N).

## Main results

- `ProEtale.isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction`: **derived
  Nakayama**, a derived complete complex with vanishing first derived reduction is zero.
- `ProEtale.derivedCompleteIntegers_ext₂`: derived complete complexes are closed under
  extensions.
- `ProEtale.derivedCompleteIntegers_rightDerivedLowerStar_obj`: `Rf_*` preserves derived
  complete complexes.
- `ProEtale.derivedCompleteIntegers_leftDerivedUpperStar_obj`: `Lf^*` preserves derived
  complete complexes, for a morphism of quasi-compact quasi-separated schemes. The pullback
  commutes with derived limits, since it preserves countable products
  (`ProEtale.preservesLimitsOfSize_upperStar_ab`), and `K` is derived complete if and only if
  the derived limit of `⋯ --ϖ--> K --ϖ--> K` vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- A complex `K` of `𝒪_{E,X}`-module objects is **derived complete** if every morphism to `K`
from a complex `Z` with vanishing first derived reduction `Z ⊗ᴸ 𝔽_E` is zero. -/
def derivedCompleteIntegers (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :=
  fun K ↦ ∀ ⦃Z⦄, IsZero ((derivedReduction X ℓ E).obj Z) → ∀ f : Z ⟶ K, f = 0

variable {ℓ E}

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **Derived Nakayama**: a derived complete complex whose first derived reduction vanishes is
zero. -/
theorem isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (h : IsZero ((derivedReduction X ℓ E).obj K)) :
    IsZero K :=
  (IsZero.iff_id_eq_zero K).2 (hK h (𝟙 K))

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Complexes with vanishing first derived reduction are closed under shifts. -/
lemma isZero_derivedReduction_shift {X : Scheme.{u}}
    {Z : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hZ : IsZero ((derivedReduction X ℓ E).obj Z)) (n : ℤ) :
    IsZero ((derivedReduction X ℓ E).obj (Z⟦n⟧)) := by
  rw [isZero_derivedReduction_iff] at hZ ⊢
  exact ((shiftFunctor _ n).map_isZero hZ).of_iso
    (((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.commShiftIso
      n).app Z)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Derived complete complexes are closed under extensions: in a distinguished triangle whose
first and third objects are derived complete, so is the second. -/
theorem derivedCompleteIntegers_ext₂ {X : Scheme.{u}}
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))))
    (hT : T ∈ distTriang _) (h₁ : derivedCompleteIntegers ℓ E X T.obj₁)
    (h₃ : derivedCompleteIntegers ℓ E X T.obj₃) : derivedCompleteIntegers ℓ E X T.obj₂ := by
  intro Z hZ f
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ T hT f (h₃ hZ _)
  rw [h₁ hZ g, zero_comp]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Derived complete complexes are closed under shifts. -/
theorem derivedCompleteIntegers_shift {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (n : ℤ) :
    derivedCompleteIntegers ℓ E X (K⟦n⟧) := by
  intro Z hZ f
  have h : f⟦-n⟧' = 0 := (cancel_mono
    ((shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app K)).1 (by
      rw [zero_comp]
      exact hK (isZero_derivedReduction_shift hZ (-n)) _)
  exact (shiftFunctor _ (-n)).map_eq_zero_iff.1 h

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **Derived Nakayama for morphisms**: a morphism of derived complete complexes whose first
derived reduction is an isomorphism is an isomorphism (blueprint
`lemma-reduction-derived-nakayama`): its cone is derived complete, with vanishing first derived
reduction. -/
theorem isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (φ : K ⟶ L)
    (hK : derivedCompleteIntegers ℓ E X K) (hL : derivedCompleteIntegers ℓ E X L)
    (h : IsIso ((derivedReduction X ℓ E).map φ)) : IsIso φ := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle φ
  have hF := (Mod.extendScalars
    (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished _ hT
  have := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map X ℓ E _ h
  have hC : derivedCompleteIntegers ℓ E X C :=
    derivedCompleteIntegers_ext₂ _ (rot_of_distTriang _ hT) hL (derivedCompleteIntegers_shift hK 1)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction hC ?_)
  rw [isZero_derivedReduction_iff]
  exact (Triangle.isZero₃_iff_isIso₁ _ hF).2 this

/-- For an adjunction `F ⊣ G` between preadditive categories, if every morphism `F Z ⟶ K`
vanishes, then so does every morphism `Z ⟶ G K`. -/
lemma _root_.CategoryTheory.Adjunction.eq_zero_of_forall_eq_zero {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {Z : C}
    {K : D} (h : ∀ g : F.obj Z ⟶ K, g = 0) (f : Z ⟶ G.obj K) : f = 0 := by
  obtain ⟨g, rfl⟩ := (adj.homEquiv _ _).surjective f
  have := adj.isRightAdjoint
  rw [h g, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The derived pushforward `Rf_*` preserves derived complete complexes: it is right adjoint to
`Lf^*`, which commutes with the first derived reduction. -/
theorem derivedCompleteIntegers_rightDerivedLowerStar_obj {W X : Scheme.{u}} (f : W ⟶ X)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W))}
    (hK : derivedCompleteIntegers ℓ E W K) :
    derivedCompleteIntegers ℓ E X
      ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
  intro Z hZ g
  have hZ' : IsZero ((derivedReduction W ℓ E).obj
      ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj Z)) := by
    rw [isZero_derivedReduction_iff] at hZ ⊢
    exact ((L((f)^*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E)⟧)).map_isZero
      hZ).of_iso
      ((CondensedRing.derivedUpperStarExtendScalarsIso
        (Profinite.padicIntegersRingObjToResidueField ℓ E) f).app Z)
  exact (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E)
    f).eq_zero_of_forall_eq_zero (hK hZ') g

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- For a uniformizer `ϖ` of `𝒪_E`, a complex is derived complete if and only if it is complete
with respect to the central action of `ϖ` on `D(X)`: the complexes with vanishing first derived
reduction are those on which `ϖ` acts invertibly. -/
lemma derivedCompleteIntegers_iff_isCenterComplete {X : Scheme.{u}}
    {ϖ : PadicAlgCl.integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    derivedCompleteIntegers ℓ E X K ↔ IsCenterComplete (derivedUniformizer X ℓ E ϖ) K := by
  constructor
  · intro hK Z hZ g
    exact hK ((isZero_derivedReduction_iff_isIso hϖ Z).2 hZ) g
  · intro hK Z hZ g
    exact hK ((isZero_derivedReduction_iff_isIso hϖ Z).1 hZ) g

/-- The derived pullback `Lf^*` along a morphism of quasi-compact quasi-separated schemes
preserves derived complete complexes: it commutes with the derived limit of
`⋯ --ϖ--> K --ϖ--> K`, whose vanishing characterizes derived complete complexes. -/
theorem derivedCompleteIntegers_leftDerivedUpperStar_obj {W X : Scheme.{u}} (f : W ⟶ X)
    [CompactSpace W] [QuasiSeparatedSpace W] [CompactSpace X] [QuasiSeparatedSpace X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) :
    derivedCompleteIntegers ℓ E W
      ((L((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ] at hK ⊢
  exact (hK.map (derivedUniformizer W ℓ E ϖ)
    (fun K ↦ CatCenter.derivedCategory_app_shift _ K 1)
    ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).mapDerivedCategory
    (CondensedRing.mapDerivedCategory_upperStar_map_derivedUniformizer_app ℓ E ϖ f)).of_iso
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ f).symm.app K)

end AlgebraicGeometry.ProEtale
