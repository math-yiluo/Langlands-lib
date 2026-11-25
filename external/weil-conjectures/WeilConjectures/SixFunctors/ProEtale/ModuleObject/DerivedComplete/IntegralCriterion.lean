/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructureTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ConstructibleOfComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The integral constructibility criterion

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, uniformizer `ϖ` and
residue field `𝔽_E`, and `X` a noetherian scheme. Blueprint
`proposition-integral-constructibility-criterion` (section `chap-The-pro-etale-site`) characterizes
the bounded constructible `𝒪_E`-complexes on `X_proét`: a complex `K` is bounded constructible if
and only if it is derived complete and its first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` is
a bounded constructible complex of `𝔽_E`-sheaves (Bhatt–Scholze, *The pro-étale topology for
schemes*, Proposition 6.8.11; Stacks, Tag 09C7).

The implication (1) ⇒ (2) is proved:
`ProEtale.derivedCompleteIntegers_of_boundedConstructible` and
`ProEtale.boundedConstructible_derivedReduction_obj`. This file proves the converse
(2) ⇒ (1), `ProEtale.boundedConstructible_of_derivedCompleteIntegers`.

## Proof of (2) ⇒ (1)

Regard `K₁` as a complex of `𝒪_{E,X}`-modules (`ProEtale.derivedReductionComap`); it is bounded
constructible (`ProEtale.boundedConstructible_comap_derivedExtendScalars_of_derivedReduction`),
with cohomology in some interval `[b - n, b]`. We show by induction on `n` that a derived
complete `K` whose reduction `K₁` is bounded constructible with cohomology in `[b - n, b]` is
bounded constructible (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_amplitude`).
The reduction triangle `K --ϖ--> K ⟶ K₁ ⟶` gives exact sequences
`0 ⟶ coker (ϖ on Hᵠ K) ⟶ Hᵠ K₁ ⟶ ker (ϖ on Hᵠ⁺¹ K) ⟶ 0`.

1. For `q > b` and `q < b - n`, `ϖ` acts surjectively on `Hᵠ K`, which is derived complete;
   hence `Hᵠ K = 0` by Nakayama's lemma (`ProEtale.isZero_homology_of_derivedCompleteIntegers`).
2. `M = Hᵇ K` is constructible
   (`ProEtale.isConstructibleModuleObject_homology_of_derivedCompleteIntegers`): it is derived
   complete, the cokernel of `ϖ` on it is `Hᵇ K₁` (as `Hᵇ⁺¹ K = 0`), and the kernel of `ϖ` on it
   is a quotient of `Hᵇ⁻¹ K₁`, so that
   `ProEtale.isConstructibleModuleObject_of_derivedCompleteIntegers` applies.
3. If `n = 0`, then `K` has the single cohomology sheaf `M`, and is bounded constructible.
   Otherwise, consider the truncation triangle `K' ⟶ K ⟶ K'' ⟶` with `K' = τ^{≤ b - 1} K` and
   `K'' = τ^{≥ b} K = M[-b]`. Then `K''` is derived complete and bounded constructible, so `K'` is
   derived complete. The reduction `K'₁` is bounded constructible, by two-out-of-three in the
   reduced triangle `K'₁ ⟶ K₁ ⟶ K''₁ ⟶`, and has cohomology in `[b - n, b - 1]`: `K'₁` lies in
   degrees `≤ b - 1` and `K''₁` in degrees `≥ b - 1`, by their reduction triangles. By induction
   `K'` is bounded constructible, hence so is `K`
   (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_triangle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- An object of a derived category concentrated in degree `b` has `Hᵠ = 0` for `q ≠ b`. -/
lemma isZero_homologyFunctor_obj_of_ne (X : DerivedCategory C) {b q : ℤ} [X.IsGE b] [X.IsLE b]
    (hq : q ≠ b) : IsZero ((homologyFunctor C q).obj X) := by
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact isZero_of_isGE _ b q hq
  · exact isZero_of_isLE _ b q hq

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ} {X : Scheme.{u}}

/-- Arithmetic for the inductive step of the integral criterion. -/
private lemma lt_of_lt_sub_one_sub {i b : ℤ} {m : ℕ} (h : i < b - 1 - m) :
    i - 1 < b - 1 ∧ i < b - (m + 1 : ℕ) := by
  push_cast
  refine ⟨?_, ?_⟩
  · lia
  · lia

/-- Arithmetic for the base case of the integral criterion. -/
private lemma lt_sub_natCast_zero_or_lt_of_ne {i b : ℤ} (h : i ≠ b) :
    i < b - (0 : ℕ) ∨ b < i := by
  rw [Nat.cast_zero, sub_zero]
  exact lt_or_gt_of_ne h

/-- Arithmetic for the integral criterion. -/
private lemma lt_or_lt_of_lt_sub_toNat_or_lt {i a b : ℤ} (h : i < b - (b - a).toNat ∨ b < i) :
    i < a ∨ b < i := by
  lia

/-- The reduction `K ↦ K₁ = 𝔽_{E,X} ⊗ᴸ K`, regarded as a complex of `𝒪_{E,X}`-modules: the derived
extension of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` followed by the restriction of scalars. -/
noncomputable abbrev derivedReductionComap (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :=
  (Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor ⋙
    (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory

/-- If `K` is derived complete and `Hᵠ K₁ = 0`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K`, then `Hᵠ K = 0`:
`ϖ` acts surjectively on the derived complete sheaf `Hᵠ K`, which vanishes by Nakayama's
lemma. -/
lemma isZero_homology_of_derivedCompleteIntegers
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((derivedReductionComap X ℓ E).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  have := epi_padicIntegersCenter_homology_of_isZero hϖ K q hq
  exact isZero_of_derivedCompleteIntegers_singleFunctor_of_epi hϖ
    (derivedCompleteIntegers_singleFunctor_homology hK q)

/-- If `K` is derived complete with `Hᵇ⁺¹ K = 0` and `K₁ = 𝔽_{E,X} ⊗ᴸ K` is bounded
constructible, then `Hᵇ K` is constructible: the cokernel of `ϖ` on it is `Hᵇ K₁`, and the
kernel of `ϖ` on it is a quotient of `Hᵇ⁻¹ K₁`. -/
lemma isConstructibleModuleObject_homology_of_derivedCompleteIntegers [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (b : ℤ)
    (hb : IsZero ((DerivedCategory.homologyFunctor _ (b + 1)).obj K))
    (h₁ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj K)) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((DerivedCategory.homologyFunctor _ b).obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨e⟩ := nonempty_cokernel_padicIntegersCenter_homology_iso hϖ K b (b + 1) rfl hb
  obtain ⟨f, _⟩ :=
    exists_epi_kernel_padicIntegersCenter_homology hϖ K (b - 1) b (sub_add_cancel b 1)
  exact isConstructibleModuleObject_of_derivedCompleteIntegers hϖ
    (derivedCompleteIntegers_singleFunctor_homology hK b) ((h₁.2 b).of_iso e.symm)
    (h₁.2 (b - 1)) f

/-- The reduction `K ↦ K₁ = 𝔽_{E,X} ⊗ᴸ K`, regarded as a complex of `𝒪_{E,X}`-modules, sends
distinguished triangles to distinguished triangles. -/
lemma map_distinguished_comap_derivedExtendScalars
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _) :
    (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.mapTriangle.obj
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.mapTriangle.obj
        T) ∈ distTriang _ :=
  (Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.map_distinguished _
    ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished
      T hT)

/-- Two-out-of-three for the bounded constructibility of the reductions along a distinguished
triangle `T`: if `(T.obj₂)₁` and `(T.obj₃)₁` are bounded constructible, so is `(T.obj₁)₁`. -/
lemma boundedConstructible_derivedReductionComap_obj₁ [IsNoetherian X]
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _)
    (h₂ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj T.obj₂))
    (h₃ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj T.obj₃)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj T.obj₁) :=
  (boundedConstructible _).ext_of_isTriangulatedClosed₁ _
    (map_distinguished_comap_derivedExtendScalars T hT) h₂ h₃

/-- The reduction `K₁ = 𝔽_{E,X} ⊗ᴸ K` of a bounded constructible complex `K` is bounded
constructible as a complex of `𝒪_{E,X}`-modules. -/
lemma boundedConstructible_derivedReductionComap_obj [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj K) :=
  boundedConstructible_comap_padicIntegersToResidueField
    (boundedConstructible_derivedExtendScalars_residueField X ℓ E.1 K hK)

/-- In a distinguished triangle `T` whose first object lies in degrees `≤ b - 1` and whose third
object is concentrated in degree `b`, the third object is derived complete if the second one
is: its only cohomology sheaf is `Hᵇ T.obj₃ ≅ Hᵇ T.obj₂`. -/
lemma derivedCompleteIntegers_obj₃_of_isLE_of_isGE
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _)
    (b : ℤ) [T.obj₁.IsLE (b - 1)] [T.obj₃.IsGE b] [T.obj₃.IsLE b]
    (hK : derivedCompleteIntegers ℓ E X T.obj₂) : derivedCompleteIntegers ℓ E X T.obj₃ := by
  refine (derivedCompleteIntegers_iff_forall_singleFunctor_homology _).2 fun q ↦ ?_
  rcases eq_or_ne q b with rfl | hq
  · have := DerivedCategory.isIso_homologyFunctor_map_mor₂_of_isLE T hT q
    exact derivedCompleteIntegers_of_iso (derivedCompleteIntegers_singleFunctor_homology hK q)
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((DerivedCategory.homologyFunctor _ q).map T.mor₂)))
  · exact derivedCompleteIntegers_of_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero
      (DerivedCategory.isZero_homologyFunctor_obj_of_ne T.obj₃ hq))

/-- In a distinguished triangle `T` whose first object lies in degrees `≤ b - 1` and whose third
object is concentrated in degree `b`, the third object is bounded constructible if `Hᵇ T.obj₂`
is constructible: its only cohomology sheaf is `Hᵇ T.obj₃ ≅ Hᵇ T.obj₂`. -/
lemma boundedConstructible_obj₃_of_isLE_of_isGE
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _)
    (b : ℤ) [T.obj₁.IsLE (b - 1)] [T.obj₃.IsGE b] [T.obj₃.IsLE b]
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((DerivedCategory.homologyFunctor _ b).obj T.obj₂)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) T.obj₃ := by
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨b, b, fun i hi ↦
    DerivedCategory.isZero_homologyFunctor_obj_of_ne T.obj₃ (hi.elim ne_of_lt ne_of_gt)⟩,
    fun i ↦ ?_⟩
  rcases eq_or_ne i b with rfl | hi
  · have := DerivedCategory.isIso_homologyFunctor_map_mor₂_of_isLE T hT i
    exact hM.of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map T.mor₂))
  · exact isConstructibleModuleObject_of_isZero _
      (DerivedCategory.isZero_homologyFunctor_obj_of_ne T.obj₃ hi)

/-- In a distinguished triangle `T` whose first object lies in degrees `≤ b - 1` and whose third
object lies in degrees `≥ b`, if the reduction `(T.obj₂)₁` has cohomology in degrees
`[b - (m + 1), b]`, then `(T.obj₁)₁` has cohomology in degrees `[b - 1 - m, b - 1]`. Indeed
`(T.obj₁)₁` lies in degrees `≤ b - 1` and `(T.obj₃)₁` in degrees `≥ b - 1`, by the reduction
triangles, and `(T.obj₁)₁ ⟶ (T.obj₂)₁ ⟶ (T.obj₃)₁ ⟶` is distinguished. -/
lemma isZero_homology_derivedReductionComap_obj₁ (m : ℕ)
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _)
    (b : ℤ) (hT₁ : T.obj₁.IsLE (b - 1)) (hT₃ : T.obj₃.IsGE b)
    (hb : ∀ i, i < b - (m + 1 : ℕ) ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionComap X ℓ E).obj T.obj₂)))
    (i : ℤ) (hi : i < b - 1 - m ∨ b - 1 < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionComap X ℓ E).obj T.obj₁)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  rcases hi with hi | hi
  · -- `(T.obj₃)₁` lies in degrees `≥ b - 1`, by the reduction triangle of `T.obj₃`
    obtain ⟨g, h, hTϖ⟩ := exists_distinguished_derivedUniformizer hϖ T.obj₃
    have h₀ : IsZero ((DerivedCategory.homologyFunctor _ (i - 1)).obj
        ((derivedReductionComap X ℓ E).obj T.obj₃)) :=
      DerivedCategory.isZero_of_isGE _ (b - 1) (i - 1) (lt_of_lt_sub_one_sub hi).1
        (hX := DerivedCategory.isGE_obj₃_of_isGE _ hTϖ b hT₃ hT₃)
    exact (DerivedCategory.HomologySequence.exact₁ _ (map_distinguished_comap_derivedExtendScalars
      T hT) (i - 1) i (sub_add_cancel i 1)).isZero_X₂ (h₀.eq_of_src _ _)
      ((hb i (Or.inl (lt_of_lt_sub_one_sub hi).2)).eq_of_tgt _ _)
  · -- `(T.obj₁)₁` lies in degrees `≤ b - 1`, by the reduction triangle of `T.obj₁`
    obtain ⟨g, h, hTϖ⟩ := exists_distinguished_derivedUniformizer hϖ T.obj₁
    exact DerivedCategory.isZero_of_isLE _ (b - 1) i hi
      (hX := DerivedCategory.isLE_obj₃_of_isLE _ hTϖ (b - 1) hT₁ hT₁)

/-- The inductive step of the integral criterion, along a distinguished triangle
`K' ⟶ K ⟶ K'' ⟶ K'[1]` with `K'` in degrees `≤ b - 1` and `K''` concentrated in degree `b`
(for instance the truncation triangle `τ^{≤ b - 1} K ⟶ K ⟶ τ^{≥ b} K ⟶`). Let `K` be derived
complete with `K₁ = 𝔽_{E,X} ⊗ᴸ K` bounded constructible, with cohomology in degrees
`[b - (m + 1), b]`. Then `Hᵠ K = 0` for `q > b` and `Hᵇ K` is constructible, so that
`K'' = (Hᵇ K)[-b]` is derived complete and bounded constructible. Hence `K'` is derived complete,
and its reduction `K'₁` is bounded constructible with cohomology in degrees `[b - 1 - m, b - 1]`,
so that `K'` is bounded constructible by the hypothesis `ih`, and so is `K`. -/
lemma boundedConstructible_of_derivedCompleteIntegers_of_triangle [IsNoetherian X] (m : ℕ)
    (ih : ∀ (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (b : ℤ),
      derivedCompleteIntegers ℓ E X K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
        ((derivedReductionComap X ℓ E).obj K) →
      (∀ i, i < b - m ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedReductionComap X ℓ E).obj K))) →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K)
    (T : Triangle (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))) (hT : T ∈ distTriang _)
    (b : ℤ) [T.obj₁.IsLE (b - 1)] [T.obj₃.IsGE b] [T.obj₃.IsLE b]
    (hK : derivedCompleteIntegers ℓ E X T.obj₂)
    (h₁ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj T.obj₂))
    (hb : ∀ i, i < b - (m + 1 : ℕ) ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionComap X ℓ E).obj T.obj₂))) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) T.obj₂ := by
  have hK₃c := boundedConstructible_obj₃_of_isLE_of_isGE T hT b
    (isConstructibleModuleObject_homology_of_derivedCompleteIntegers hK b
      (isZero_homology_of_derivedCompleteIntegers hK _ (hb _ (Or.inr (lt_add_one b)))) h₁)
  refine (boundedConstructible _).ext_of_isTriangulatedClosed₂ T hT
    (ih T.obj₁ (b - 1) ?_ (boundedConstructible_derivedReductionComap_obj₁ T hT h₁
      (boundedConstructible_derivedReductionComap_obj hK₃c))
      (isZero_homology_derivedReductionComap_obj₁ m T hT b inferInstance inferInstance hb)) hK₃c
  exact derivedCompleteIntegers_ext₂ _ (inv_rot_of_distTriang _ hT)
    (derivedCompleteIntegers_shift (derivedCompleteIntegers_obj₃_of_isLE_of_isGE T hT b hK) (-1))
    hK

/-- The inductive step of the integral criterion: apply
`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_triangle` to the truncation triangle
`τ^{≤ b - 1} K ⟶ K ⟶ τ^{≥ b} K ⟶`, where `K` lies in degrees `≤ b` since `Hᵠ K = 0` for
`q > b`. -/
lemma boundedConstructible_of_derivedCompleteIntegers_succ [IsNoetherian X] (m : ℕ)
    (ih : ∀ (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (b : ℤ),
      derivedCompleteIntegers ℓ E X K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
        ((derivedReductionComap X ℓ E).obj K) →
      (∀ i, i < b - m ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedReductionComap X ℓ E).obj K))) →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (b : ℤ)
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj K))
    (hb : ∀ i, i < b - (m + 1 : ℕ) ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionComap X ℓ E).obj K))) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K := by
  have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun q hq ↦
    isZero_homology_of_derivedCompleteIntegers hK q (hb q (Or.inr hq))
  have : ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (sub_add_cancel b 1)).obj
      K).obj₁.IsLE (b - 1) := inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj K) (b - 1))
  have : ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (sub_add_cancel b 1)).obj
      K).obj₃.IsGE b := inferInstanceAs (DerivedCategory.TStructure.t.IsGE
    ((DerivedCategory.TStructure.t.truncGE b).obj K) b)
  have : ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (sub_add_cancel b 1)).obj
      K).obj₃.IsLE b := inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.TStructure.t.truncGE b).obj K) b)
  exact boundedConstructible_of_derivedCompleteIntegers_of_triangle m ih
    ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (sub_add_cancel b 1)).obj K)
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (sub_add_cancel b 1) K) b
    hK h₁ hb

/-- **Descending induction for the integral criterion**: a derived complete `K` whose reduction
`K₁ = 𝔽_{E,X} ⊗ᴸ K` is bounded constructible with cohomology in degrees `[b - n, b]` is bounded
constructible. -/
lemma boundedConstructible_of_derivedCompleteIntegers_of_amplitude [IsNoetherian X] (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (b : ℤ)
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)
      ((derivedReductionComap X ℓ E).obj K))
    (hb : ∀ i, i < b - n ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedReductionComap X ℓ E).obj K))) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K := by
  induction n generalizing K b with
  | zero =>
    have hK₀ (i : ℤ) (hi : i ≠ b) : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) :=
      isZero_homology_of_derivedCompleteIntegers hK i (hb i (lt_sub_natCast_zero_or_lt_of_ne hi))
    refine (mem_boundedConstructible_iff _ K).2
      ⟨⟨b, b, fun i hi ↦ hK₀ i (hi.elim ne_of_lt ne_of_gt)⟩, fun i ↦ ?_⟩
    rcases eq_or_ne i b with rfl | hi
    · exact isConstructibleModuleObject_homology_of_derivedCompleteIntegers hK i
        (hK₀ _ (lt_add_one i).ne') h₁
    · exact isConstructibleModuleObject_of_isZero _ (hK₀ i hi)
  | succ m ih => exact boundedConstructible_of_derivedCompleteIntegers_succ m ih K b hK h₁ hb

/-- Blueprint `proposition-integral-constructibility-criterion` (section `chap-The-pro-etale-site`),
implication (2) ⇒ (1): on a noetherian scheme `X`, a derived complete complex `K` of
`𝒪_{E,X}`-module objects whose first derived reduction `K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` lies in
`Dᵇc(X, 𝔽_E)` is bounded constructible (Bhatt–Scholze, Proposition 6.8.11). -/
theorem boundedConstructible_of_derivedCompleteIntegers {X : Scheme.{u}} [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X ((derivedReduction X ℓ E).obj K)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K := by
  have h₁' := boundedConstructible_comap_derivedExtendScalars_of_derivedReduction K h₁
  obtain ⟨⟨a, b, hab⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 h₁'
  exact boundedConstructible_of_derivedCompleteIntegers_of_amplitude (b - a).toNat K b hK h₁'
    fun i hi ↦ hab i (lt_or_lt_of_lt_sub_toNat_or_lt hi)

end AlgebraicGeometry.ProEtale
