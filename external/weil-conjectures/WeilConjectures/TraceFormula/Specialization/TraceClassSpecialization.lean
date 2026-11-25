/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Specialization of the trace class

Let `T` be specialization data from a correspondence `c` of `(X, K)` with fixed locus `F` to a
correspondence `c'` of `(X', K')` with fixed locus `F'`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization`). Let `P = K ⊠ D_X K` and
`P' = K' ⊠ D_{X'} K'` be the universal kernels and let `ρ : Ψ_{X×X} P ⟶ P'` be a comparison
satisfying the second universal-kernel identity `e_{K'} ρ = RΔ'_* θ_X ∘ χ_Δ ∘ Ψ_{X×X}(e_K)`
(blueprint `lemma-nearby-cycles-universal-kernel`). If the coefficient map of `c'` is the
specialization of that of `c`, in the sense that its kernel section is
`k_{u_s} = c'^! ρ ∘ β_c ∘ Ψ_C(k_u) ∘ σ_C` (blueprint `lemma-section-specialized-correspondence`),
then the trace class of `c'` is the specialization of the trace class of `c` (blueprint
`proposition-specialization-trace-class`):
```
Tr_{c'}(u_s) = sp_F(Tr_c(u)).
```

## Main results

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.sp_traceClass_eq_traceClass`:
  `sp_F(Tr_c(u)) = Tr_{c'}(u')` when the kernel section of `u'` is the specialized kernel section
  of `u`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

namespace TraceSpecialization

variable (T : c.TraceSpecialization F c' F')

/-- The diagram chase behind `sp_traceClass_eq_traceClass`, in an arbitrary category. -/
private lemma comp_eq_of_kernel {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ A₁₂ : 𝒞} (σ : A₀ ⟶ A₁) (m : A₁ ⟶ A₂)
    (v : A₂ ⟶ A₃) (β : A₃ ⟶ A₄) (pe : A₄ ⟶ A₅) (χ : A₅ ⟶ A₆) (Δθ : A₆ ⟶ A₇) (b : A₆ ⟶ A₈)
    (dθ : A₈ ⟶ A₉) (cmp : A₉ ⟶ A₁₀) (dθcmp : A₈ ⟶ A₁₀) (r : A₄ ⟶ A₁₁) (e' : A₁₁ ⟶ A₇)
    (b' : A₇ ⟶ A₉) (m' : A₀ ⟶ A₁₂) (v' : A₁₂ ⟶ A₁₁)
    (hu : σ ≫ (m ≫ v) ≫ β ≫ r = m' ≫ v') (hρ : r ≫ e' = pe ≫ χ ≫ Δθ)
    (hB : Δθ ≫ b' = b ≫ dθ) (hd : dθcmp = dθ ≫ cmp) :
    σ ≫ m ≫ v ≫ β ≫ pe ≫ χ ≫ b ≫ dθcmp = m' ≫ v' ≫ e' ≫ b' ≫ cmp := by
  simp only [Category.assoc] at hu
  rw [hd, ← reassoc_of% hu, reassoc_of% hρ, reassoc_of% hB]

/-- **Specialization of the trace class** (blueprint `proposition-specialization-trace-class`):
let `ρ : Ψ_{X×X}(K ⊠ D_X K) ⟶ K' ⊠ D_{X'} K'` be a comparison of the universal kernels satisfying
the second universal-kernel identity `e_{K'} ρ = RΔ'_* θ_X ∘ χ_Δ ∘ Ψ_{X×X}(e_K)` (blueprint
`lemma-nearby-cycles-universal-kernel`), and suppose that the kernel section
`k_{u'} = λ_{c'} ũ' : ℚ̄_ℓ ⟶ Rc'^!(K' ⊠ D K')` of the coefficient map of `c'` is the specialization
`c'^! ρ ∘ β_c ∘ Ψ_C(k_u) ∘ σ_C` of the kernel section of `u` (blueprint
`lemma-section-specialized-correspondence`). Then `Tr_{c'}(u') = sp_F(Tr_c(u))`.

The proof combines `sp_traceClass` and `traceMap_specialization` with the naturality of the
fixed-square base change `B'` in the dualizing map `θ_X`. -/
theorem sp_traceClass_eq_traceClass
    (ρ : T.ΨXX.obj (externalProduct ℓ K (verdierDual ℓ K)) ⟶
      externalProduct ℓ K' (verdierDual ℓ K'))
    (hρ : ρ ≫ evaluationKernel ℓ K' = T.ΨXX.map (evaluationKernel ℓ K) ≫ T.χΔ.app _ ≫
      (boundedConstructibleLowerStar ℓ (diag X')).map T.θX)
    (hu : T.σC ≫ T.ΨC.map (c.mate ≫ c.verdierDualityIso.hom) ≫ T.βc.app _ ≫
      (boundedConstructibleUpperShriek ℓ c'.support).map ρ =
        c'.mate ≫ c'.verdierDualityIso.hom) :
    T.sp (c.traceClass F) = c'.traceClass F' := by
  have hB : (boundedConstructibleUpperShriek ℓ c'.support).map
      ((boundedConstructibleLowerStar ℓ (diag X')).map T.θX) ≫
        (F'.upperShriekLowerStarIso.app (dualizingComplex' ℓ X')).hom =
      (F'.upperShriekLowerStarIso.app (T.ΨX.obj (dualizingComplex' ℓ X))).hom ≫
        (boundedConstructibleLowerStar ℓ F'.ι).map
          ((boundedConstructibleUpperShriek ℓ F'.d).map T.θX) :=
    F'.upperShriekLowerStarIso.hom.naturality T.θX
  have hρ' := ((boundedConstructibleUpperShriek ℓ c'.support).map_comp _ _).symm.trans
    ((congrArg (boundedConstructibleUpperShriek ℓ c'.support).map hρ).trans
      (((boundedConstructibleUpperShriek ℓ c'.support).map_comp _ _).trans
        (congrArg (_ ≫ ·) ((boundedConstructibleUpperShriek ℓ c'.support).map_comp _ _))))
  have hu' := hu
  rw [T.ΨC.map_comp] at hu'
  rw [T.sp_traceClass, T.traceMap_specialization, traceClass_eq]
  refine congrArg
    (_ ≫ ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F'.ι).homEquiv _ _).symm ·) ?_
  exact comp_eq_of_kernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu' hρ' hB
    ((boundedConstructibleLowerStar ℓ F'.ι).map_comp _ _)

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
