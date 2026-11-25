/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RowAdditivity
public import WeilConjectures.TraceFormula.SupportedClassNaturality

/-!

# Additivity of trace classes along a distinguished triangle

Let `c` be an endocorrespondence of `(X, K)` and `K' ⟶ K ⟶ K'' ⟶ K'⟦1⟧` a distinguished triangle
with coefficient maps `u'`, `u''` on `K'`, `K''` on the support of `c` forming, with `u`, a
morphism of the triangles `Lc₂^* (-)` and `Rc₁^! (-)`. If the corner morphism groups vanish

* `Rc_! ℚ̄_ℓ ⟶ (K'' ⊠ D K')⟦-1⟧`, `K' ⊠ D K ⟶ (K'' ⊠ D K')⟦-1⟧`, `K ⊠ D K'' ⟶ (K'' ⊠ D K')⟦-1⟧`,
* `(K' ⊠ D K'')⟦1⟧ ⟶ RΔ_* ω_X`,

then the trace classes are additive, `Tr_c(u) = Tr_c(u') + Tr_c(u'')`
(`ProEtale.CondensedRing.Correspondence.traceClass_eq_add_of_distTriang`). For an open–closed
triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K` along a `c`-invariant closed subscheme these groups vanish
by support considerations (`WeilConjectures.TraceFormula.PieceVanishing`), which gives the
additivity of blueprint `proposition-additivity-trace-classes--2` and
`proposition-additivity-trace-classes--2`.

The proof writes `Tr_c(u)` as the image of `e_K ∘ ũ` (evaluation kernel and supported class,
`Correspondence.traceClass_eq_traceClassOfKernel`) and applies the triangulated lemma
`CategoryTheory.Pretriangulated.comp_eq_add_of_distTriang` to the three rows
`K' ⊠ N ⟶ K ⊠ N ⟶ K'' ⊠ N` for `N = D K, D K', D K''`, with the dinaturality of the evaluation
kernel and the naturality of the supported classes. This replaces Varshavsky's filtered argument
(Prop. 1.5.10, after SGA 5, III 4.13).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The Verdier dual of a composite which vanishes vanishes. -/
lemma verdierDualMap_comp_eq_zero
    {K₁ K₂ K₃ : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {f : K₁ ⟶ K₂} {g : K₂ ⟶ K₃}
    (h : f ≫ g = 0) : verdierDualMap ℓ g ≫ verdierDualMap ℓ f = 0 := by
  rw [verdierDualMap, verdierDualMap, ← NatTrans.comp_app, ← pre_map, h]
  apply uncurry_injective
  rw [uncurry_pre, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, uncurry_eq,
    MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp]

/-- `M ⊠ -` of a vanishing composite vanishes. -/
lemma externalProductMap_id_comp_eq_zero {M N N' N'' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {g : N ⟶ N'} {g' : N' ⟶ N''} (h : g ≫ g' = 0) :
    externalProductMap ℓ (𝟙 M) g ≫ externalProductMap ℓ (𝟙 M) g' = 0 := by
  rw [← externalProductMap_comp, h, externalProductMap_zero_right]

/-- The external product `- ⊠ N` of a distinguished triangle is distinguished. -/
lemma externalProduct_distTriang {K' K K'' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ε : K' ⟶ K} {η : K ⟶ K''} {δ : K'' ⟶ K'⟦(1 : ℤ)⟧} (hT : Triangle.mk ε η δ ∈ distTriang _)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ δ', Triangle.mk (externalProductMap ℓ ε (𝟙 N)) (externalProductMap ℓ η (𝟙 N)) δ' ∈
      distTriang _ := by
  have := (externalProductLeft ℓ X N).map_distinguished _ hT
  simp only [Functor.mapTriangle_obj, Triangle.mk_mor₁, Triangle.mk_mor₂,
    externalProductLeft_map] at this
  exact ⟨_, this⟩

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- **Additivity of trace classes along a distinguished triangle** (blueprint
`proposition-additivity-trace-classes--2`, `proposition-additivity-trace-classes`): see the module
docstring. -/
theorem traceClass_eq_add_of_distTriang (F : c.FixedLocus)
    {K' K'' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {ε : K' ⟶ K} {η : K ⟶ K''}
    {δ : K'' ⟶ K'⟦(1 : ℤ)⟧} (hT : Triangle.mk ε η δ ∈ distTriang _)
    (u' : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K')
    (u'' : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K'' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K'')
    (hu' : (boundedConstructibleUpperStar _ ℓ c.c₂).map ε ≫ c.u =
      u' ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map ε)
    (hu'' : (boundedConstructibleUpperStar _ ℓ c.c₂).map η ≫ u'' =
      c.u ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map η)
    (h₁ : ∀ φ : (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (externalProduct ℓ K'' (verdierDual ℓ K')) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₂ : ∀ φ : externalProduct ℓ K' (verdierDual ℓ K) ⟶
      (externalProduct ℓ K'' (verdierDual ℓ K')) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₃ : ∀ φ : externalProduct ℓ K (verdierDual ℓ K'') ⟶
      (externalProduct ℓ K'' (verdierDual ℓ K')) ⟦(-1 : ℤ)⟧, φ = 0)
    (h₄ : ∀ φ : (externalProduct ℓ K' (verdierDual ℓ K'')) ⟦(1 : ℤ)⟧ ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X), φ = 0) :
    c.traceClass F = F.traceClassWithCoeff K' u' + F.traceClassWithCoeff K'' u'' := by
  refine (traceClass_eq_traceClassOfKernel c F).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· + ·)
    (FixedLocus.traceClassWithCoeff_eq F K' u').symm
    (FixedLocus.traceClassWithCoeff_eq F K'' u'').symm)
  refine (congrArg F.traceClassOfKernel ?_).trans (map_add F.traceClassOfKernel _ _)
  have hεη : ε ≫ η = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hDcomp := verdierDualMap_comp_eq_zero (X := X) hεη
  have hfP := externalProductMap_exchange (X := X) (Y := X) ℓ ε (verdierDualMap ℓ ε)
  have hfR := externalProductMap_exchange (X := X) (Y := X) ℓ η (verdierDualMap ℓ ε)
  have hgR := externalProductMap_exchange (X := X) (Y := X) ℓ η (verdierDualMap ℓ η)
  have hgfQ := externalProductMap_id_comp_eq_zero (X := X) (M := K) hDcomp
  have hgfR := externalProductMap_id_comp_eq_zero (X := X) (M := K'') hDcomp
  have he₁ : externalProductMap ℓ ε (𝟙 _) ≫ evaluationKernel ℓ K =
      externalProductMap ℓ (𝟙 K') (verdierDualMap ℓ ε) ≫ evaluationKernel ℓ K' :=
    externalProductMap_comp_evaluationKernel (X := X) ℓ ε
  have he₂ : externalProductMap ℓ (𝟙 K) (verdierDualMap ℓ η) ≫
        evaluationKernel ℓ K =
      externalProductMap ℓ η (𝟙 _) ≫ evaluationKernel ℓ K'' :=
    (externalProductMap_comp_evaluationKernel (X := X) ℓ η).symm
  have hσ₁ : c.supportedClass ≫ externalProductMap ℓ (𝟙 K) (verdierDualMap ℓ ε) =
      c.supportedClassOfCoeff K' K' u' ≫ externalProductMap ℓ ε (𝟙 _) := by
    rw [← supportedClassOfCoeff_u, ← supportedClassOfCoeff_upperStar_map_comp, hu',
      supportedClassOfCoeff_comp_upperShriek_map]
  have hσ₂ : c.supportedClass ≫ externalProductMap ℓ η (𝟙 _) =
      c.supportedClassOfCoeff K'' K'' u'' ≫
        externalProductMap ℓ (𝟙 K'') (verdierDualMap ℓ η) := by
    rw [← supportedClassOfCoeff_u, ← supportedClassOfCoeff_comp_upperShriek_map, ← hu'',
      supportedClassOfCoeff_upperStar_map_comp]
  obtain ⟨_, h₀⟩ := externalProduct_distTriang (X := X) (ℓ := ℓ) hT (verdierDual ℓ K)
  obtain ⟨_, h₁'⟩ := externalProduct_distTriang (X := X) (ℓ := ℓ) hT (verdierDual ℓ K')
  obtain ⟨_, h₂'⟩ := externalProduct_distTriang (X := X) (ℓ := ℓ) hT (verdierDual ℓ K'')
  exact comp_eq_add_of_distTriang h₀ h₁' h₂' _ _ _ _ _
    hfP hfR hgR hgfQ hgfR _ _ _ he₁ he₂ _ _ _ hσ₁ hσ₂ h₁ h₂ h₃ h₄

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
