/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Homology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LocallyFinitelyGenerated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits

import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre

/-!
# Constructibility of derived complete sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and uniformizer `ϖ`,
and `X` a noetherian scheme. Let `M` be an `𝒪_{E,X}`-module object on `X_proét` which is derived
complete when placed in degree `0`. If the cokernel of `ϖ` on `M` is constructible and the kernel
of `ϖ` on `M` is a quotient of a constructible module, then `M` is constructible
(`ProEtale.isConstructibleModuleObject_of_derivedCompleteIntegers`; Bhatt–Scholze, *The
pro-étale topology for schemes*, proof of Proposition 6.8.11; blueprint
`proposition-integral-constructibility-criterion`).

## Proof

On each stratum of a common stratification, it suffices to prove that a derived complete `M`
with `M/ϖ` pro-étale locally finitely presented and `M[ϖ]` pro-étale locally finitely generated
is pro-étale locally finitely presented
(`ProEtale.isLocallyFinitelyPresented_of_derivedCompleteIntegers`).

* **Generators** (`ProEtale.isLocallyFinitelyGenerated_of_derivedCompleteIntegers`): if `M/ϖ`
  is pro-étale locally finitely generated, generators of `M/ϖ` lift pro-étale locally to a map
  `ψ : R^r ⟶ M` with `M = im ψ + ϖ M`; its cokernel is derived complete and `ϖ` acts
  surjectively on it, so it vanishes by Nakayama's lemma
  (`ProEtale.epi_of_epi_comp_cokernel_π_padicIntegersCenter`).
* **Relations** (`ProEtale.isLocallyFinitelyPresented_of_epi_of_derivedCompleteIntegers`): for
  `φ : R^r ↠ M` with kernel `N`, the snake lemma for `ϖ` on `0 ⟶ N ⟶ R^r ⟶ M ⟶ 0` gives the
  exact sequence `M[ϖ] ⟶ N/ϖ ⟶ R^r/ϖ ⟶ M/ϖ ⟶ 0`, so `N/ϖ` is pro-étale locally finitely
  generated. As `N` is derived complete, it is pro-étale locally finitely generated, and `M` is
  pro-étale locally finitely presented.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

/-! ### Diagram lemmas -/

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- For an epimorphism `f : X ⟶ Y` and `g : Y ⟶ Z`, the induced morphism
`ker (f ≫ g) ⟶ ker g` is an epimorphism. -/
lemma epi_kernel_lift_kernel_ι_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    Epi (kernel.lift g (kernel.ι (f ≫ g) ≫ f) (by rw [Category.assoc, kernel.condition])) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T x
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi f (x ≫ kernel.ι g)
  refine ⟨T₁, π₁, inferInstance, kernel.lift (f ≫ g) y ?_, ?_⟩
  · rw [← Category.assoc, ← hy, Category.assoc, Category.assoc, kernel.condition, comp_zero,
      comp_zero]
  · rw [← cancel_mono (kernel.ι g), Category.assoc, Category.assoc, kernel.lift_ι,
      kernel.lift_ι_assoc, hy]

namespace ShortComplex.ShortExact

/-- The snake input attached to a morphism `v : S₁ ⟶ S₂` of short exact sequences: its zeroth
and third rows are the kernels and the cokernels of the components of `v`. -/
@[simps]
noncomputable def snakeInput {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (v : S₁ ⟶ S₂) : SnakeInput C where
  L₀ :=
    { f := kernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂
      g := kernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃
      zero := by ext; simp }
  L₁ := S₁
  L₂ := S₂
  L₃ :=
    { f := cokernel.map v.τ₁ v.τ₂ S₁.f S₂.f v.comm₁₂
      g := cokernel.map v.τ₂ v.τ₃ S₁.g S₂.g v.comm₂₃
      zero := by ext; simp }
  v₀₁ :=
    { τ₁ := kernel.ι _
      τ₂ := kernel.ι _
      τ₃ := kernel.ι _ }
  v₁₂ := v
  v₂₃ :=
    { τ₁ := cokernel.π _
      τ₂ := cokernel.π _
      τ₃ := cokernel.π _ }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      exact (KernelFork.isLimitMapConeEquiv _ _).2 (kernelIsKernel _)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel _)
  epi_L₁_g := h₁.epi_g
  mono_L₂_f := h₂.mono_f
  L₁_exact := h₁.exact
  L₂_exact := h₂.exact

end ShortComplex.ShortExact

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-! ### Derived complete module objects -/

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- A module object placed in degree `0` is derived complete if and only if
`1 - ϖ · shift : ∏ₙ M ⟶ ∏ₙ M` is an isomorphism. -/
lemma derivedCompleteIntegers_singleFunctor_iff {X : Scheme.{u}} {ϖ : integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :
    derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M) ↔
      IsIso (𝟙 _ - powShift ((padicIntegersCenter X ℓ E ϖ).app M)) := by
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ]
  exact CatCenter.isCenterComplete_derivedCategory_singleFunctor_iff _ M

/-- Finitely presented module objects are derived complete. -/
lemma derivedCompleteIntegers_singleFunctor_of_isFinitelyPresented {X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hM : Mod.IsFinitelyPresented _ M) :
    derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M) :=
  (derivedCompleteIntegers_singleFunctor_iff hϖ M).2
    (isIso_sub_powShift_padicIntegersCenter_of_isFinitelyPresented _ ℓ E
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ) hM)

/-- The pullback of `𝒪_E`-module objects along a weakly étale morphism preserves countable
products. -/
instance preservesLimitsOfShape_discrete_nat_upperStar_padicIntegers_of_weaklyEtale
    {W X : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g] :
    PreservesLimitsOfShape (Discrete ℕ) ((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) := by
  unfold CondensedRing.upperStar
  infer_instance

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- The pullback along a weakly étale morphism preserves derived complete module objects. -/
lemma derivedCompleteIntegers_singleFunctor_upperStar_of_weaklyEtale {W X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    (g : W ⟶ X) [WeaklyEtale g]
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hM : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M)) :
    derivedCompleteIntegers ℓ E W
      ((DerivedCategory.singleFunctor _ 0).obj
        ((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M)) := by
  rw [derivedCompleteIntegers_singleFunctor_iff hϖ] at hM ⊢
  rw [← upperStar_map_padicIntegersCenter_app, ← isIso_map_sub_powShift_iff]
  infer_instance

/-- **Nakayama's lemma for generators**: let `ψ : F ⟶ A` be a morphism of derived complete
module objects such that `F ⟶ A ⟶ A/ϖ` is an epimorphism. Then `ψ` is an epimorphism: `ϖ` acts
surjectively on the derived complete cokernel of `ψ`. -/
theorem epi_of_epi_comp_cokernel_π_padicIntegersCenter {X : Scheme.{u}} {ϖ : integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {F A : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hF : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj F))
    (hA : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj A))
    (ψ : F ⟶ A) [Epi (ψ ≫ cokernel.π ((padicIntegersCenter X ℓ E ϖ).app A))] : Epi ψ := by
  let z := padicIntegersCenter X ℓ E ϖ
  have hC := derivedCompleteIntegers_singleFunctor_cokernel ψ hF hA
  let S := ShortComplex.mk (z.app A) (cokernel.π (z.app A)) (cokernel.condition _)
  have h₁ : Epi (biprod.desc (𝟙 A ≫ z.app A) ψ) :=
    epi_biprod_desc_of_exact (S := S) (S.exact_of_g_is_cokernel (cokernelIsCokernel _)) (𝟙 A) ψ
  have h₂ : biprod.desc (𝟙 A ≫ z.app A) ψ ≫ cokernel.π ψ =
      biprod.fst ≫ cokernel.π ψ ≫ z.app (cokernel ψ) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.id_comp, biprod.inl_fst_assoc]
      exact (z.naturality (cokernel.π ψ)).symm
    · rw [biprod.inr_desc_assoc, biprod.inr_fst_assoc, cokernel.condition, zero_comp]
  have : Epi ((biprod.fst : A ⊞ F ⟶ A) ≫ cokernel.π ψ ≫ z.app (cokernel ψ)) := by
    rw [← h₂]
    exact epi_comp _ _
  have : Epi (z.app (cokernel ψ)) := by
    rw [← Category.assoc] at this
    exact epi_of_epi ((biprod.fst : A ⊞ F ⟶ A) ≫ cokernel.π ψ) _
  exact Preadditive.epi_of_isZero_cokernel _
    (isZero_of_derivedCompleteIntegers_singleFunctor_of_epi hϖ hC)

/-! ### Generators -/

/-- A derived complete module object `A` such that `A/ϖ` is a quotient of a free module of
finite rank is pro-étale locally finitely generated. -/
theorem isLocallyFinitelyGenerated_of_derivedCompleteIntegers_of_epi {X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {P A : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hP : Mod.IsFree _ P)
    (hA : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj A))
    (p : P ⟶ cokernel ((padicIntegersCenter X ℓ E ϖ).app A)) [Epi p] :
    IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E) A := by
  obtain ⟨𝒰, h𝒰⟩ := exists_cover_lift_of_isFree (cokernel.π _) hP p
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨s, hs⟩ := h𝒰 i
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  let F := (𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
  have hP' := IsFree.upperStar _ (𝒰.f i) hP
  have : Epi (s ≫ cokernel.π ((padicIntegersCenter (𝒰.X i) ℓ E ϖ).app (F.obj A))) := by
    rw [← upperStar_map_padicIntegersCenter_app]
    have h : s ≫ cokernel.π (F.map ((padicIntegersCenter X ℓ E ϖ).app A)) =
        F.map p ≫ inv (cokernelComparison ((padicIntegersCenter X ℓ E ϖ).app A) F) := by
      rw [← hs, IsIso.eq_comp_inv, Category.assoc, π_comp_cokernelComparison]
    rw [h]
    infer_instance
  have : Epi s := epi_of_epi_comp_cokernel_π_padicIntegersCenter hϖ
    (derivedCompleteIntegers_singleFunctor_of_isFinitelyPresented hϖ hP'.isFinitelyPresented)
    (derivedCompleteIntegers_singleFunctor_upperStar_of_weaklyEtale hϖ _ hA) s
  exact hP'.isFinitelyGenerated_of_epi s

/-- **Generators of derived complete module objects**: a derived complete module object `A`
such that `A/ϖ` is pro-étale locally finitely generated is pro-étale locally finitely
generated. -/
theorem isLocallyFinitelyGenerated_of_derivedCompleteIntegers {X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {A : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hA : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj A))
    (h : IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E)
      (cokernel ((padicIntegersCenter X ℓ E ϖ).app A))) :
    IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E) A := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine isLocallyFinitelyGenerated_of_cover 𝒰 fun i ↦ ?_
  obtain ⟨n, p, _⟩ := h𝒰 i
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  let F := (𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
  let e : F.obj (cokernel ((padicIntegersCenter X ℓ E ϖ).app A)) ≅
      cokernel ((padicIntegersCenter (𝒰.X i) ℓ E ϖ).app (F.obj A)) :=
    PreservesCokernel.iso F _ ≪≫ cokernelIsoOfEq (upperStar_map_padicIntegersCenter_app ℓ E ϖ _ A)
  have : Epi (p ≫ e.hom) := epi_comp _ _
  exact isLocallyFinitelyGenerated_of_derivedCompleteIntegers_of_epi hϖ ⟨n, ⟨Iso.refl _⟩⟩
    (derivedCompleteIntegers_singleFunctor_upperStar_of_weaklyEtale hϖ _ hA) (p ≫ e.hom)

/-! ### Relations -/

/-- Let `φ : P ⟶ A` be an epimorphism from a free module of finite rank onto a derived complete
module object `A`, with `A/ϖ` pro-étale locally finitely presented and `A[ϖ]` pro-étale locally
finitely generated. Then `A` is pro-étale locally finitely presented: by the snake lemma for `ϖ`
on `0 ⟶ ker φ ⟶ P ⟶ A ⟶ 0`, the reduction of the derived complete kernel `ker φ` is pro-étale
locally finitely generated, hence so is `ker φ`. -/
theorem isLocallyFinitelyPresented_of_epi_of_derivedCompleteIntegers {X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {P A : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hP : Mod.IsFree _ P) (φ : P ⟶ A) [Epi φ]
    (hA : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj A))
    (h₁ : IsLocallyFinitelyPresented _ (cokernel ((padicIntegersCenter X ℓ E ϖ).app A)))
    (h₂ : IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E)
      (kernel ((padicIntegersCenter X ℓ E ϖ).app A))) :
    IsLocallyFinitelyPresented _ A := by
  let z := padicIntegersCenter X ℓ E ϖ
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel φ) }
  let v : S ⟶ S :=
    { τ₁ := z.app _
      τ₂ := z.app _
      τ₃ := z.app _
      comm₁₂ := (z.naturality _).symm
      comm₂₃ := (z.naturality _).symm }
  let T := hS.snakeInput hS v
  -- the exact sequence `A[ϖ] ⟶ (ker φ)/ϖ ⟶ P/ϖ ⟶ A/ϖ ⟶ 0` of the snake lemma
  let δ : kernel (z.app A) ⟶ cokernel (z.app (kernel φ)) := T.δ
  let f₃ : cokernel (z.app (kernel φ)) ⟶ cokernel (z.app P) :=
    cokernel.map _ _ (kernel.ι φ) (kernel.ι φ) (z.naturality _).symm
  let g₃ : cokernel (z.app P) ⟶ cokernel (z.app A) := cokernel.map _ _ φ φ (z.naturality _).symm
  have hδ : δ ≫ f₃ = 0 := T.δ_L₃_f
  have h₂' : (ShortComplex.mk δ f₃ hδ).Exact := T.L₂'_exact
  have hfg : f₃ ≫ g₃ = 0 := T.L₃.zero
  have h₃' : (ShortComplex.mk f₃ g₃ hfg).Exact := T.L₃_exact
  -- the kernel of `P/ϖ ⟶ A/ϖ` is pro-étale locally finitely generated
  have hJ : IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E) (kernel g₃) := by
    have e : cokernel.π (z.app P) ≫ g₃ = φ ≫ cokernel.π (z.app A) := cokernel.π_desc _ _ _
    have hK := IsLocallyFinitelyGenerated.kernel_of_isFree hP (φ ≫ cokernel.π (z.app A)) h₁
    rw [← e] at hK
    obtain ⟨q, _⟩ : ∃ q : kernel (cokernel.π (z.app P) ≫ g₃) ⟶ kernel g₃, Epi q :=
      ⟨_, epi_kernel_lift_kernel_ι_comp _ _⟩
    exact hK.of_epi q
  -- the reduction of the kernel of `φ` is pro-étale locally finitely generated
  have hQ : IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E)
      (cokernel (z.app (kernel φ))) := by
    let U := ShortComplex.mk δ (kernel.lift g₃ f₃ hfg) (by
      rw [← cancel_mono (kernel.ι g₃), Category.assoc, kernel.lift_ι, hδ, zero_comp])
    let α : U ⟶ ShortComplex.mk δ f₃ hδ :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι _ }
    have hU : U.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 h₂'
    have : Epi U.g := h₃'.epi_kernelLift
    exact IsLocallyFinitelyGenerated.of_exact (S := U) hU h₂ hJ
  have hN := derivedCompleteIntegers_singleFunctor_kernel φ
    (derivedCompleteIntegers_singleFunctor_of_isFinitelyPresented hϖ hP.isFinitelyPresented) hA
  obtain ⟨𝒰, h𝒰⟩ := isLocallyFinitelyGenerated_of_derivedCompleteIntegers hϖ hN hQ
  refine (isLocallyFinitelyPresented_iff A).2 ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, p, _⟩ := h𝒰 i
  let F := (𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
  have hSF := hS.map_of_exact F
  let e : F.obj A ≅ cokernel (p ≫ F.map (kernel.ι φ)) :=
    hSF.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel _) ≪≫
      (cokernelEpiComp p _).symm
  exact (fp_cokernel_of_free _ ⟨n, ⟨Iso.refl _⟩⟩ (IsFree.upperStar _ _ hP)).of_iso e.symm

/-- **Derived complete module objects with finitely presented reduction**: a derived complete
module object `A` such that `A/ϖ` is pro-étale locally finitely presented and `A[ϖ]` is
pro-étale locally finitely generated is pro-étale locally finitely presented. -/
theorem isLocallyFinitelyPresented_of_derivedCompleteIntegers {X : Scheme.{u}}
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {A : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hA : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj A))
    (h₁ : IsLocallyFinitelyPresented _ (cokernel ((padicIntegersCenter X ℓ E ϖ).app A)))
    (h₂ : IsLocallyFinitelyGenerated (Profinite.padicIntegersRingObj ℓ E)
      (kernel ((padicIntegersCenter X ℓ E ϖ).app A))) :
    IsLocallyFinitelyPresented _ A := by
  obtain ⟨𝒰, h𝒰⟩ := isLocallyFinitelyGenerated_of_derivedCompleteIntegers hϖ hA
    h₁.isLocallyFinitelyGenerated
  refine isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦ ?_
  obtain ⟨n, p, _⟩ := h𝒰 i
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  let F := (𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
  have h := upperStar_map_padicIntegersCenter_app ℓ E ϖ (𝒰.f i) A
  exact isLocallyFinitelyPresented_of_epi_of_derivedCompleteIntegers hϖ ⟨n, ⟨Iso.refl _⟩⟩ p
    (derivedCompleteIntegers_singleFunctor_upperStar_of_weaklyEtale hϖ _ hA)
    ((IsLocallyFinitelyPresented.upperStar _ _ h₁).of_iso
      (PreservesCokernel.iso F _ ≪≫ cokernelIsoOfEq h))
    ((h₂.upperStar _).of_iso (PreservesKernel.iso F _ ≪≫ kernelIsoOfEq h))

/-! ### Constructibility -/

/-- **Constructibility of derived complete sheaves** (Bhatt–Scholze, proof of
Proposition 6.8.11; blueprint `proposition-integral-constructibility-criterion`): on a noetherian
scheme `X`, let `M` be an `𝒪_{E,X}`-module object which is derived complete when placed in degree
`0`, such that the cokernel of a uniformizer `ϖ` on `M` is constructible and the kernel of `ϖ` on
`M` is a quotient of a constructible module object. Then `M` is constructible. -/
theorem isConstructibleModuleObject_of_derivedCompleteIntegers {X : Scheme.{u}} [IsNoetherian X]
    {ϖ : integers ℓ E} (hϖ : IsLocalRing.maximalIdeal (integers ℓ E) = Ideal.span {ϖ})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hM : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M))
    (h₁ : IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (cokernel ((padicIntegersCenter X ℓ E ϖ).app M)))
    {C : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hC : IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) C)
    (f : C ⟶ kernel ((padicIntegersCenter X ℓ E ϖ).app M)) [Epi f] :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) M := by
  obtain ⟨S, hS⟩ := common_lfp_stratification h₁ hC
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff _ (S.immersion a) M).2 ?_⟩
  have : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  have : QuasiSeparatedSpace (S.domain a) :=
    ⟨fun _ _ _ _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let F := (S.immersion a)^*⟦Profinite.padicIntegersRingObj ℓ E⟧
  have h := upperStar_map_padicIntegersCenter_app ℓ E ϖ (S.immersion a) M
  have : Epi (F.map f) := inferInstance
  exact isLocallyFinitelyPresented_of_derivedCompleteIntegers hϖ
    (derivedCompleteIntegers_of_iso (derivedCompleteIntegers_leftDerivedUpperStar_obj _ hM)
      (leftDerivedUpperStarSingleFunctorIso _ _ M 0))
    (((isLocallyFinitelyPresented_mapMod_iff _ _ _).1 (hS a).1).of_iso
      (PreservesCokernel.iso F _ ≪≫ cokernelIsoOfEq h))
    (((((isLocallyFinitelyPresented_mapMod_iff _ _ _).1
      (hS a).2).isLocallyFinitelyGenerated).of_epi (F.map f)).of_iso
      (PreservesKernel.iso F _ ≪≫ kernelIsoOfEq h))

end AlgebraicGeometry.ProEtale
