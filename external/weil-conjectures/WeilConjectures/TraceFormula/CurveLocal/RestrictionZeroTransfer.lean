/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.PowIntersection
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.NumberTheory.Padics.IntegersToAlgCl
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZero
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.AlgebraicGeometry.OverPullbackFiniteType
public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.AdicSystem
public import WeilConjectures.TraceFormula.FixedPointScheme
public import WeilConjectures.TraceFormula.Correspondence

/-!

# From finite coefficients to `ℚ̄_ℓ`: an integral vanishing criterion

Blueprint `lemma-vanishing-local-term-zero-stalk` is proved on the classical étale models with
finite `ℓ`-primary coefficients
(`AlgebraicGeometry.Etale.CurveLocalModel.sectionsWithSupportRestriction_eq_zero`,
packaged for all models and coefficient rings as
`AlgebraicGeometry.Etale.CurveLocalModel.restrictionZero`). Its last step, as in the blueprint
proof ("the comparison theorems transport this identity back to the proétale formulation"),
transports this vanishing to the `ℚ̄_ℓ`-coefficient pro-étale supported restriction `ρ_P` of
`Correspondence.FixedLocus.supportedRestriction`. This is the passage `ℚ̄_ℓ = colim_E E`,
`E = 𝒪_E[1/ℓ]`, `𝒪_E = lim_n 𝒪_E / ℓ^n`. This file proves the last part of that passage:

* a morphism `ρ` of the point category `Dᵇc(s)⟦ℚ̄_ℓ⟧` *has an integral model reducing to
  classical supported restrictions* on a strictly local model if `Fib_s(ρ) ≅ ℚ̄_ℓ ⊗ᴸ f₀` for a
  morphism `f₀` of perfect `𝒪_E`-complexes whose reductions modulo every `ℓ^n` factor through
  classical supported restrictions `ρ_{a,b}` with finite coefficients
  (`Correspondence.HasIntegralReductionModel`);
* such a morphism vanishes: the reductions vanish by the classical computation, so `f₀` is
  divisible by every `ℓ^n`, hence zero by the Krull intersection theorem, and so is `ρ`, the
  fibre functor of the point being faithful (`Correspondence.eq_zero_of_hasIntegralReductionModel`).

That the stalk of `ρ_P` at a Frobenius fixed point has such an integral model, on the strictly
local model at the fixed point (`Correspondence.frobeniusLocalModel`), needs the comparison
theorems of the six-functor formalism (`proposition-six-operations-change-coefficients`,
`sk-thm-sf-package`, `theorem-bounded-below-cohomology-comparison`) for the condensed coefficients,
which are not formalized yet.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale.CurveLocalModel

variable (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ)

/-- **The supported restriction is zero for Frobenius, for all models and coefficient rings**
(blueprint `lemma-vanishing-local-term-zero-stalk`): for every strictly local model of a smooth
curve over `k`, every finite commutative `ℓ`-primary ring `Λ`, all `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`, the supported restriction `ρ_{a,b}` is zero. -/
def RestrictionZero : Prop :=
  ∀ (M : CurveLocalModel k) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ],
    (∃ n : ℕ, (ℓ : Λ) ^ n = 0) →
    ∀ (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X L →
      DerivedCategory.boundedConstructibleFiniteTor Λ M.X K →
      IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K) →
      ∀ (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
          (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) →
        sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB
          M.openComplement_yB_le P = 0

variable {k ℓ}

/-- `RestrictionZero` holds for every prime `ℓ` invertible in `k` (blueprint
`lemma-vanishing-local-term-zero-stalk`). -/
theorem restrictionZero [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : RestrictionZero k ℓ :=
  fun M _ _ _ hΛ L K hL hK hKy P eP ↦
    M.sectionsWithSupportRestriction_eq_zero ℓ hℓ hΛ L K hL hK hKy P eP


variable (ℓ) in
/-- **Classical coefficient data on a strictly local model**: a finite `ℓ`-primary coefficient
ring `Λ`, complexes `L, K ∈ D^b_{ctf}(X, Λ)` with `K_ȳ = 0`, and a model `P` of `(L ⊠ K)|_T` on
the strict localization, as in `RestrictionZero`. -/
structure CoefficientDatum (M : CurveLocalModel k) where
  /-- The coefficient ring. -/
  Λ : Type (u + 1)
  [commRing : CommRing Λ]
  [finite : Finite Λ]
  isNilpotent_natCast : ∃ n : ℕ, (ℓ : Λ) ^ n = 0
  /-- The first factor. -/
  L : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The second factor, with vanishing stalk at `y`. -/
  K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  boundedConstructibleFiniteTor_L : DerivedCategory.boundedConstructibleFiniteTor Λ M.X L
  boundedConstructibleFiniteTor_K : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K
  isZero_upperStar_y : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)
  /-- A model of `(L ⊠ K)|_T`. -/
  P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The identification `P ≅ (L ⊠ K)|_T`. -/
  iso : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
    (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)

attribute [instance] CoefficientDatum.commRing CoefficientDatum.finite

namespace CoefficientDatum

variable {M : CurveLocalModel k} (D : M.CoefficientDatum ℓ)

/-- The sections with support `RΓ_a(T, P)` on the graph. -/
noncomputable abbrev source : DerivedCategory (ModuleCat.{u + 1} D.Λ) :=
  ((sectionsWithSupportTriangle (ModuleCat.{u + 1} D.Λ) M.a).obj D.P).obj₁

/-- The local cohomology `RΓ_y(B, b^* P)` on the diagonal. -/
noncomputable abbrev target : DerivedCategory (ModuleCat.{u + 1} D.Λ) :=
  ((sectionsWithSupportTriangle (ModuleCat.{u + 1} D.Λ) M.yB).obj
    ((Functor.mapDerivedCategoryPlus (M.b)^*[ModuleCat.{u + 1} D.Λ]).obj D.P)).obj₁

/-- The classical supported restriction `ρ_{a,b} : RΓ_a(T, P) ⟶ RΓ_y(B, b^* P)` of the datum. -/
noncomputable abbrev supportedRestriction : D.source ⟶ D.target :=
  sectionsWithSupportRestriction (ModuleCat.{u + 1} D.Λ) M.b M.a M.yB M.openComplement_yB_le D.P

/-- The classical supported restriction of a coefficient datum vanishes when `RestrictionZero`
holds. -/
lemma supportedRestriction_eq_zero (h : RestrictionZero k ℓ) : D.supportedRestriction = 0 :=
  h M D.Λ D.isNilpotent_natCast D.L D.K D.boundedConstructibleFiniteTor_L
    D.boundedConstructibleFiniteTor_K D.isZero_upperStar_y D.P D.iso

end CoefficientDatum

end AlgebraicGeometry.Etale.CurveLocalModel

namespace CategoryTheory

/-- In an `R`-linear category, composing with `(ℓ : ℤ)^n • 𝟙` is the multiplication by the image
`(ℓ : R)^n`. -/
lemma Linear.comp_zsmul_natCast_pow_id {R : Type*} [CommRing R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] {X Y : C} (g : X ⟶ Y) (ℓ n : ℕ) :
    g ≫ (((ℓ : ℤ) ^ n) • 𝟙 Y) = ((ℓ : R) ^ n) • g := by
  rw [Preadditive.comp_zsmul, Category.comp_id, ← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

open PadicAlgCl

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The fixed point `x = ι(z)` of `Φ_m` underlying a point `z` of the fixed locus of the graph
correspondence `(𝟙, Φ_m)`. -/
lemma comp_ι_comp_frobeniusIterate {m : ℕ}
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    (z ≫ F.ι) ≫ frobeniusIterate Φ m = z ≫ F.ι := by
  rw [Category.assoc]
  exact (congrArg (z ≫ ·) F.w).symm.trans (congrArg (z ≫ ·) (Category.comp_id F.ι))

/-- The classical strictly local model (`AlgebraicGeometry.Etale.CurveLocalModel.ofModelFrobenius`)
at the fixed point `x = ι(z)` of `Φ_m` underlying a point `z` of the fixed locus of `(𝟙, Φ_m)`. -/
noncomputable abbrev frobeniusLocalModel [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom]
    (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (z : RationalPoint F.F) :
    Etale.CurveLocalModel k :=
  Etale.CurveLocalModel.ofModelFrobenius hΦ hm (z ≫ F.ι) (comp_ι_comp_frobeniusIterate v F z)

variable (ℓ) in
/-- A morphism `ρ` of the point category `Dᵇc(s)⟦ℚ̄_ℓ⟧` *has an integral model reducing to
classical supported restrictions on the strictly local model `M`* if there is a morphism
`f₀ : A₀ ⟶ B₀` of perfect `𝒪_E`-complexes with `Fib_s(ρ) ≅ ℚ̄_ℓ ⊗ᴸ f₀` (as arrows) such that for
every `n` there are classical coefficient data on `M` (with coefficients `Λ`, a ring under
`𝒪_E`) for which `f₀` followed by the reduction `B₀ ⟶ B₀ / ℓ^n` (part of a distinguished triangle
on the multiplication by `ℓ^n`) is the reduction `A₀ ⟶ RΓ_a(T, P)` followed by the classical
supported restriction `ρ_{a,b}`, read in `D(𝒪_E)`. -/
def HasIntegralReductionModel [IsAlgClosed k] (M : Etale.CurveLocalModel k)
    (E : FiniteIntermediateField ℓ) {A B : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ρ : A ⟶ B) : Prop :=
  ∃ (A₀ B₀ : DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1))))
    (f₀ : A₀ ⟶ B₀),
    A₀.IsPerfect ∧ B₀.IsPerfect ∧
    Nonempty (Arrow.mk ((pointFiberFunctor ℓ k).map ρ) ≅
      Arrow.mk ((ModuleCat.derivedExtendScalars (PadicAlgCl.integersToULift.{u} ℓ E.1)
        (PadicAlgCl.flat_integersToULift ℓ E.1)).map f₀)) ∧
    ∀ n : ℕ, ∃ (D : M.CoefficientDatum ℓ)
      (φ : Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1) →+* D.Λ)
      (πA : A₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.source)
      (πB : B₀ ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target)
      (δ : (ModuleCat.restrictScalars φ).mapDerivedCategory.obj D.target ⟶ B₀⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 B₀) πB δ ∈ distTriang _ ∧
      πA ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map D.supportedRestriction =
        f₀ ≫ πB

/-- **Integral vanishing criterion**: if `RestrictionZero` holds, a morphism of the point category
with an integral model reducing to classical supported restrictions vanishes. The reductions of
the integral model `f₀` modulo every `ℓ^n` vanish, so `f₀` is divisible by every `ℓ^n`, hence
zero by the Krull intersection theorem (`DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul`);
the fibre functor of the point is faithful. -/
lemma eq_zero_of_hasIntegralReductionModel [IsAlgClosed k] {M : Etale.CurveLocalModel k}
    {E : FiniteIntermediateField ℓ} {A B : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ρ : A ⟶ B} (H : HasIntegralReductionModel ℓ M E ρ)
    (hRZ : Etale.CurveLocalModel.RestrictionZero k ℓ) : ρ = 0 := by
  obtain ⟨A₀, B₀, f₀, hA, hB, ⟨eArr⟩, hred⟩ := H
  have hf₀ : f₀ = 0 := by
    refine DerivedCategory.IsPerfect.eq_zero_of_forall_eq_pow_smul hA hB
      (PadicAlgCl.natCast_mem_maximalIdeal_shrink ℓ E.1) fun n ↦ ?_
    have hn := hred n
    obtain ⟨D, hn⟩ := hn
    obtain ⟨φ, hn⟩ := hn
    obtain ⟨πA, πB, δ, hn⟩ := hn
    obtain ⟨hT, hcomm⟩ := hn
    have h0 := D.supportedRestriction_eq_zero hRZ
    simp only [h0, Functor.map_zero, Limits.comp_zero] at hcomm
    have hex := Pretriangulated.Triangle.coyoneda_exact₂ _ hT f₀ hcomm.symm
    refine ⟨hex.choose, hex.choose_spec.trans ?_⟩
    exact Linear.comp_zsmul_natCast_pow_id hex.choose ℓ n
  have : (pointFiberFunctor ℓ k).Additive := by unfold pointFiberFunctor; infer_instance
  have : (pointFiberFunctor ℓ k).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  apply (bijective_pointFiberFunctor_map ℓ k _ _).1
  have hw := eArr.hom.w
  simp only [Arrow.mk_hom, hf₀, Functor.map_zero, Limits.comp_zero] at hw
  simp only [Functor.map_zero]
  have hr : eArr.hom.right ≫ eArr.inv.right = 𝟙 _ := by
    rw [← Arrow.comp_right, Iso.hom_inv_id, Arrow.id_right]
  calc (pointFiberFunctor ℓ k).map ρ
      = ((pointFiberFunctor ℓ k).map ρ ≫ eArr.hom.right) ≫ eArr.inv.right := by
        rw [Category.assoc, hr]; exact (Category.comp_id _).symm
    _ = 0 := by rw [← hw, Limits.zero_comp]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
