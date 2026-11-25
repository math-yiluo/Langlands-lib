/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageConnectingNaturality
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageTransition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StalkColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.CommShiftPlus
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Dimension shifting for systems of stages

Let `𝒮` be a cofiltered system of stages (`AlgebraicGeometry.Etale.LimitStageSystem`). Say that
`𝒮` is a *stalkwise colimit* at a complex `K` in degree `q` if on every geometric stalk of the
base, `H^q` of the limit stage at `K` is the elementwise colimit of `H^q` of the stages
(`AlgebraicGeometry.Etale.LimitStageSystem.IsStalkColimit`).

If the pullbacks of injective sheaves along the maps `w` of the stages are injective (for
instance if all the `w` are identities), then being a stalkwise colimit in degree `0` at every
injective sheaf implies being a stalkwise colimit in every degree at every sheaf
(`AlgebraicGeometry.Etale.LimitStageSystem.isStalkColimit_of_injective`): by dimension shifting
along `0 ⟶ G ⟶ I ⟶ Q ⟶ 0`, the transition maps being compatible with the connecting maps of
the long exact sequences since they commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I] (𝒮 : LimitStageSystem B W I)

/-- The system `𝒮` is a *stalkwise colimit* at `K` in degree `q`: on every geometric stalk of
the base, `H^q` of the limit stage is the elementwise colimit of `H^q` of the stages. -/
def IsStalkColimit (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (q : ℤ) : Prop :=
  ∀ x : B, ModuleCat.IsElementwiseColimit
    (fun i ↦ (stalkHomology Λ q x).obj ((LimitStage.functor Λ (𝒮.obj i)).obj K))
    ((stalkHomology Λ q x).obj ((LimitStage.functor Λ 𝒮.pt).obj K))
    (fun i ↦ (stalkHomology Λ q x).map ((LimitStage.transition Λ (𝒮.π i)).app K))
    (fun f ↦ (stalkHomology Λ q x).map ((LimitStage.transition Λ (𝒮.map f)).app K))

variable [IsCofiltered I]

/-- A stalkwise colimit system gives a colimit cocone of sheaves. -/
noncomputable def isColimitOfIsStalkColimit
    {K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {q : ℤ}
    (h : 𝒮.IsStalkColimit Λ K q) : IsColimit (𝒮.cocone Λ K q) :=
  isColimitOfIsElementwiseColimit _ h

variable {Λ}

/-- A system all of whose `H^q` vanish is a stalkwise colimit in degree `q`. -/
lemma isStalkColimit_of_isZero
    {K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {q : ℤ}
    (hi : ∀ i, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((LimitStage.functor Λ (𝒮.obj i)).obj K)))
    (hpt : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((LimitStage.functor Λ 𝒮.pt).obj K))) :
    𝒮.IsStalkColimit Λ K q := by
  intro x
  refine ⟨fun b ↦ ⟨IsCofiltered.nonempty.some, 0, ?_⟩, fun i a _ ↦ ⟨i, 𝟙 i, ?_⟩⟩
  · rw [map_zero, ModuleCat.eq_zero_of_isZero
      (Functor.map_isZero (B.uliftPointSmallEtale x).sheafFiber hpt) b]
  · rw [ModuleCat.eq_zero_of_isZero
      (Functor.map_isZero (B.uliftPointSmallEtale x).sheafFiber (hi i)) a, map_zero]

/-- The dimension-shifting step: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with
`H^{n+1}` vanishing at `X₂`, a stalkwise colimit in degree `n` at `X₂` and at `X₃` gives a
stalkwise colimit in degree `n + 1` at `X₁`. -/
lemma isStalkColimit_succ {E : ShortComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : E.ShortExact) (n : ℤ)
    (hi : ∀ i, IsZero ((DerivedCategory.Plus.homologyFunctor _ (n + 1)).obj
      ((LimitStage.functor Λ (𝒮.obj i)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂))))
    (hpt : IsZero ((DerivedCategory.Plus.homologyFunctor _ (n + 1)).obj
      ((LimitStage.functor Λ 𝒮.pt).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂))))
    (h' : 𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂) n)
    (h'' : 𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₃) n) :
    𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₁) (n + 1) := by
  obtain ⟨δ, hT⟩ := hE.exists_mk_singleTrianglePlus_distinguished
  have hsurj (α : LimitStage B W) (hα : IsZero ((DerivedCategory.Plus.homologyFunctor _ (n + 1)).obj
      ((LimitStage.functor Λ α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂))))
      (x : B) : Function.Surjective ((B.uliftPointSmallEtale x).sheafFiber.map
        (LimitStage.connecting Λ δ α n (n + 1) rfl)).hom := fun y ↦
    LimitStage.exists_of_stalk_exact₁ δ hT α n (n + 1) rfl x y (ModuleCat.eq_zero_of_isZero
      (Functor.map_isZero (B.uliftPointSmallEtale x).sheafFiber hα) _)
  intro x
  refine ModuleCat.IsElementwiseColimit.of_cokernel
    (fun i ↦ (stalkHomology Λ n x).map ((LimitStage.functor Λ (𝒮.obj i)).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g)))
    ((stalkHomology Λ n x).map ((LimitStage.functor Λ 𝒮.pt).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.g)))
    (fun i ↦ (B.uliftPointSmallEtale x).sheafFiber.map
      (LimitStage.connecting Λ δ (𝒮.obj i) n (n + 1) rfl))
    ((B.uliftPointSmallEtale x).sheafFiber.map (LimitStage.connecting Λ δ 𝒮.pt n (n + 1) rfl))
    (fun i ↦ ?_) (fun i ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_)
    (fun f g ↦ ?_) (fun i y ↦ ?_) (fun y hy ↦ ?_) (hsurj _ hpt x) (fun i ↦ hsurj _ (hi i) x)
    (h' x) (h'' x)
  · rw [← Functor.map_comp, ← Functor.map_comp, (LimitStage.transition Λ (𝒮.π i)).naturality]
  · have := congrArg (B.uliftPointSmallEtale x).sheafFiber.map
      (LimitStage.connecting_naturality Λ δ (𝒮.π i) n (n + 1) rfl)
    simp only [Functor.map_comp] at this
    exact this
  · rw [← Functor.map_comp, ← Functor.map_comp, ← (LimitStage.transition Λ (𝒮.map f)).naturality]
  · have := congrArg (B.uliftPointSmallEtale x).sheafFiber.map
      (LimitStage.connecting_naturality Λ δ (𝒮.map f) n (n + 1) rfl)
    simp only [Functor.map_comp] at this
    exact this.symm
  · rw [← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp, 𝒮.w]
  · rw [← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp, 𝒮.w]
  · rw [← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp, ← 𝒮.map_comp]
  · have := congrArg (B.uliftPointSmallEtale x).sheafFiber.map
      (LimitStage.connecting_comp_eq_zero δ hT (𝒮.obj i) n (n + 1) rfl)
    rw [Functor.map_comp, Functor.map_zero] at this
    simpa using congrArg (fun φ ↦ φ.hom y) this
  · exact LimitStage.exists_of_stalk_exact₃ δ hT 𝒮.pt n (n + 1) rfl x y hy

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the map `H^0(Φ(X₁)) ⟶ H^0(Φ(X₂))` is
injective on stalks, as `H^{-1}(Φ(X₃))` vanishes. -/
lemma injective_stalk_zero (α : LimitStage B W)
    {E : ShortComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact)
    (x : B) :
    Function.Injective ((stalkHomology Λ 0 x).map ((LimitStage.functor Λ α).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.f))).hom := by
  obtain ⟨δ, hT⟩ := hE.exists_mk_singleTrianglePlus_distinguished
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  obtain ⟨z, rfl⟩ := LimitStage.exists_of_stalk_exact₁ δ hT α (-1) 0 (by norm_num) x y hy
  rw [ModuleCat.eq_zero_of_isZero (Functor.map_isZero (B.uliftPointSmallEtale x).sheafFiber
    (LimitStage.isZero_homology_functor_obj_single_of_lt Λ α E.X₃ (by norm_num))) z, map_zero]

lemma shortExact_cokernelSequence_injectiveι
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (ShortComplex.cokernelSequence (Injective.ι G)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (inferInstanceAs (Mono (Injective.ι G))) inferInstance

variable (hz : ∀ (J : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] (q : ℤ),
      q ≠ 0 → (∀ i, IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((LimitStage.functor Λ (𝒮.obj i)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj J))))
        ∧ IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((LimitStage.functor Λ 𝒮.pt).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj J))))
  (h0 : ∀ (J : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J],
    𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj J) 0)

omit [IsCofiltered I] in
include h0 in
/-- Degree zero: a stalkwise colimit in degree `0` at all injective sheaves is one at all
sheaves, by left exactness. -/
lemma isStalkColimit_zero (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj G) 0 := by
  let E := ShortComplex.cokernelSequence (Injective.ι G)
  have hE : E.ShortExact := shortExact_cokernelSequence_injectiveι G
  let E' := ShortComplex.cokernelSequence (Injective.ι E.X₃)
  have hE' : E'.ShortExact := shortExact_cokernelSequence_injectiveι E.X₃
  obtain ⟨δ, hT⟩ := hE.exists_mk_singleTrianglePlus_distinguished
  have h₁ : 𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂) 0 :=
    h0 (Injective.under G)
  have h₂ : 𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E'.X₂) 0 :=
    h0 (Injective.under E.X₃)
  intro x
  refine ModuleCat.IsElementwiseColimit.of_kernel
    (fun i ↦ (stalkHomology Λ 0 x).map ((LimitStage.functor Λ (𝒮.obj i)).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.f)))
    ((stalkHomology Λ 0 x).map ((LimitStage.functor Λ 𝒮.pt).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map E.f)))
    (fun i ↦ (stalkHomology Λ 0 x).map ((LimitStage.functor Λ (𝒮.obj i)).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map (E.g ≫ E'.f))))
    ((stalkHomology Λ 0 x).map ((LimitStage.functor Λ 𝒮.pt).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map (E.g ≫ E'.f))))
    (fun i ↦ ?_) (fun i ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_) (fun f ↦ ?_)
    (injective_stalk_zero 𝒮.pt hE x) (fun i ↦ injective_stalk_zero _ hE x) (fun y ↦ ?_)
    (fun i y hy ↦ ?_) (h₁ x) (h₂ x)
  · rw [← Functor.map_comp, ← Functor.map_comp, (LimitStage.transition Λ (𝒮.π i)).naturality]
  · rw [← Functor.map_comp, ← Functor.map_comp, (LimitStage.transition Λ (𝒮.π i)).naturality]
  · rw [← Functor.map_comp, ← Functor.map_comp, ← (LimitStage.transition Λ (𝒮.map f)).naturality]
  · rw [← Functor.map_comp, ← Functor.map_comp, ← (LimitStage.transition Λ (𝒮.map f)).naturality]
  · rw [← Functor.map_comp, ← NatTrans.comp_app, LimitStage.transition_comp, 𝒮.w]
  · rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      E.zero_assoc]
    simp
  · have hy' : ((stalkHomology Λ 0 x).map ((LimitStage.functor Λ (𝒮.obj i)).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map E'.f))).hom
        (((stalkHomology Λ 0 x).map ((LimitStage.functor Λ (𝒮.obj i)).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map E.g))).hom y) = 0 := by
      have h' := hy
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
      exact h'
    exact LimitStage.exists_of_stalk_exact₂ δ hT _ 0 x y
      (injective_stalk_zero _ hE' x (by rw [hy', map_zero]))

include hz h0 in
/-- **Dimension shifting.** If `H^q` of all the stages vanishes on injective sheaves for
`q ≠ 0`, and the system is a stalkwise colimit in degree `0` at every injective sheaf, then it
is a stalkwise colimit in every degree `n ≥ 0` at every sheaf. -/
theorem isStalkColimit_of_injective :
    ∀ (n : ℕ) (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj G) n
  | 0, G => 𝒮.isStalkColimit_zero h0 G
  | n + 1, G => by
    let E := ShortComplex.cokernelSequence (Injective.ι G)
    have hE : E.ShortExact := shortExact_cokernelSequence_injectiveι G
    have hIH := isStalkColimit_of_injective n E.X₃
    have h' : 𝒮.IsStalkColimit Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj E.X₂) n := by
      rcases n with _ | k
      · exact h0 (Injective.under G)
      · have := hz (Injective.under G) ((k + 1 : ℕ) : ℤ) (by omega)
        exact 𝒮.isStalkColimit_of_isZero this.1 this.2
    have h1 := hz (Injective.under G) ((n : ℤ) + 1) (by omega)
    have := 𝒮.isStalkColimit_succ hE n h1.1 h1.2 h' hIH
    push_cast
    exact this

end LimitStageSystem

end AlgebraicGeometry.Etale
