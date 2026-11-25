/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.ExchangeCompat
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Base change along open immersions: the projective case over a separably closed field

Let `K` be a separably closed field, `j : U ⟶ X` an open immersion of `K`-schemes of finite type,
`Y` a proper `K`-scheme, `W = X ×_K Y` and `V = U ×_X W`. If the base change maps of a sheaf `F`
are isomorphisms on the geometric stalks at all non-closed points of `W`, then the cone `Q` of the
derived base change map `β` at `F` has vanishing stalks at all non-closed points, so `Q = 0` as
soon as `RΓ(W, Q) = 0` (blueprint `corollary-open-direct-image-over-field--2`); and `RΓ(W, β)` is an
isomorphism by the Künneth formula with one proper factor (blueprint
`lemma-kunneth-finite-direct-image--1`). This is the projective case of the proof of blueprint
`corollary-open-direct-image-over-field--2`, after the reduction to a separably closed ground field.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace DerivedCategory

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [Category* D] [Abelian D]

/-- For a distinguished triangle `T` in `D(C)` and an exact functor `Φ : C ⥤ D`, if `Φ` maps the
morphisms `H^n(T.mor₁)` and `H^{n+1}(T.mor₁)` to isomorphisms, then `Φ(H^n(T.obj₃)) = 0`. -/
lemma isZero_map_homology_obj₃_of_isIso (Φ : C ⥤ D) [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n : ℤ) (h₀ : IsIso (Φ.map ((homologyFunctor C n).map T.mor₁)))
    (h₁ : IsIso (Φ.map ((homologyFunctor C (n + 1)).map T.mor₁))) :
    IsZero (Φ.obj ((homologyFunctor C n).obj T.obj₃)) := by
  have : Φ.Additive := Functor.additive_of_preserves_binary_products _
  have e₂ := (HomologySequence.exact₂ T hT n).map Φ
  have e₃ := (HomologySequence.exact₃ T hT n (n + 1) rfl).map Φ
  have e₁ := (HomologySequence.exact₁ T hT n (n + 1) rfl).map Φ
  have hg : Φ.map ((homologyFunctor C n).map T.mor₂) = 0 :=
    e₂.epi_f_iff.1 (inferInstanceAs (Epi (Φ.map ((homologyFunctor C n).map T.mor₁))))
  have hδ : Φ.map (HomologySequence.δ T n (n + 1) rfl) = 0 :=
    e₁.mono_g_iff.1
      (inferInstanceAs (Mono (Φ.map ((homologyFunctor C (n + 1)).map T.mor₁))))
  exact e₃.isZero_X₂ hg hδ

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The Künneth input of the projective case (blueprint `lemma-kunneth-finite-direct-image--1`):
over a separably closed field, `RΓ(W, -)` maps the exchange morphism `β : q₁^* Rj_* E ⟶ Rh_* e^* E`
to an isomorphism, for `Λ` killed by an integer `n ≠ 0`. -/
theorem Etale.isIso_rightDerivedGlobalSections_map_unboundedExchange_of_isProper {K : Type u}
    [Field K] [IsSepClosed K] {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsProper aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn₀ : n ≠ 0)
    (hΛ : (n : Λ) = 0)
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
      (Etale.unboundedExchange (ModuleCat.{u + 1} Λ) sq.toCommSq E)) := by
  refine Etale.isIso_rightDerivedGlobalSections_map_derivedBaseChangeMap_of_isProper Λ
    (fun x ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn₀, ?_⟩) aX aY q₁ q₂ hW
    j e h sq E
  rw [nsmul_eq_mul, hΛ, zero_mul]

/-- Blueprint `corollary-open-direct-image-over-field--2`, the projective case over a separably
closed field: for `K` separably closed and `Y` proper over `K`, if the base change map at `F` is an
isomorphism on the geometric stalks at all non-closed points of `W = X ×_K Y`, then it is an
isomorphism. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isProper_of_isSepClosed {K : Type u}
    [Field K] [IsSepClosed K] {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsProper aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ z : W, ¬ IsClosed ({z} : Set W) → ∀ i : ℤ,
      IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)))
    (i : ℤ) : IsIso (Etale.baseChangeHomologyMap Λ sq i F) := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  set β := (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  suffices hβ : IsIso β by
    rw [Etale.isIso_baseChangeHomologyMap_iff]
    infer_instance
  suffices hι : IsIso (DerivedCategory.Plus.ι.map β) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι β
  obtain ⟨Q, g, δ, hT⟩ := distinguished_cocone_triangle β
  have hT' := DerivedCategory.Plus.ι.map_distinguished _ hT
  refine (Triangle.isZero₃_iff_isIso₁ _ hT').1 ?_
  obtain ⟨m, hm⟩ := Q.2
  have : (DerivedCategory.Plus.ι.obj Q).IsGE m := hm
  have : LocallyOfFiniteType (q₁ ≫ aX) := by
    have : LocallyOfFiniteType q₁ := MorphismProperty.of_isPullback hW.flip inferInstance
    infer_instance
  refine (Etale.isZero_iff_forall_isZero_homology_rightDerivedGlobalSections_of_isGE (q₁ ≫ aX)
    (DerivedCategory.Plus.ι.obj Q) m (fun k z hz ↦ ?_)).2 (fun k ↦ ?_)
  · have : LocallySmall.{u + 1} W.Etale := locallySmall_max.{u + 1, u}
    have hiso (k' : ℤ) : IsIso ((W.uliftPointSmallEtale z).sheafFiber.map
        ((DerivedCategory.homologyFunctor _ k').map (DerivedCategory.Plus.ι.map β))) :=
      hF z hz k'
    refine (DerivedCategory.isZero_map_homology_obj₃_of_isIso
      (W.uliftPointSmallEtale z).sheafFiber _ hT' k (hiso k) (hiso (k + 1))).of_iso ?_
    exact (((pointSmallEtale (W.algClosurePoint z)).uliftSheafFiberIso
      (ModuleCat.{u + 1} Λ)).app _).symm
  · have hRΓ : IsIso ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map
        (DerivedCategory.Plus.ι.map β)) :=
      (Arrow.isIso_iff_isIso_of_isIso
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).mapArrow.mapIso
          (Etale.baseChangeArrowIsoUnboundedExchange _ sq.toCommSq
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).hom).2
        (Etale.isIso_rightDerivedGlobalSections_map_unboundedExchange_of_isProper Λ aX aY j q₁
          q₂ hW e h sq n hn₀ hΛ _)
    have : (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).IsTriangulated :=
      inferInstanceAs
        ((Sheaf.Γ W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated)
    have := (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).map_distinguished _ hT'
    exact (DerivedCategory.homologyFunctor _ k).map_isZero
      ((Triangle.isZero₃_iff_isIso₁ _ this).2 hRΓ)

end AlgebraicGeometry
