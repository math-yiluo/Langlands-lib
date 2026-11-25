/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeRational

/-!
# Compact-support base change with `ℚ̄_ℓ`-coefficients

The `ℚ̄_ℓ`-stage `D_comp(X_proét, ℚ̄_ℓ)` is the common-stage (pair) category of the rational stages
`D_comp(X_proét, E)` over the finite extensions `E/ℚ_ℓ` inside `ℚ̄_ℓ`, with the scalar extensions
`T_{F/E} = F ⊗ᴸ_E -` as transition functors (`CategoryTheory.StageSystem.PairCategory`). The
operations of the `ℚ̄_ℓ`-stage are descended from the finite stages: a family of functors `Φ_E`
together with compatibilities `β_{F/E} : T_{F/E} ∘ Φ_E ≅ Φ_F ∘ T_{F/E}` with the scalar extensions
is a morphism of stage systems, which induces a functor on the pair categories, and compatible
families of natural transformations descend to natural transformations
(`CategoryTheory.StageSystem.Morphism`).

This file proves the two statements of the `ℚ̄_ℓ`-stage which concern the compact-support direct
image, for any such stage-system structure on the rational stages and any descent data of the
finite-stage functors (the scalar-extension compatibilities of `Rf_!` and `Lg^*`, blueprint
`lemma-change-coefficients-compact-support`, which are taken as data here):

- `AlgebraicGeometry.ProEtale.nonempty_iso_ι_obj_rationalRightDerivedLowerShriek`: the value of
  the descended compact-support direct image on an object of the `ℚ̄_ℓ`-stage may be computed at
  any finite stage at which the object is represented;
- `AlgebraicGeometry.ProEtale.isIso_descNatTrans_app_rationalExchange`: the descended
  compact-support exchange transformation is an isomorphism at every object represented at a
  finite stage by an integral lattice whose reductions are of étale origin.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] {I : Type} [Preorder I] [IsDirectedOrder I]
  (E : I → Type w) [∀ i, Field (E i)] [∀ i, Algebra (E i) (PadicAlgCl l)]
  [∀ i, Algebra ℚ_[l] (E i)] [∀ i, IsScalarTower ℚ_[l] (E i) (PadicAlgCl l)]
  [∀ i, FiniteDimensional ℚ_[l] (E i)] [∀ i, Small.{u + 1} (E i)]

set_option hygiene false in
/-- The rational stage `D_comp(X_proét, E_i)`. -/
local notation "𝐃𝐐[" i "](" X ")" =>
  DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l (E i)

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  {S : StageSystem fun i ↦ 𝐃𝐐[i](X)} {S' : StageSystem fun i ↦ 𝐃𝐐[i](Y)}

/-- Independence of the finite coefficient field.

Let `F` be a descent datum for the rational compact-support direct images
`Rf_{!,E} : D_comp(X_proét, E) ⥤ D_comp(Y_proét, E)` along a stage-system structure on the
rational stages (the `ℚ̄_ℓ`-stage being its pair category). If an object `K_{ℚ̄_ℓ}` of the
`ℚ̄_ℓ`-stage is represented at the finite stages `E` and `L` by `K_E` and `K_L`, then
`Rf_! K_E ⊗_E ℚ̄_ℓ` and `Rf_! K_L ⊗_L ℚ̄_ℓ` are canonically isomorphic: both are isomorphic to the
value of the descended functor on `K_{ℚ̄_ℓ}`. -/
theorem nonempty_iso_ι_obj_rationalRightDerivedLowerShriek (F : S.Morphism S')
    (hF : ∀ i, F.Φ i = rationalRightDerivedLowerShriek l (E i) c) {i j : I}
    {KE : 𝐃𝐐[i](X)} {KL : 𝐃𝐐[j](X)} (e : (S.ι i).obj KE ≅ (S.ι j).obj KL) :
    Nonempty ((S'.ι i).obj ((rationalRightDerivedLowerShriek l (E i) c).obj KE) ≅
      (S'.ι j).obj ((rationalRightDerivedLowerShriek l (E j) c).obj KL)) := by
  rw [← hF i, ← hF j]
  exact ⟨(F.ιCompFunctorIso i).symm.app KE ≪≫ F.functor.mapIso e ≪≫ (F.ιCompFunctorIso j).app KL⟩

end Independence

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g) (c : Compactification f)
  {S : StageSystem fun i ↦ 𝐃𝐐[i](X)} {S' : StageSystem fun i ↦ 𝐃𝐐[i](Y')}

/-- `ℚ̄_ℓ` compact-support base change.

Let `F` and `G` be descent data, along stage-system structures on the rational stages, for the
rational functors `Lg^* Rf_!(c)` and `Rf'_!(c') Lg'^*` (whose values at the finite stage `E_i`
are the transports `Rationalization.map` of the integral operations), and let `τ` be a compatible
family whose component at every finite stage is the rational compact-support exchange map
(`AlgebraicGeometry.ProEtale.rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap`). Then
the descended exchange transformation `Lg^* Rf_! K ⟶ Rf'_! Lg'^* K` on the `ℚ̄_ℓ`-stage is an
isomorphism at every object `K` represented at a finite stage `E_i` by (the rationalization of)
an integral lattice `K_i ∈ D_comp(X_proét, 𝒪_{E_i})` whose reductions are of étale origin: there
it is represented by the `E_i`-coefficient compact-support base change isomorphism
(`isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`).
It is independent of the finite stage and of the representative, being the component of a
natural transformation of functors on the pair category. -/
theorem isIso_descNatTrans_app_rationalExchange {F G : S.Morphism S'} (τ : F.Hom G)
    (hF : ∀ i, F.Φ i = Rationalization.map (nonZeroDivisors (Shrink.{u + 1}
      (PadicAlgCl.integers l (E i)))) (integralOperation l (E i)
        (Rf_!(c)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l (E i)))] ⋙
          L((g)^*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l (E i)))]))))
    (hG : ∀ i, G.Φ i = Rationalization.map (nonZeroDivisors (Shrink.{u + 1}
      (PadicAlgCl.integers l (E i)))) (integralOperation l (E i)
        (L((g')^*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l (E i)))]) ⋙
          Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1}
            (Shrink.{u + 1} (PadicAlgCl.integers l (E i)))])))
    (hτ : ∀ i, HEq (τ.τ i)
      (rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap l (E i) sq c))
    (i : I) (K : DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l (E i))
    (Kn : ∀ n : ℕ, _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l (E i)) ⧸
        PadicAlgCl.maximalIdealShrink l (E i) ^ n))))
    (η : ∀ n : ℕ, (DerivedCategoryDerivedCompleteIntegral.ι _ l (E i)).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l (E i) ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, Sheaf.IsDerivedBaseChange (η n))
    (hKn : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l (E i)) ⧸
        PadicAlgCl.maximalIdealShrink l (E i) ^ n)) X (Kn n)) :
    IsIso ((StageSystem.Morphism.descNatTrans τ).app
      ⟨i, (DerivedCategoryDerivedCompleteRational.fromIntegral _ l (E i)).obj K⟩) := by
  refine StageSystem.Morphism.isIso_descNatTrans_app τ _ ?_
  have h := isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app l (E i) sq
    c K Kn η hη hKn
  change IsIso ((τ.τ i).app ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l (E i)).obj K))
  obtain ⟨Φ, β, coh⟩ := F
  obtain ⟨Ψ, γ, coh'⟩ := G
  obtain ⟨τ, comm⟩ := τ
  dsimp only at hF hG hτ ⊢
  have hΦ : Φ = _ := funext hF
  have hΨ : Ψ = _ := funext hG
  subst hΦ hΨ
  rw [eq_of_heq (hτ i)]
  exact h

end Exchange

end AlgebraicGeometry.ProEtale
