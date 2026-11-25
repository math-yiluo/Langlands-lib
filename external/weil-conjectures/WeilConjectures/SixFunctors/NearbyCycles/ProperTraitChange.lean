/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.SixFunctors.NearbyCycles.PushforwardExchangeSquare
public import WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait
import WeilConjectures.Tactic.ExactModProofs

/-!

# Step (B): global cohomology of nearby cycles under change of strictly henselian trait

Let `ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings (for instance
strictly henselian discrete valuation rings), with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` to separably
closed fields (geometric generic points) and `bᵢ : Rᵢ ⟶ κᵢ` to fields (special points, `b₂` with
kernel the maximal ideal), compatible with `c : Ω₁ ⟶ Ω₂` and `d : κ₁ ⟶ κ₂`. Let `N` be a model
**proper** over `S₁ = Spec R₁` along `q₁`, `M` its base change to `S₂ = Spec R₂` and `φ : M ⟶ N`
the morphism of models. Write `p₂ : X'_{s₂} ⟶ Spec κ₂` for the special fibre of `M`.

Step (B) of the proof of SGA 4½, [Th. finitude], Prop. 3.7: the global cohomology
`Rp₂_*` of the pullback exchange `α : Lf'^* Ψ_N ⟶ Ψ_M Lφ^*` (with coefficients in a finite ring)
is an isomorphism at every complex bounded below of étale origin on the geometric generic fibre
of `N` (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_isProper_trait`). Both sides
compute the cohomology of the geometric generic fibre:
`RΓ(X_{s₂}, Ψ_M K) = RΓ(X_{η̄₂}, K) = RΓ(X_{η̄₁}, K) = RΓ(X_{s₁}, Ψ_N K)`.

Formally, `φ`, the structure morphisms `N ⟶ S₁`, `M ⟶ S₂` (`NearbyCyclesModel.Hom.toOfTrait`) and
the morphism of traits `S₂ ⟶ S₁` (`NearbyCyclesModel.ofTraitHom`) form a commutative square of
morphisms of models, and the square law of the pushforward exchanges
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square`) applies. Its inputs are
* the proper exchange for `N ⟶ S₁` and `M ⟶ S₂`
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`);
* proper base change for the square of special fibres and for the square of geometric generic
  fibres `X_{η̄₂} ⟶ X_{η̄₁}`; the latter is the invariance of `RΓ(X_η̄, -)` under the extension
  `Ω₁ ⟶ Ω₂` of separably closed fields
  (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_finiteCoefficient`);
* the invariance of the nearby cycles of the trait itself
  (`NearbyCyclesModel.isIso_pullbackExchange_ofTraitHom_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂} {d : κ₁ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Step (B) of Deligne's proof of the invariance of nearby cycles under change of strictly
henselian trait** (SGA 4½, [Th. finitude], Prop. 3.7, step (B); finite coefficients). Let
`ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings with compatible maps to
separably closed fields `aᵢ : Rᵢ ⟶ Ωᵢ` (`c ∘ a₁ = a₂ ∘ ι`) and to fields `bᵢ : Rᵢ ⟶ κᵢ`
(`d ∘ b₁ = b₂ ∘ ι`, `b₂` with kernel the maximal ideal). Let `N` be a model proper over
`Spec R₁` along `q₁` (geometric generic fibre over `Spec Ω₁` along `g₁`, special fibre over
`Spec κ₁` along `p₁`, both cartesian), `M` a model over `Spec R₂` along `q₂` (likewise with `g₂`,
`p₂`), and `φ : M ⟶ N` a morphism of models whose square of total spaces over `Spec ι` is
cartesian and whose maps of geometric generic fibres and of special fibres lie over `Spec c` and
`Spec d`. Then `Rp₂_*` of the pullback exchange `Lf'^* Ψ_N K ⟶ Ψ_M Lφ^* K` of the models of the
geometric generic fibres is an isomorphism for every complex `K` on the geometric generic fibre
of `N` bounded below of étale origin: the global cohomology of the special fibre of the nearby
cycles is that of the geometric generic fibre, on both sides. -/
theorem isIso_map_pullbackExchange_app_of_isProper_trait
    (hc : c.comp a₁ = a₂.comp ι) (hd : d.comp b₁ = b₂.comp ι)
    (hb₂ : RingHom.ker b₂ = IsLocalRing.maximalIdeal R₂) (φ : M.Hom N f f')
    (q₁ : N.total ⟶ Spec (.of R₁)) [IsProper q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (hs : f' ≫ p₁ = p₂ ≫ Spec.map (CommRingCat.ofHom d))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
      ((finiteCoefficientDerivedEquivalence _ T).functor.obj K)) :
    IsIso (R((p₂)_*⟦Profinite.continuousMapRingObj T⟧).map
      ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) := by
  -- the squares of rings
  have hcs : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom a₁) =
      Spec.map (CommRingCat.ofHom a₂) ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have hds : Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom b₁) =
      Spec.map (CommRingCat.ofHom b₂) ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hd]
  -- the squares of geometric generic fibres and of special fibres are cartesian
  have hpbs : IsPullback f' p₂ p₁ (Spec.map (CommRingCat.ofHom d)) := by
    refine IsPullback.of_right ?_ hs hNi
    have h := hMi.paste_horiz hφ
    rw [← φ.comm_i, ← hds] at h
    exact h
  have hpbg : IsPullback φ.generic g₂ g₁ (Spec.map (CommRingCat.ofHom c)) := by
    refine IsPullback.of_right ?_ hgen hNj
    have h := hMj.paste_horiz hφ
    rw [← φ.comm_j, ← hcs] at h
    exact h
  -- finiteness properties, by base change
  have : IsProper q₂ := MorphismProperty.of_isPullback hφ ‹_›
  have : IsProper g₁ := MorphismProperty.of_isPullback hNj ‹_›
  have : IsProper g₂ := MorphismProperty.of_isPullback hMj ‹_›
  have : IsProper p₁ := MorphismProperty.of_isPullback hNi ‹_›
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  -- the inputs: the proper exchanges, proper base change and the trait case
  have hχ := isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    (Hom.toOfTrait N a₁ b₁ q₁ g₁ p₁ hNj.w hNi.w) hNi
    (IsPullback.of_horiz_isIso ⟨by simp⟩) K hK
  have hK' := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
    φ.generic hK
  have hχ' := isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T
    (Hom.toOfTrait M a₂ b₂ q₂ g₂ p₂ hMj.w hMi.w) hMi
    (IsPullback.of_horiz_isIso ⟨by simp⟩) _ hK'
  have hΨ := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T N.i
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T N.j
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
        N.toGeneric.ε hK))
  have hbc' : IsIso ((baseChangeMap (Profinite.continuousMapRingObj T) hpbs.toCommSq).app
      ((N.toGeneric.nearbyCycles (Profinite.continuousMapRingObj T)).obj K)) :=
    isIso_baseChangeMap_app_of_isProper_finiteCoefficient T hpbs _ hΨ
  have hbc := isIso_baseChangeMap_app_of_isProper_finiteCoefficient T hpbg K hK
  have hα₁ := isIso_pullbackExchange_ofTraitHom_app T a₁ b₁ a₂ b₂ ι c d hc hd hb₂ _
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T g₁ hK)
  have key := isIso_map_pullbackExchange_app_of_square (Profinite.continuousMapRingObj T)
    φ.toGeneric (Hom.toOfTrait N a₁ b₁ q₁ g₁ p₁ hNj.w hNi.w)
    (Hom.toOfTrait M a₂ b₂ q₂ g₂ p₂ hMj.w hMi.w) (ofTraitHom a₁ b₁ a₂ b₂ ι c d hc hd) hφ.w
    hgen hgen hs K (by exact_mod_proofs hχ) (by exact_mod_proofs hbc')
    (by exact_mod_proofs hα₁) (by exact_mod_proofs hbc) (by exact_mod_proofs hχ')
  exact_mod_proofs key

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
