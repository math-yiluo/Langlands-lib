/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsTorsion
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoinvariant
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethEquivariant

/-!

# The Künneth map descends along Galois layers

Let `M`, `N`, `P` be models with morphisms `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N`, and suppose that the
generic fibres of `M` and `P` lie over a field `L`, compatibly with `φ₁`. For a Galois extension
`Ω/L` with finite layers of degrees invertible in a finite discrete ring `T₀`, consider the Galois
layers `M_Ω`, `P_Ω` (`NearbyCyclesModel.galoisLayer`) and the Künneth map `Π_Ω` of the product
configuration `M_Ω ⟵ P_Ω ⟶ N` (`NearbyCyclesModel.galoisLayerMap` and the projection of the
layer). This file shows that the Künneth map `Π` of `M ⟵ P ⟶ N` is invertible as soon as `Π_Ω` is
(`NearbyCyclesModel.isIso_kunnethMap_of_isIso_galoisLayer`), given the coinvariant property of the
projector onto the invariants of `Ψ_{M_Ω}` after tensoring with the second factor.

Indeed `Ψ_M A ⟶ Ψ_{M_Ω} A` and `Ψ_P (A ⊠ B) ⟶ Ψ_{P_Ω} (A ⊠ B)` are the inclusions of the
`Gal(Ω/L)`-invariants (SGA 4½, [Th. finitude], Lemme 3.4,
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin`), `Π_Ω` is
equivariant (`NearbyCyclesModel.kunnethMap_autAction`) with the Galois group acting trivially on
the second factor, and invariants commute with the tensor product with a complex with trivial
action (blueprint `prose-E-10`,
`NearbyCyclesModel.isIso_map_kunnethMap_of_coinvariant`). This is the projection formula (3) of
the generic-slicing step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`), for torsion coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}
  (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂') {L : Type u} [Field L]
  {hM : M.generic ⟶ Spec (.of L)} {hP : P.generic ⟶ Spec (.of L)}
  (h₁ : φ₁.generic ≫ hM = hP ≫ Spec.map (CommRingCat.ofHom (RingHom.id L)))
  (Ω : Type u) [Field Ω] [Algebra L Ω]

/-- The first projection `P_Ω ⟶ M_Ω` of the Galois layers of a product configuration: the change
of Galois layers along `φ₁` (`NearbyCyclesModel.galoisLayerMap`). -/
noncomputable abbrev galoisLayerFst : (P.galoisLayer hP Ω).Hom (M.galoisLayer hM Ω) f₁ f₁' :=
  galoisLayerMap Ω Ω (RingHom.id Ω) rfl φ₁ h₁

/-- The second projection `P_Ω ⟶ N` of the Galois layer of a product configuration: the
projection of the layer followed by `φ₂`. -/
noncomputable abbrev galoisLayerSnd : (P.galoisLayer hP Ω).Hom N (𝟙 Z ≫ f₂) (𝟙 Z' ≫ f₂') :=
  (P.galoisLayerHom hP Ω).comp φ₂

omit [Algebra L Ω] in
include h₁ in
lemma galoisLayerFst_generic_comp_galoisLayerAut [Algebra L Ω] (σ : Ω ≃ₐ[L] Ω) :
    (P.galoisLayerAut hP Ω σ).generic ≫ (galoisLayerFst φ₁ h₁ Ω).generic =
      (galoisLayerFst φ₁ h₁ Ω).generic ≫ (M.galoisLayerAut hM Ω σ).generic := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp only [galoisLayerAut_generic, galoisLayerMap_generic, Category.assoc,
      galoisLayerGenericMap_snd, galoisLayerGenericMap_snd_assoc,
      pullbackAction_snd, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]

set_option maxHeartbeats 1600000 in
-- the Künneth maps of the two product configurations are large terms
/-- **The Künneth map descends along a Galois layer** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, projection formula (3); torsion coefficients).
Let `φ₁ : P ⟶ M`, `φ₂ : P ⟶ N` be morphisms of models with the generic fibres of `M`, `P` over `L`,
and `Ω/L` Galois with degrees invertible in `T₀`. Suppose that `Lε^*` of `A` on `M` and of
`Lf₁^* A ⊗ Lf₂^* B` on `P` are bounded below of étale origin, and that the exchange
`α_M : Ψ_M A ⟶ Ψ_{M_Ω} A` of the layer has a retraction `r_M` whose projector, tensored with the
second factor of the Künneth map, fixes on cohomology every map invariant under `Gal(Ω/L)`. Then
the Künneth map `Π_{A,B}` of `M ⟵ P ⟶ N` is invertible if the one of `M_Ω ⟵ P_Ω ⟶ N` is. -/
theorem isIso_kunnethMap_of_isIso_galoisLayer [IsGalois L Ω] [QuasiCompact P.j]
    [QuasiSeparated P.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) Y)))
    (hAB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) P.generic
      ((finiteCoefficientDerivedEquivalence P.generic T₀).functor.obj
        (L((P.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj
          (L((f₁)^*⟦Profinite.continuousMapRingObj T₀⟧).obj A ⊗
            L((f₂)^*⟦Profinite.continuousMapRingObj T₀⟧).obj B))))
    (rM : (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
        (M.galoisLayer hM Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj A ⟶
      (M.nearbyCycles (Profinite.continuousMapRingObj T₀) ⋙
        L((𝟙 X')^*⟦Profinite.continuousMapRingObj T₀⟧)).obj A)
    (hrM : ((M.galoisLayerHom hM Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app A ≫
      rM = 𝟙 _)
    (hcoinv : ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology Z') Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) Z')}
      (φ : (DerivedCategory.homologyFunctor _ q).obj
        (L((f₁')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            (((M.galoisLayer hM Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj A)) ⊗
          L((𝟙 Z' ≫ f₂')^*⟦Profinite.continuousMapRingObj T₀⟧).obj
            ((N.nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
              (L((𝟙 Y)^*⟦Profinite.continuousMapRingObj T₀⟧).obj B))) ⟶ W),
      (∀ σ : Ω ≃ₐ[L] Ω, (DerivedCategory.homologyFunctor _ q).map
          (L((f₁')^*⟦Profinite.continuousMapRingObj T₀⟧).map
            (M.galoisLayerAction (Profinite.continuousMapRingObj T₀) hM Ω σ
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj A)) ▷ _) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((f₁')^*⟦Profinite.continuousMapRingObj T₀⟧).map (rM ≫
            ((M.galoisLayerHom hM Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app
              A) ▷ _) ≫ φ = φ)
    (hK : IsIso (kunnethMap (Profinite.continuousMapRingObj T₀) (galoisLayerFst φ₁ h₁ Ω)
      (galoisLayerSnd φ₂ Ω) (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj A)
      (L((𝟙 Y)^*⟦Profinite.continuousMapRingObj T₀⟧).obj B))) :
    IsIso (kunnethMap (Profinite.continuousMapRingObj T₀) φ₁ φ₂ A B) := by
  obtain ⟨rP, hrP, hinvP⟩ := exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin
    T₀ P hP Ω hp _ hAB
  have key := isIso_map_kunnethMap_of_coinvariant (Profinite.continuousMapRingObj T₀) φ₁ φ₂
    (galoisLayerFst φ₁ h₁ Ω) (galoisLayerSnd φ₂ Ω) (M.galoisLayerHom hM Ω) (Hom.id N)
    (P.galoisLayerHom hP Ω) (by simp) (by simp) (by simp [Hom.comp]) (by simp [Hom.comp])
    (by simp) (by simp) (by simp) (by simp) A B
    (fun σ : Ω ≃ₐ[L] Ω ↦ M.galoisLayerAut hM Ω σ) (fun _ ↦ Hom.id N)
    (fun σ ↦ P.galoisLayerAut hP Ω σ)
    (fun σ ↦ kunnethMap_autAction _ _ _ _ _ _ (by simp)
      (galoisLayerFst_generic_comp_galoisLayerAut φ₁ h₁ Ω σ) (by simp [Hom.comp])
      (by simp [Hom.comp]) _ _)
    (fun _ ↦ Hom.autAction_of_eq_id _ _ rfl rfl _)
    (by
      rw [Hom.pullbackExchange_app_of_eq_id _ _ _ rfl rfl]
      infer_instance)
    rM hrM hcoinv rP hrP (fun σ ↦ (hinvP σ).1) hK
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId _ Z') _).1 key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
