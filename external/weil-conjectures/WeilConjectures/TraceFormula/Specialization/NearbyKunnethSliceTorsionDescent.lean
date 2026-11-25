/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionExchange
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGaloisLayer
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsCoinvariantTensor
public import WeilConjectures.Tactic.ExactByKernel
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure

/-!

# Descent of the Künneth map along a Galois slice

This file assembles the projection formula of the generic-slicing step of Gabber's Künneth formula
(blueprint `proposition-external-kunneth-formula-nearby-cycles`, identification (2) and projection
formula (3)) for finite field coefficients, for abstract product configurations
(`NearbyCyclesModel.isIso_map_kunnethMap_of_galoisSlice`). Consider:

* a product configuration `M ⟵ P ⟶ N` (with Künneth map `Π`);
* models `M₁`, `P₁` with generic fibres over a field `L`, a morphism `μ₁ : P₁ ⟶ M₁` over the
  identity of `Spec L`, and morphisms `ψ_M : M₁ ⟶ M`, `ψ_P : P₁ ⟶ P` with invertible exchanges,
  compatible with `μ₁` and the first projection;
* a Galois extension `Ω/L` with degrees invertible in `T₀`, and a product configuration
  `M_S ⟵ P_S ⟶ N` with morphisms `ρ_M : M_S ⟶ M₁^Ω`, `ρ_P : P_S ⟶ P₁^Ω` to the Galois layers, with
  invertible exchanges, compatible with the projections.

If the Künneth map of `M_S ⟵ P_S ⟶ N` is invertible, so is `Lψ'^* Π`: the Künneth map of the
Galois layers is invertible by the square along `ρ`, it descends to `M₁ ⟵ P₁ ⟶ N`
(`NearbyCyclesModel.isIso_kunnethMap_of_isIso_galoisLayer`, with the coinvariant retraction of
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor`), and it is
identified with `Lψ'^* Π` by the square along `ψ`.

The statement is kept abstract so that it is elaborated once: the slices over a generic slice trait
are large terms.

-/

@[expose] public section


universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Nearby cycles preserve bounded below complexes. -/
lemma isGE_nearbyCycles_obj {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (n : ℤ) [K.IsGE n] : ((M.nearbyCycles Λ).obj K).IsGE n := by
  have := isGE_leftDerivedUpperStar_obj Λ M.ε K n
  have := Functor.isGE_rightDerivedFunctor_obj ((M.j)_*⟦Λ⟧) ((L((M.ε)^*⟦Λ⟧)).obj K) n
  exact isGE_leftDerivedUpperStar_obj Λ M.i _ n

end General

variable (T₀ : Type) [TopologicalSpace T₀] [Field T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
  [Finite T₀]
  {X X' Y Y' Z Z' XS ZS XS' ZS' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'}
  {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
  {M₁ : NearbyCyclesModel X XS'} {P₁ : NearbyCyclesModel Z ZS'} {μs : ZS' ⟶ XS'}
  (μ₁ : P₁.Hom M₁ f₁ μs) {rM : X ⟶ X} {rM' : XS' ⟶ X'} {rP : Z ⟶ Z} {rP' : ZS' ⟶ Z'}
  (ψM : M₁.Hom M rM rM') (ψP : P₁.Hom P rP rP')
  {L : Type u} [Field L] (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  {resM : M₁.generic ⟶ Spec (.of L)} {resP : P₁.generic ⟶ Spec (.of L)}
  (h₁ : μ₁.generic ≫ resM = resP ≫ Spec.map (CommRingCat.ofHom (RingHom.id L)))
  {M_S : NearbyCyclesModel XS XS'} {P_S : NearbyCyclesModel ZS ZS'} {σM : XS ⟶ X} {σP : ZS ⟶ Z}
  (ρM : M_S.Hom (M₁.galoisLayer resM Ω) σM (𝟙 XS'))
  (ρP : P_S.Hom (P₁.galoisLayer resP Ω) σP (𝟙 ZS')) {μf : ZS ⟶ XS} (μS : P_S.Hom M_S μf μs)
  {νf : ZS ⟶ Y} {νs : ZS' ⟶ Y'} (νS : P_S.Hom N νf νs)

set_option hygiene false in
/-- The condensed ring `T̲₀`. -/
local notation "Λ" => Profinite.continuousMapRingObj T₀

omit [DiscreteTopology T₀] [Finite T₀] [IsGalois L Ω] in
/-- The derived pullback along an identity reflects isomorphisms. -/
lemma isIso_of_isIso_map_leftDerivedUpperStar_id {W : Scheme.{u}}
    {C C' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))}
    (f : C ⟶ C') (h : IsIso ((L((𝟙 W)^*⟦Λ⟧)).map f)) : IsIso f :=
  (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ W) f).1 h

omit [DiscreteTopology T₀] [Finite T₀] [IsGalois L Ω] in
/-- The Künneth map at `A`, `B` is invertible if it is at `L𝟙^* L𝟙^* A`, `L𝟙^* L𝟙^* L𝟙^* B`. -/
lemma isIso_kunnethMap_leftDerivedUpperStar_id {X₀ Y₀ Z₀ X₀' Y₀' Z₀' : Scheme.{u}}
    {M₀ : NearbyCyclesModel X₀ X₀'} {N₀ : NearbyCyclesModel Y₀ Y₀'}
    {P₀ : NearbyCyclesModel Z₀ Z₀'}
    {g₁ : Z₀ ⟶ X₀} {g₁' : Z₀' ⟶ X₀'} {g₂ : Z₀ ⟶ Y₀} {g₂' : Z₀' ⟶ Y₀'} (ψ₁ : P₀.Hom M₀ g₁ g₁')
    (ψ₂ : P₀.Hom N₀ g₂ g₂') {W : Scheme.{u}} (σ : X₀ ⟶ W)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y₀) Ab.{u + 1})
      (condensedRingObj Λ Y₀)))
    (h : IsIso (kunnethMap Λ ψ₁ ψ₂ ((L((σ)^*⟦Λ⟧)).obj A) B)) :
    IsIso (kunnethMap Λ ψ₁ ψ₂
      ((L((σ)^*⟦Λ⟧)).obj ((L((𝟙 W)^*⟦Λ⟧)).obj ((L((𝟙 W)^*⟦Λ⟧)).obj A)))
      ((L((𝟙 Y₀)^*⟦Λ⟧)).obj ((L((𝟙 Y₀)^*⟦Λ⟧)).obj ((L((𝟙 Y₀)^*⟦Λ⟧)).obj B)))) :=
  isIso_kunnethMap_of_iso Λ ψ₁ ψ₂
    ((L((σ)^*⟦Λ⟧)).mapIso ((leftDerivedUpperStarId Λ W).app _ ≪≫
      (leftDerivedUpperStarId Λ W).app _))
    ((leftDerivedUpperStarId Λ Y₀).app _ ≪≫ (leftDerivedUpperStarId Λ Y₀).app _ ≪≫
      (leftDerivedUpperStarId Λ Y₀).app _) h

/-- **The Künneth map descends along a Galois slice** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, identification (2) and projection formula (3);
finite field coefficients `T₀`): in the situation of the module docstring, if the Künneth map of
`M_S ⟵ P_S ⟶ N` is invertible at `Lσ_M^* A`, `B`, then `Lψ_P'^* Π_{A,B}` is invertible. -/
theorem isIso_map_kunnethMap_of_galoisSlice (hrM : rM = 𝟙 X) (hrP : rP = 𝟙 Z)
    (htotψ : μ₁.total ≫ ψM.total = ψP.total ≫ φ₁.total)
    (hgenψ : μ₁.generic ≫ ψM.generic = ψP.generic ≫ φ₁.generic)
    (hsψ : μs ≫ rM' = rP' ≫ f₁')
    (hψM : ∀ C, IsIso ((ψM.pullbackExchange Λ).app C))
    (hψP : ∀ C, IsIso ((ψP.pullbackExchange Λ).app C))
    (htotρ : μS.total ≫ ρM.total = ρP.total ≫ (galoisLayerFst μ₁ h₁ Ω).total)
    (hgenρ : μS.generic ≫ ρM.generic = ρP.generic ≫ (galoisLayerFst μ₁ h₁ Ω).generic)
    (hbρ : μf ≫ σM = σP ≫ f₁)
    (htotν : νS.total = ρP.total ≫ ψP.total ≫ φ₂.total)
    (hgenν : νS.generic = ρP.generic ≫ (P₁.galoisLayerHom resP Ω).generic ≫ ψP.generic ≫
      φ₂.generic)
    (hbν : νf = σP ≫ rP ≫ f₂) (hsν : νs = rP' ≫ f₂')
    (hρM : ∀ C, IsIso ((ρM.pullbackExchange Λ).app C))
    (hρP : ∀ C, IsIso ((ρP.pullbackExchange Λ).app C))
    [QuasiCompact M₁.j] [QuasiSeparated M₁.j] [QuasiCompact P₁.j] [QuasiSeparated P₁.j]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) X
      ((finiteCoefficientDerivedEquivalence X T₀).functor.obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) Y
      ((finiteCoefficientDerivedEquivalence Y T₀).functor.obj B))
    (a : ℤ) (hBa : B.IsGE a)
    (hS : IsIso (kunnethMap Λ μS νS ((L((σM)^*⟦Λ⟧)).obj A) B)) :
    IsIso (L((rP')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  subst hrM hrP
  -- Share the derived functors and their module-category instances across the two squares.
  let pullX := L((𝟙 X)^*⟦Λ⟧)
  let pullY := L((𝟙 Y)^*⟦Λ⟧)
  have := hBa
  have : IsIso (Hom.id N).total := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso (Hom.id N).generic := inferInstanceAs (IsIso (𝟙 _))
  have hid := (Hom.id N).isIso_pullbackExchange_of_isIso Λ
  have : ∀ C, IsIso ((ψP.pullbackExchange Λ).app C) := hψP
  have : ∀ C, IsIso ((ρP.pullbackExchange Λ).app C) := hρP
  have hT : IsField T₀ := Field.toIsField T₀
  -- the square along `ψ`
  have sqψ := isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange' Λ φ₁ φ₂ μ₁ (ψP.comp φ₂)
    ψM (Hom.id N) ψP htotψ hgenψ
    (Category.comp_id _) (Category.comp_id _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) hsψ
    (Category.comp_id _) (Category.comp_id _) A B
    ?iM ?iN ?iP (𝟭 _)
  case iM => cast_proofs hψM A
  case iN => infer_instance
  case iP =>
    have h : IsIso (ψP.pullbackExchange Λ) := NatIso.isIso_of_isIso_app _
    cast_proofs h
  refine sqψ.2 ?_
  -- the Künneth map descends along the Galois layer
  have hA₂ := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (𝟙 X) hA
  have hB₂ := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (𝟙 Y) hB
  have hAB := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ P₁.ε
    (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar
      T₀ hT f₁ (𝟙 Z ≫ f₂) hA₂ hB₂)
  have hC := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ M₁.ε hA₂
  have hret := exists_retraction_pullbackExchange_galoisLayerHom_coinvariant_tensor M₁
    resM Ω T₀ hp _ hC μs id (fun L' σ ↦ ⟨σ.liftNormal Ω, fun x ↦ σ.liftNormal_commutes Ω x⟩)
  let r := hret.choose
  have hr := hret.choose_spec.1
  have hco := hret.choose_spec.2
  -- Infer each intermediate complex from its bound instead of rebuilding the derived functors.
  have hB₁GE := isGE_leftDerivedUpperStar_obj Λ (𝟙 Y) B a
  have hB₂GE := @isGE_leftDerivedUpperStar_obj Λ _ _ _ _ (𝟙 Y) _ a hB₁GE
  have hNGE := @isGE_nearbyCycles_obj Λ _ _ _ _ N _ a hB₂GE
  have hGE := @isGE_leftDerivedUpperStar_obj Λ _ _ _ _ (𝟙 ZS' ≫ rP' ≫ f₂') _ a hNGE
  have sqρ := isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange' Λ
    (galoisLayerFst μ₁ h₁ Ω) (galoisLayerSnd (hP := resP) (ψP.comp φ₂) Ω) μS νS ρM (Hom.id N) ρP
    htotρ hgenρ ?e1 ?e2 hbρ ?e3 ?e4 ?e5 (pullX.obj (pullX.obj A))
    (pullY.obj (pullY.obj B)) ?jM ?jN ?jP (𝟭 _)
  case jM => cast_proofs hρM _
  case jN => infer_instance
  case jP =>
    have h : IsIso (ρP.pullbackExchange Λ) := NatIso.isIso_of_isIso_app _
    cast_proofs h
  case e1 =>
    exact (Category.comp_id _).trans
      (htotν.trans (congrArg (ρP.total ≫ ·) (Category.id_comp _).symm))
  case e2 => exact (Category.comp_id _).trans hgenν
  case e3 => exact (Category.comp_id μs).trans (Category.id_comp μs).symm
  case e4 =>
    exact (Category.comp_id _).trans
      (hbν.trans (congrArg (σP ≫ ·) (Category.id_comp _).symm))
  case e5 =>
    exact (Category.comp_id _).trans
      (hsν.trans ((Category.id_comp _).symm.trans (Category.id_comp _).symm))
  -- the Künneth map descends along the Galois layer
  have hG := isIso_kunnethMap_of_isIso_galoisLayer μ₁ (ψP.comp φ₂) h₁ Ω T₀ ?hp
    (pullX.obj A) (pullY.obj B) ?hAB ?r ?hr ?hco ?hK
  case r => exact_by_kernel r
  case hp => exact_by_kernel hp
  case hAB => exact_by_kernel hAB
  case hr => exact_by_kernel hr
  case hco => exact_by_kernel fun q W φ hφ ↦ hco q _ a hGE (W := W) φ hφ
  case hK =>
    exact_by_kernel isIso_of_isIso_map_leftDerivedUpperStar_id T₀ _
      (sqρ.2 (by exact_by_kernel isIso_kunnethMap_leftDerivedUpperStar_id T₀ μS νS σM A B hS))
  exact_by_kernel hG

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
