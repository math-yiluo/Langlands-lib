/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux

/-!
# Derived tensor products and duals of lisse `𝒪_E`-sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `Z` a scheme
with noetherian underlying space. A lisse `𝒪_E`-sheaf on `Z` (a pro-étale locally finitely
presented module object over `𝒪̲_{E,Z}`) is pro-étale locally isomorphic to a constant module
`⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` (`ProEtale.exists_cover_iso_integralConstantModule`). Hence:

* if `A` and `L` are bounded complexes with lisse cohomology sheaves, then `A ⊗ᴸ L` is bounded
  constructible
  (`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_tensorObj_of_lisse_homology`):
  by dévissage in both variables it suffices to treat `P[0] ⊗ᴸ N[0]` for lisse `P` and `N`, whose
  cohomology sheaves are computed, on a common trivializing cover, by
  `ProEtale.CondensedRing.integralConstantModule_tensorObj_homology`;
* a lisse sheaf `P` placed in degree `q` is dualizable in `D(Mod_{𝒪_{E,Z}})`, with a bounded left
  dual whose cohomology sheaves are lisse
  (`PadicIntegersRingObj.exists_exactPairing_singleFunctor_of_isLocallyFinitelyPresented`):
  dualizability is detected by the derived pullbacks to the members of a trivializing pro-étale
  cover (`ProEtale.CondensedRing.isDualizable_of_cover`), which are monoidal, jointly conservative
  and commute with internal homs, and the pullbacks of the dual are the duals of constant modules
  (`ProEtale.CondensedRing.exists_exactPairing_integralConstantModule`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- In a braided monoidal category, a dualizable object has a left dual. -/
lemma IsDualizable.exists_exactPairing {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] {X : C} (hX : IsDualizable X) : ∃ Y : C, Nonempty (ExactPairing Y X) := by
  obtain ⟨_⟩ := hX
  exact ⟨Xᘁ, ⟨BraidedCategory.exactPairing_swap X Xᘁ⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- If the pullback of `M` along `f` is constant, so is its pullback along `a ≫ f`. -/
lemma nonempty_upperStar_comp_iso_integralConstantModule {Y W V : Scheme.{u}} (a : Y ⟶ W)
    (f : W ⟶ V) {M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)}
    (ϖ : PadicAlgCl.integers ℓ E) (k r : ℕ) (e : Fin k → ℕ)
    (eM : (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M ≅
      integralConstantModule ℓ E W ϖ k r e) :
    Nonempty ((a ≫ f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M ≅
      integralConstantModule ℓ E Y ϖ k r e) := by
  obtain ⟨e'⟩ := nonempty_upperStar_integralConstantModule_iso ℓ E a ϖ k r e
  exact ⟨(upperStarComp (Profinite.padicIntegersRingObj ℓ E) a f).app M ≪≫
    (upperStar (Profinite.padicIntegersRingObj ℓ E) a).mapIso eM ≪≫ e'⟩

/-- **A common trivializing cover.** Two lisse `𝒪_E`-sheaves on a scheme with noetherian
underlying space are simultaneously constant on the members of some pro-étale cover. -/
theorem exists_cover_iso_integralConstantModule_pair (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {P N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) N)
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z, ∀ i,
      (∃ (k r : ℕ) (e : Fin k → ℕ),
        Nonempty ((𝒲.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj P ≅
          integralConstantModule ℓ E (𝒲.X i) ϖ k r e)) ∧
      (∃ (k r : ℕ) (e : Fin k → ℕ),
        Nonempty ((𝒲.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj N ≅
          integralConstantModule ℓ E (𝒲.X i) ϖ k r e)) := by
  obtain ⟨𝒰, h𝒰⟩ := ProEtale.exists_cover_iso_integralConstantModule ℓ E Z hP ϖ hϖ
  obtain ⟨𝒱, h𝒱⟩ := ProEtale.exists_cover_iso_integralConstantModule ℓ E Z hN ϖ hϖ
  have hQ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)) ⦃Y W : Scheme.{u}⦄
      (a : Y ⟶ W) (f : W ⟶ Z)
      (h : ∃ (k r : ℕ) (e : Fin k → ℕ), Nonempty ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M ≅
        integralConstantModule ℓ E W ϖ k r e)) :
      ∃ (k r : ℕ) (e : Fin k → ℕ),
        Nonempty ((a ≫ f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M ≅
          integralConstantModule ℓ E Y ϖ k r e) := by
    obtain ⟨k, r, e, ⟨eM⟩⟩ := h
    exact ⟨k, r, e, nonempty_upperStar_comp_iso_integralConstantModule ℓ E a f ϖ k r e eM⟩
  exact exists_cover_forall_and _ _ (hQ P) (hQ N) 𝒰 𝒱 h𝒰 h𝒱

/-- The derived tensor product `P[0] ⊗ᴸ N[0]` of two lisse `𝒪_E`-sheaves has lisse cohomology
sheaves, concentrated in degrees `-1` and `0`: on a common trivializing cover, it is the derived
tensor product of two constant modules. -/
theorem isLocallyFinitelyPresented_homology_singleFunctor_tensorObj (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {P N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) N)
    (n : ℤ) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj P ⊗
            (DerivedCategory.singleFunctor _ 0).obj N)) ∧
      ((n < -1 ∨ 0 < n) → IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj P ⊗
            (DerivedCategory.singleFunctor _ 0).obj N))) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨𝒲, h𝒲⟩ := exists_cover_iso_integralConstantModule_pair ℓ E Z hP hN ϖ hϖ
  have key (i : 𝒲.I₀) :
      IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒲.X i))
        ((DerivedCategory.homologyFunctor _ n).obj
          ((L((𝒲.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj P ⊗
              (DerivedCategory.singleFunctor _ 0).obj N))) ∧
      ((n < -1 ∨ 0 < n) → IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((L((𝒲.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj P ⊗
              (DerivedCategory.singleFunctor _ 0).obj N)))) := by
    obtain ⟨⟨k, r, e, ⟨eP⟩⟩, ⟨k', r', e', ⟨eN⟩⟩⟩ := h𝒲 i
    have h := integralConstantModule_tensorObj_homology ℓ E (𝒲.X i) ϖ hϖ k r k' r' e e' n
    let eT := (Functor.Monoidal.μIso L((𝒲.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) _ _).symm ≪≫
      tensorIso
        (leftDerivedUpperStarSingleIso _ _ P ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eP)
        (leftDerivedUpperStarSingleIso _ _ N ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eN)
    exact ⟨h.1.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso eT).symm,
      fun hn ↦ (h.2 hn).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso eT)⟩
  exact ⟨isLocallyFinitelyPresented_homology_of_cover 𝒲 _ n fun i ↦ (key i).1,
    fun hn ↦ isZero_homology_of_cover 𝒲 _ n fun i ↦ (key i).2 hn⟩

/-- The derived tensor product `P[0] ⊗ᴸ N[0]` of two lisse `𝒪_E`-sheaves is bounded
constructible. -/
theorem boundedConstructible_singleFunctor_tensorObj_singleFunctor (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {P N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) N) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.singleFunctor _ 0).obj P ⊗ (DerivedCategory.singleFunctor _ 0).obj N) :=
  boundedConstructible_of_isLocallyFinitelyPresented_homology_of_le (-1) 0
    (fun n ↦ (isLocallyFinitelyPresented_homology_singleFunctor_tensorObj ℓ E Z hP hN n).2)
    (fun n ↦ (isLocallyFinitelyPresented_homology_singleFunctor_tensorObj ℓ E Z hP hN n).1)

/-- **The derived tensor product of complexes with lisse cohomology.** If `A` and `L` are bounded
complexes of `𝒪̲_E`-module objects on a scheme with noetherian underlying space, whose cohomology
sheaves are lisse, then `A ⊗ᴸ L` is bounded constructible. -/
theorem boundedConstructible_tensorObj_of_lisse_homology (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : DerivedCategory.TStructure.t.bounded L)
    (hL' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj L)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) (A ⊗ L) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)) :=
    ⟨fun e h ↦ h.of_iso e⟩
  refine DerivedCategory.prop_of_bounded
    ((boundedConstructible _).inverseImage ((curriedTensor _).flip.obj L))
    (IsLocallyFinitelyPresented _) (fun P hP ↦ ?_) A hA hA'
  exact DerivedCategory.prop_of_bounded
    ((boundedConstructible _).inverseImage
      ((curriedTensor _).obj ((DerivedCategory.singleFunctor _ 0).obj P)))
    (IsLocallyFinitelyPresented _)
    (fun N hN ↦ boundedConstructible_singleFunctor_tensorObj_singleFunctor ℓ E Z hP hN) L hL hL'

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- On the members of a trivializing pro-étale cover of a lisse `𝒪_E`-sheaf `P`, the pullback of
`P[q]` has a left dual concentrated in degrees `[-q, 1 - q]` with lisse cohomology sheaves. -/
theorem exists_exactPairing_leftDerivedUpperStar_singleFunctor {Z W : Scheme.{u}} (g : W ⟶ Z)
    {P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) (k r : ℕ)
    (e : Fin k → ℕ)
    (eP : (g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj P ≅ integralConstantModule ℓ E W ϖ k r e)
    (q : ℤ) :
    ∃ D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W)),
      D.IsGE (-q) ∧ D.IsLE (1 - q) ∧
      (∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W)
        ((DerivedCategory.homologyFunctor _ n).obj D)) ∧
      Nonempty (ExactPairing D ((L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
        ((DerivedCategory.singleFunctor _ q).obj P))) := by
  obtain ⟨D, h₁, h₂, h₃, ⟨_⟩⟩ := exists_exactPairing_integralConstantModule ℓ E W ϖ hϖ k r e q
  exact ⟨D, h₁, h₂, h₃, ⟨exactPairingCongr (Iso.refl _)
    (leftDerivedUpperStarSingleFunctorIso _ g P q ≪≫
      (DerivedCategory.singleFunctor _ q).mapIso eP)⟩⟩

/-- **Duals of lisse sheaves.** A lisse `𝒪_E`-sheaf `P` on a scheme with noetherian underlying
space, placed in degree `q`, is dualizable in `D(Mod_{𝒪_{E,Z}})`, with a bounded left dual whose
cohomology sheaves are lisse. -/
theorem exists_exactPairing_singleFunctor_of_isLocallyFinitelyPresented (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) P)
    (q : ℤ) :
    ∃ D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)),
      DerivedCategory.TStructure.t.bounded D ∧
      (∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
        ((DerivedCategory.homologyFunctor _ n).obj D)) ∧
      Nonempty (ExactPairing D ((DerivedCategory.singleFunctor _ q).obj P)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  obtain ⟨𝒰, h𝒰⟩ := ProEtale.exists_cover_iso_integralConstantModule ℓ E Z hP ϖ hϖ
  have hloc (i : 𝒰.I₀) : ∃ D' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (𝒰.X i))
      Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒰.X i))),
      D'.IsGE (-q) ∧ D'.IsLE (1 - q) ∧
      (∀ n, IsLocallyFinitelyPresented
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒰.X i))
        ((DerivedCategory.homologyFunctor _ n).obj D')) ∧
      Nonempty (ExactPairing D' ((L((𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
        ((DerivedCategory.singleFunctor _ q).obj P))) := by
    obtain ⟨k, r, e, ⟨eP⟩⟩ := h𝒰 i
    exact exists_exactPairing_leftDerivedUpperStar_singleFunctor ℓ E (𝒰.f i) ϖ hϖ k r e eP q
  -- dualizability is detected by the derived pullbacks to the members of the cover
  have hX : IsDualizable ((DerivedCategory.singleFunctor _ q).obj P) :=
    isDualizable_of_cover 𝒰 fun i ↦ by
      obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Mod (Sheaf
        (Scheme.ProEt.topology (𝒰.X i)) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒰.X i)))
      obtain ⟨D', -, -, -, ⟨_⟩⟩ := hloc i
      let _ := BraidedCategory.exactPairing_swap D'
        ((L((𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
          ((DerivedCategory.singleFunctor _ q).obj P))
      exact ⟨{ rightDual := D' }⟩
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Mod (Sheaf (Scheme.ProEt.topology Z)
    Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))
  obtain ⟨Y, ⟨pY⟩⟩ := hX.exists_exactPairing
  -- the pullbacks of the dual `Y` are the duals of the pullbacks of `P[q]`
  have hD (i : 𝒰.I₀) : ∃ D' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (𝒰.X i))
      Ab.{u + 1}) (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒰.X i))),
      D'.IsGE (-q) ∧ D'.IsLE (1 - q) ∧
      (∀ n, IsLocallyFinitelyPresented
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) (𝒰.X i))
        ((DerivedCategory.homologyFunctor _ n).obj D')) ∧
      Nonempty ((L((𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj Y ≅ D') := by
    obtain ⟨D', h₁, h₂, h₃, ⟨p⟩⟩ := hloc i
    exact ⟨D', h₁, h₂, h₃, nonempty_leftDerivedUpperStar_obj_iso_of_exactPairing (𝒰.f i) pY p⟩
  refine ⟨Y, ?_, fun n ↦ isLocallyFinitelyPresented_homology_of_cover 𝒰 _ n fun i ↦ ?_,
    ⟨pY⟩⟩
  · rw [← DerivedCategory.exists_homologyConcentratedIn_iff_bounded]
    refine ⟨-q, 1 - q, (DerivedCategory.isGE_iff _ _).2 fun n hn ↦
      isZero_homology_of_cover 𝒰 _ n fun i ↦ ?_, (DerivedCategory.isLE_iff _ _).2 fun n hn ↦
      isZero_homology_of_cover 𝒰 _ n fun i ↦ ?_⟩
    · obtain ⟨D', h₁, -, -, ⟨e⟩⟩ := hD i
      exact (D'.isZero_of_isGE (-q) n hn).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)
    · obtain ⟨D', -, h₂, -, ⟨e⟩⟩ := hD i
      exact (D'.isZero_of_isLE (1 - q) n hn).of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e)
  · obtain ⟨D', -, -, h₃, ⟨e⟩⟩ := hD i
    exact (h₃ n).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e).symm

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
