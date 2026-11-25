/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsFreeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClRetraction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeFiniteCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-!
# Descent of lisse `ℚ̄_ℓ`-sheaves to a finite subextension

This file is the lisse descent of PR #1740 (`Colimit/LisseDescent.lean` there), placed in the
namespace `ProEtale.FiniteSubfieldDescent` and with the retraction `ℚ̄_ℓ,X ⟶ E_X` inlined, so that
it does not import `Colimit/DerivedExtendScalars.lean`, which clashes with
`Colimit/TwoColimit.lean` on this branch.

Let `ℓ` be a prime and `S` a quasi-compact quasi-separated scheme. Every lisse (finite locally
free) `ℚ̄_ℓ,S`-module `L` is the extension of scalars `ℚ̄_ℓ,S ⊗_{E_S} L_E` of a lisse
`E_S`-module `L_E`, for some finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`ProEtale.exists_isLocallyFree_extendScalars_iso`, blueprint
`lemma-descent-lisse-qbar-sheaves-finite--1` (1)).

The proof: `S` being quasi-compact, `L` is trivialised on a finite pro-étale cover by affine
schemes `V_k` (`ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`). The fibre
products `V_j ×_S V_k` are quasi-compact and quasi-separated, so the global sections of
`ℚ̄_ℓ = colim_E E` over them are the filtered colimit of those of the `E`
(`ProEtale.exists_subfieldToPadicAlgClSection_eq`, blueprint
`lemma-descent-lisse-qbar-sheaves-finite--1` (2)): the finitely many entries of the transition
matrices and of their inverses come from a common `E_{V_j ×_S V_k}`
(`ProEtale.exists_forall_le_isDefinedOver`). The lattices spanned by the bases then glue to a
lisse `E_S`-module
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`),
the units `E^n ⟶ ℚ̄_ℓ^n` being split injective by the retraction `ℚ̄_ℓ ⟶ E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace FiniteSubfieldDescent

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {ℓ} in
/-- A global section of `ℚ̄_ℓ,X` over a quasi-compact quasi-separated scheme comes from `E_X`
for every large enough finite subextension `E`. -/
lemma exists_forall_le_subfieldToPadicAlgClSection_eq {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (s : Γ (padicAlgClRingObj X ℓ)) :
    ∃ E₀ : FiniteIntermediateField ℓ, ∀ E, E₀ ≤ E →
      ∃ t : Γ (padicSubfieldRingObj X ℓ E), subfieldToPadicAlgClSection ℓ X E t = s := by
  obtain ⟨E₀, f, rfl⟩ := exists_subfieldToPadicAlgClSection_eq s
  exact ⟨E₀, fun E h ↦ ⟨_, subfieldToPadicAlgClSection_map h _⟩⟩

/-- Finitely many finite subextensions are contained in a common one. -/
lemma exists_forall_le_finiteIntermediateField {J : Type*} [Finite J]
    (E : J → FiniteIntermediateField ℓ) : ∃ F, ∀ i, E i ≤ F := by
  classical
  have := Fintype.ofFinite J
  obtain ⟨F, hF⟩ := Finset.exists_le (Finset.univ.image E)
  exact ⟨F, fun i ↦ hF _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

variable {ℓ} in
/-- A morphism `p^* ℚ̄_ℓ,V^n ⟶ p'^* ℚ̄_ℓ,V'^m` over a quasi-compact quasi-separated scheme `P` is
defined over `E` for every large enough finite subextension `E`: its finitely many matrix entries
are global sections of `ℚ̄_ℓ,P`. -/
lemma exists_forall_le_isDefinedOver {P V V' : Scheme.{u}} [CompactSpace P]
    [QuasiSeparatedSpace P] (p : P ⟶ V) (p' : P ⟶ V') {n m : ℕ}
    (Y : (p)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (Mod.finiteFree (padicAlgClRingObj V ℓ) n) ⟶
      (p')^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (Mod.finiteFree (padicAlgClRingObj V' ℓ) m)) :
    ∃ E₀ : FiniteIntermediateField ℓ, ∀ E, E₀ ≤ E →
      CondensedRing.IsDefinedOver (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p p' Y := by
  choose s hs using fun i j ↦ Mod.regularEndRingHom_bijective.2 <| .of
    ((CondensedRing.upperStarObjRegularIso _ p).inv ≫
      (p)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (biproduct.ι (fun _ : Fin n ↦ Mod.regular (padicAlgClRingObj V ℓ)) i) ≫ Y ≫
      (p')^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (biproduct.π (fun _ : Fin m ↦ Mod.regular (padicAlgClRingObj V' ℓ)) j) ≫
      (CondensedRing.upperStarObjRegularIso _ p').hom)
  choose E₀ hE₀ using fun ij : Fin n × Fin m ↦
    exists_forall_le_subfieldToPadicAlgClSection_eq (s ij.1 ij.2)
  obtain ⟨F, hF⟩ := exists_forall_le_finiteIntermediateField ℓ E₀
  refine ⟨F, fun E hE i j ↦ ?_⟩
  obtain ⟨t, ht⟩ := hE₀ (i, j) E ((hF (i, j)).trans hE)
  refine ⟨t, ?_⟩
  simpa only [← ht] using (congrArg End.asHom (hs i j)).symm

variable {ℓ} in
/-- The unit `M ⟶ ℚ̄_ℓ,X ⊗_{E_X} M` is a monomorphism: it has the retraction induced by the
`E_X`-linear retraction `ℚ̄_ℓ,X ⟶ E_X`. -/
lemma mono_extendRestrictAdjunction_unit_app_padicSubfieldRingObjToPadicAlgCl
    (X : Scheme.{u}) (E : FiniteIntermediateField ℓ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    Mono ((Mod.extendRestrictAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)).unit.app M) :=
  have h := Mod.extendRestrictAdjunction_unit_comp_extendScalarsRetraction _
    ((upperStarFromPoint X).map (Profinite.padicAlgClRetraction ℓ E)) (by
      rw [← Functor.map_comp, Profinite.padicSubfieldRingObjToPadicAlgCl_comp_padicAlgClRetraction,
        CategoryTheory.Functor.map_id])
    (Functor.LaxMonoidal.map_whiskerRight_comp_mul_comp_map (upperStarFromPoint X) _ _
      (Profinite.padicSubfieldRingObjToPadicAlgCl_whiskerRight_comp_mul_comp_padicAlgClRetraction
        ℓ E))
    (Functor.LaxMonoidal.map_whiskerLeft_comp_mul_comp_map (upperStarFromPoint X) _ _
      (Profinite.whiskerLeft_padicSubfieldRingObjToPadicAlgCl_comp_mul_comp_padicAlgClRetraction
        ℓ E))
  (SplitMono.mk _ (by simpa using NatTrans.congr_app h M)).mono

/-- Blueprint `lemma-descent-lisse-qbar-sheaves-finite--1` (1): for a quasi-compact
quasi-separated scheme `S` and a lisse `ℚ̄_ℓ,S`-module `L`, there are a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a lisse `E_S`-module `L_E` with `ℚ̄_ℓ,S ⊗_{E_S} L_E ≅ L`. See the
module docstring. -/
theorem exists_isLocallyFree_extendScalars_iso (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S]
    (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicAlgClRingObj S ℓ))
    (hL : IsLocallyFree (padicAlgClRingObj S ℓ) L) :
    ∃ (E : FiniteIntermediateField ℓ)
      (L' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicSubfieldRingObj S ℓ E)),
      IsLocallyFree (padicSubfieldRingObj S ℓ E) L' ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl S ℓ E)).obj L' ≅ L) := by
  obtain ⟨𝒰, h𝒰, haff, hfree⟩ :=
    CondensedRing.exists_finite_affine_cover_isFree_upperStar hL
  choose n e using hfree
  let e' (k : 𝒰.I₀) := (e k).some.symm
  have hP (j k : 𝒰.I₀) := IsPullback.of_hasPullback (𝒰.f j) (𝒰.f k)
  have hdef (j k : 𝒰.I₀) : ∃ E₀ : FiniteIntermediateField ℓ, ∀ E, E₀ ≤ E →
      CondensedRing.IsDefinedOver (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (pullback.fst (𝒰.f j) (𝒰.f k)) (pullback.snd (𝒰.f j) (𝒰.f k))
          (CondensedRing.finiteFreeTransition (hP j k) (e' j) (e' k)).hom ∧
        CondensedRing.IsDefinedOver (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
          (pullback.snd (𝒰.f j) (𝒰.f k)) (pullback.fst (𝒰.f j) (𝒰.f k))
          (CondensedRing.finiteFreeTransition (hP j k) (e' j) (e' k)).inv := by
    have := haff j
    have := haff k
    obtain ⟨_, _⟩ := compactSpace_quasiSeparatedSpace_of_isPullback (hP j k)
    obtain ⟨E₁, hE₁⟩ := exists_forall_le_isDefinedOver _ _
      (CondensedRing.finiteFreeTransition (hP j k) (e' j) (e' k)).hom
    obtain ⟨E₂, hE₂⟩ := exists_forall_le_isDefinedOver _ _
      (CondensedRing.finiteFreeTransition (hP j k) (e' j) (e' k)).inv
    obtain ⟨E₀, h₁, h₂⟩ := exists_le_le ℓ E₁ E₂
    exact ⟨E₀, fun E hE ↦ ⟨hE₁ E (h₁.trans hE), hE₂ E (h₂.trans hE)⟩⟩
  choose E₀ hE₀ using hdef
  obtain ⟨E, hE⟩ := exists_forall_le_finiteIntermediateField ℓ fun jk : 𝒰.I₀ × 𝒰.I₀ ↦ E₀ jk.1 jk.2
  obtain ⟨L', hL', ⟨i⟩⟩ := CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) L 𝒰 e' hP
    (fun k ↦ mono_extendRestrictAdjunction_unit_app_padicSubfieldRingObjToPadicAlgCl _ E _)
    fun j k ↦ hE₀ j k E (hE (j, k))
  exact ⟨E, L', hL', ⟨i⟩⟩

end FiniteSubfieldDescent

end AlgebraicGeometry.ProEtale
