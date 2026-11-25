/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeTransition

/-!
# Values of sections of `E_X` and integral sections

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`. For a scheme `W`, the endomorphisms of the regular
module `E_W` are the global sections of `E_W`, that is the continuous functions `W → E`; the
restriction along `g : W' ⟶ W` is the precomposition with `g`
(`AlgebraicGeometry.ProEtale.exists_subfieldEndRingEquiv`). An endomorphism whose function takes
values in `𝒪_E` is the extension of a global section of `𝒪_{E,W}`.

We also show that the units `𝒪_{E,V}ⁿ ⟶ E_V ⊗ 𝒪_{E,V}ⁿ` are monomorphisms
(`AlgebraicGeometry.ProEtale.mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers`):
the inclusion `𝒪_{E,V} ⟶ E_V` is a monomorphism, `𝒪̲_E ⟶ E̲` being injective on sections and
`p_V^*` exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-! ### Integral sections -/

/-- The inclusion `𝒪_{E,W} ⟶ E_W` on global sections is the postcomposition of continuous
functions `W → 𝒪_E` with the inclusion `𝒪_E ⊆ E`. -/
lemma Γ_map_padicIntegersToPadicSubfield (W : Scheme.{u}) :
    letI := normedFieldOfAlgebra ℓ E.1
    ∀ h : C(W, integers ℓ E.1),
      Γ.map (padicIntegersToPadicSubfield W ℓ E)
          (continuousMapCoefficientSectionRingHom W (integers ℓ E.1) h) =
        continuousMapCoefficientSectionRingHom W E.1
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(integers ℓ E.1, E.1)).comp h) := by
  let := normedFieldOfAlgebra ℓ E.1
  have := isUltrametricDist_ofAlgebra ℓ E.1
  intro h
  have hn := continuousMapComparison_naturality W (integers ℓ E.1).subtype continuous_subtype_val
  have hn' : inv (continuousMapComparison W (integers ℓ E.1)) ≫
      padicIntegersToPadicSubfield W ℓ E =
      (sheafCompose (ProEt.topology W) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap W (integers ℓ E.1).subtype continuous_subtype_val) ≫
        inv (continuousMapComparison W E.1) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
    rfl
  refine Γ.ext ?_
  rw [Γ.map_hom, continuousMapCoefficientSectionRingHom_hom,
    continuousMapCoefficientSectionRingHom_hom, Category.assoc, hn', ← Category.assoc]
  congr 1
  refine Sheaf.unitHomEval_injective (J := ProEt.topology W) (ProEt.isTerminalMkId W) _ ?_
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology W) _ _ _).trans ?_
  rw [unitHomEval_continuousMapSectionRingHom, unitHomEval_continuousMapSectionRingHom]
  rfl

/-! ### Values of endomorphisms of `E_W` -/

/-- **Values of sections of `E_W`.** There are ring isomorphisms from the endomorphisms of the
regular modules `E_W` onto the continuous functions `W → E`, compatible with restriction along
morphisms `g : W' ⟶ W` (precomposition with `g`), such that an endomorphism whose function
takes values in `𝒪_E` is the extension of a global section of `𝒪_{E,W}`. -/
theorem exists_subfieldEndRingEquiv :
    ∃ ev : ∀ W : Scheme.{u},
        End (Mod.regular (padicSubfieldRingObj W ℓ E)) ≃+* C(W, E),
      (∀ (W' W : Scheme.{u}) (g : W' ⟶ W) (t : End (Mod.regular (padicSubfieldRingObj W ℓ E)))
        (x : W'), ev W' (restrictEnd (Profinite.continuousMapRingObj E) g t) x = ev W t (g x)) ∧
      ∀ (W : Scheme.{u}) (t : End (Mod.regular (padicSubfieldRingObj W ℓ E))),
        (∀ x, ‖ev W t x‖ ≤ 1) →
          ∃ s : Γ (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W),
            Mod.regularEndRingHom (Γ.map (padicIntegersToPadicSubfield W ℓ E) s) = t := by
  let e (W : Scheme.{u}) : C(W, E) ≃+*
      End (Mod.regular (padicSubfieldRingObj W ℓ E)) :=
    RingEquiv.ofBijective
      (Mod.regularEndRingHom.comp (subfieldSectionRingHom ℓ W E))
      (Mod.regularEndRingHom_bijective.comp (subfieldSectionRingHom_bijective ℓ W E))
  have key (W : Scheme.{u}) (f : C(W, E)) :
      (e W).symm (Mod.regularEndRingHom (subfieldSectionRingHom ℓ W E f)) = f :=
    (e W).symm_apply_apply f
  have inverse (W : Scheme.{u}) (t : End (Mod.regular (padicSubfieldRingObj W ℓ E))) :
      Mod.regularEndRingHom (subfieldSectionRingHom ℓ W E ((e W).symm t)) = t :=
    (e W).apply_symm_apply t
  refine ⟨fun W ↦ (e W).symm, ?_, ?_⟩
  · intro W' W g t x
    have h := restrictEnd_regularEndRingHom (Profinite.continuousMapRingObj E) g
      (subfieldSectionRingHom ℓ W E ((e W).symm t))
    rw [inverse, Γ_map_condensedPullbackHom_subfieldSectionRingHom] at h
    rw [h, key]
    rfl
  · intro W t ht
    let f := (e W).symm t
    let := normedFieldOfAlgebra ℓ E.1
    have hmem (x : W) : f x ∈ integers ℓ E.1 :=
      (mem_integers_iff_norm_le_one_intermediateField _).2 (ht x)
    let h : C(W, integers ℓ E.1) := ⟨fun x ↦ ⟨f x, hmem x⟩,
      (continuous_induced_rng.2 (continuous_subtype_val.comp f.continuous)).subtype_mk _⟩
    refine ⟨continuousMapCoefficientSectionRingHom W (integers ℓ E.1) h, ?_⟩
    rw [Γ_map_padicIntegersToPadicSubfield]
    exact inverse W t

/-! ### The units `𝒪_{E,V}ⁿ ⟶ E_V ⊗ 𝒪_{E,V}ⁿ` are monomorphisms -/

/-- The inclusion `𝒪̲_E ⟶ E̲` is a monomorphism of condensed abelian groups. -/
instance mono_padicIntegersRingObjToContinuousMapRingObj :
    Mono (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  have (S : Profinite.{u}ᵒᵖ) :
      Mono ((padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E).hom.app S) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    have h' (s : S.unop) : ((a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.1)).down s :
        E.1) = (b : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E.1)).down s :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E.1) ↦ z.down s) h
    exact ULift.ext (ContinuousMap.ext fun s ↦ Subtype.ext (h' s))
  have := NatTrans.mono_of_mono_app (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E).hom
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The inclusion `𝒪_{E,V} ⟶ E_V` is a monomorphism, `p_V^*` being left exact. -/
instance mono_padicIntegersToPadicSubfield (V : Scheme.{u}) :
    Mono (padicIntegersToPadicSubfield V ℓ E) :=
  (upperStarFromPoint V).map_mono _

/-- **The units `𝒪_{E,V}ⁿ ⟶ E_V ⊗ 𝒪_{E,V}ⁿ` are monomorphisms.** -/
lemma mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers (V : Scheme.{u})
    (n : ℕ) :
    Mono ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield V ℓ E)).unit.app
      (Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V) n)) := by
  set φ := padicIntegersToPadicSubfield V ℓ E
  have hreg : Mono (Mod.regularHomComap φ) :=
    (Mod.forget _).mono_of_mono_map (by
      change Mono φ
      infer_instance)
  set u := (Mod.extendRestrictAdjunction φ).unit.app
    (Mod.finiteFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) V) n) ≫
    (Mod.comap φ).map (Mod.finiteFreeIsoMap (Mod.extendScalars φ)
      (Mod.extendScalarsObjRegularIso φ) n).hom
  have hu (i : Fin n) : u ≫ (Mod.comap φ).map
      (biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj E.1) V)) i) =
      biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
        (Profinite.padicIntegersRingObj ℓ E.1) V)) i ≫ Mod.regularHomComap φ := by
    have hn := (Mod.extendRestrictAdjunction φ).unit.naturality
      (biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
        (Profinite.padicIntegersRingObj ℓ E.1) V)) i)
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [Category.assoc, ← Functor.map_comp, Mod.finiteFreeIsoMap_hom_comp_π, Functor.map_comp,
      ← reassoc_of% hn, Mod.extendRestrictAdjunction_unit_app_regular_comp_comap_map]
  have : Mono u := by
    refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    rw [zero_comp, ← cancel_mono (Mod.regularHomComap φ), zero_comp, Category.assoc, ← hu,
      reassoc_of% hg, zero_comp]
  exact mono_of_mono _ ((Mod.comap φ).map (Mod.finiteFreeIsoMap (Mod.extendScalars φ)
      (Mod.extendScalarsObjRegularIso φ) n).hom)

end AlgebraicGeometry.ProEtale
