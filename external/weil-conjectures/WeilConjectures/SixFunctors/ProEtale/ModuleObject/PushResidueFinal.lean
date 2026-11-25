/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlatOfAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueInputsAcyclic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.TorsionFreeResolutionProEtale

/-!
# The derived (Push) comparison along `𝒪_E ⟶ 𝔽_E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
residue field `𝔽_E`, and `f : X ⟶ Y` a morphism of schemes. We show that the comparison
`𝔽_E ⊗ᴸ Rf_* K ⟶ Rf_*(𝔽_E ⊗ᴸ K)` is an isomorphism for every bounded below `K ∈ D(𝒪_{E,X})`
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`).

The proof applies the criterion
`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_isStrictlyGE`
to a torsion-free `f_*`-acyclic resolution `J` of `K`
(`ProEtale.CondensedRing.exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_padicIntegers`),
built from the inclusion `𝒪_{E,X} ⟶ E_X`: it is a monomorphism
(`ProEtale.mono_padicIntegersToSubfieldRingObj`), `E_X` is flat over
`𝒪_{E,X}`, a uniformizer `ϖ` acts invertibly on `E_X`
(`ProEtale.isIso_regularEndSMul_comap_padicSubfield_hom`), and `E_X` is the
pullback of `E_Y` (`ProEtale.CondensedRing.upperStarComapPadicSubfieldIso`).
Since `ϖ` acts injectively on the terms of `J` and of `f_* J`, the derived extensions of scalars
are computed levelwise, the reductions `J^k ⧸ ϖ` are `f_*`-acyclic (long exact sequence) and the
underived (Push) comparison is invertible on each `J^k`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] Bimod.monoidalCategory

namespace Profinite

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- Multiplications by constants compose. -/
lemma continuousMapRingObjMulLeft_comp (s t : T) :
    continuousMapRingObjMulLeft.{u} T s ≫ continuousMapRingObjMulLeft T t =
      continuousMapRingObjMulLeft T (t * s) := by
  ext S a
  exact ULift.ext (ContinuousMap.ext fun _ ↦ (mul_assoc t s _).symm)

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (ϖ : PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪̲_E ⟶ E̲` is a monomorphism of condensed abelian groups. -/
instance mono_padicIntegersRingObjToSubfieldRingObj :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Mono (Profinite.padicIntegersRingObjToSubfieldRingObj.{u} ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have (S : Profinite.{u}ᵒᵖ) :
      Mono ((Profinite.padicIntegersRingObjToSubfieldRingObj.{u} ℓ E).hom.app S) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b h
    have h' (s : S.unop) : ((a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)).down s :
        E) = (b : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)).down s :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E) ↦ z.down s) h
    exact ULift.ext (ContinuousMap.ext fun s ↦ Subtype.ext (h' s))
  have := NatTrans.mono_of_mono_app (Profinite.padicIntegersRingObjToSubfieldRingObj.{u} ℓ E).hom
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The inclusion `𝒪_{E,X} ⟶ E_X` is a monomorphism, `p_X^*` being exact. -/
instance mono_padicIntegersToSubfieldRingObj : Mono (padicIntegersToSubfieldRingObj X ℓ E) :=
  (upperStarFromPoint X).map_mono _

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The inclusion `𝒪̲_E ⟶ E̲` sends the constant global section `ϖ` to the constant global
section `ϖ`. -/
lemma continuousMapConstRingHom_hom_comp_padicIntegersRingObjToSubfieldRingObj :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    (Profinite.continuousMapConstRingHom.{u} (PadicAlgCl.integers ℓ E) ϖ).hom ≫
      Profinite.padicIntegersRingObjToSubfieldRingObj ℓ E =
      (Profinite.continuousMapConstRingHom.{u} E (ϖ : E)).hom := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [← MonObj.Γ.map_hom]
  exact congrArg MonObj.Γ.hom (Sheaf.Γ_map_ringHomΓSheafCompose _
    (Profinite.continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype
      continuous_subtype_val) (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl)
      (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl) (r := ϖ) (r' := (ϖ : E))
      fun _ ↦ rfl)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- `ϖ` acts by an isomorphism on the restriction of scalars of `E_X`, if `ϖ ≠ 0` in `E`. -/
lemma isIso_regularEndSMul_comap_padicSubfield_hom (hϖ : (ϖ : E) ≠ 0) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    IsIso (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)
      ((Mod.comap (padicIntegersToSubfieldRingObj X ℓ E)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)))).hom := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [regularEndSMul_padicIntegersRegularEnd_hom, Mod.globalSmul_comap, padicIntegersConstSection,
    Category.assoc, ← Functor.map_comp,
    continuousMapConstRingHom_hom_comp_padicIntegersRingObjToSubfieldRingObj]
  erw [Mod.globalSmul_regular_obj (upperStarFromPoint X)]
  rw [Profinite.globalSmul_continuousMapConstRingHom]
  have : IsIso (Profinite.continuousMapRingObjMulLeft.{u} E (ϖ : E)) :=
    ⟨Profinite.continuousMapRingObjMulLeft E (ϖ : E)⁻¹, by
      rw [Profinite.continuousMapRingObjMulLeft_comp, inv_mul_cancel₀ hϖ,
        Profinite.continuousMapRingObjMulLeft_one], by
      rw [Profinite.continuousMapRingObjMulLeft_comp, mul_inv_cancel₀ hϖ,
        Profinite.continuousMapRingObjMulLeft_one]⟩
  infer_instance

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- `ϖ` acts by an epimorphism on the restriction of scalars of `E_X`, if `ϖ ≠ 0` in `E`. -/
lemma epi_regularEndSMul_comap_padicSubfield (hϖ : (ϖ : E) ≠ 0) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Epi (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)
      ((Mod.comap (padicIntegersToSubfieldRingObj X ℓ E)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)))) := by
  have := isIso_regularEndSMul_comap_padicSubfield_hom X ℓ E ϖ hϖ
  exact (Mod.forget _).epi_of_epi_map (inferInstanceAs (Epi (Mod.regularEndSMul _ _).hom))

namespace CondensedRing

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of the `𝒪_{E,Y}`-module `E_Y` is the `𝒪_{E,X}`-module `E_X`. -/
noncomputable def upperStarComapPadicSubfieldIso :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj
        ((Mod.comap (padicIntegersToSubfieldRingObj Y ℓ E)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) Y))) ≅
      (Mod.comap (padicIntegersToSubfieldRingObj X ℓ E)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ((comapUpperStarIso (Profinite.padicIntegersRingObjToSubfieldRingObj ℓ E) f).app _).symm ≪≫
    (Mod.comap _).mapIso (Functor.Monoidal.εIso (f)^*⟦Profinite.continuousMapRingObj E⟧).symm

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- A generator of the maximal ideal of `𝒪_E` is nonzero in `E`. -/
lemma coe_ne_zero_of_maximalIdeal_eq_span {ϖ : PadicAlgCl.integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ϖ : E) ≠ 0 := by
  intro h
  have h₀ : ϖ = 0 := Subtype.ext h
  have hℓ := PadicAlgCl.natCast_mem_maximalIdeal_integers ℓ E
  rw [hϖ, h₀, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hℓ
  have hℓ' : ((ℓ : PadicAlgCl.integers ℓ E) : E) = 0 := by rw [hℓ]; rfl
  exact Profinite.natCast_ne_zero_of_algebra ℓ E (by simpa using hℓ')

variable (ϖ : PadicAlgCl.integers ℓ E)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **Torsion-free `f_*`-acyclic resolutions for `𝒪_E`-coefficients**: every bounded below
`K ≥ n` in `D(𝒪_{E,X})` is represented by a complex `J ≥ n - 1` of `f_*`-acyclic
`𝒪_{E,X}`-modules on which a uniformizer `ϖ` acts injectively. -/
theorem exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_padicIntegers
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    ∃ (J : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ℤ),
      Nonempty (K ≅ DerivedCategory.Q.obj J) ∧ J.IsStrictlyGE (n - 1) ∧
      (∀ k, Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) (J.X k))) ∧
      ∀ k, ((f)_*⟦_⟧).rightAcyclic (J.X k) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let ιY := Mod.regularToComapRegular (padicIntegersToSubfieldRingObj Y ℓ E)
  have : Mono ιY := Mod.mono_regularToComapRegular _
  let ιX := Functor.LaxMonoidal.ε (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧ ≫
    (f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.map ιY
  have : Mono ιX := mono_comp _ _
  let e := upperStarComapPadicSubfieldIso ℓ E f
  have : Functor.PreservesMonomorphisms (tensorLeft ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj
      ((Mod.comap (padicIntegersToSubfieldRingObj Y ℓ E)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) Y))))) := by
    have := Mod.preservesMonomorphisms_tensorLeft_comap_regular
      (padicIntegersToSubfieldRingObj X ℓ E)
    exact Functor.PreservesMonomorphisms.of_iso ((tensoringLeft _).mapIso e.symm)
  have : Epi (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)
      ((f)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj
        ((Mod.comap (padicIntegersToSubfieldRingObj Y ℓ E)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) Y))))) := by
    have := epi_regularEndSMul_comap_padicSubfield X ℓ E ϖ
      (coe_ne_zero_of_maximalIdeal_eq_span ℓ E hϖ)
    have h := Mod.regularEndSMul_naturality (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) e.hom
    rw [show Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) _ = _ ≫ _ ≫ e.inv from
      (by rw [← reassoc_of% h, e.hom_inv_id, Category.comp_id])]
    infer_instance
  obtain ⟨J, hK, hJ, hr, hG⟩ := exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic _ ιX
    (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) K n
  exact ⟨J, hK, hJ, hr, fun k ↦ hG f ιY (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id]) k⟩

/-- **The derived (Push) comparison for `𝒪_E ⟶ 𝔽_E`**: for every morphism of schemes
`f : X ⟶ Y` and every bounded below `K ∈ D(𝒪_{E,X})`, the comparison
`𝔽_E ⊗ᴸ Rf_* K ⟶ Rf_*(𝔽_E ⊗ᴸ K)` is an isomorphism. -/
theorem isIso_derivedUpperStarExtendScalarsPushHom_residueField_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E) f).app K) := by
  -- Destructuring a local hypothesis avoids abstracting the term in the (large) goal.
  have hϖ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  obtain ⟨ϖ, hϖ⟩ := hϖ
  rw [Ideal.submodule_span_eq] at hϖ
  have hJ := exists_iso_Q_obj_mono_regularEndSMul_rightAcyclic_padicIntegers ℓ E f ϖ hϖ K n
  obtain ⟨J, ⟨e⟩, hJn, hr, hJ⟩ := hJ
  have hmem := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have w := padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ hmem
  have hφ := shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ
  have := mono_padicIntegersRegularEnd_hom X ℓ E ϖ hϖ
  have := mono_padicIntegersRegularEnd_hom Y ℓ E ϖ hϖ
  have hY : ∀ k, Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ)
      ((f)_*⟦_⟧.obj (J.X k))) := fun k ↦ by
    have := hr k
    have h : (f)_*⟦_⟧.map (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) (J.X k)) =
        Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj (J.X k)) :=
      Mod.hom_ext _ _ (lowerStar_map_regularEndSMul ℓ E ϖ f (J.X k))
    rw [← h]
    infer_instance
  -- The conclusion differs from the goal only in proof arguments; at default transparency the
  -- unifier unfolds the morphisms of the derived categories instead (minutes).
  with_reducible
    refine isIso_derivedUpperStarExtendScalarsPushHom_app_of_isStrictlyGE _ f K J e (n - 1) hJ
      (fun k ↦ ?_) (fun k ↦ ?_) ?_ ?_
  · have := hr k
    exact rightAcyclic_lowerStar_of_comap ℓ E f _
      ((Mod.shortExact_regularEndSMul_extendUnit w hφ (J.X k)).rightAcyclic_X₃ (hJ k) (hJ k))
  · have := hr k
    exact isIso_pushHom_residueField_app_of_rightAcyclic ℓ E f ϖ hϖ (J.X k) (hJ k)
  · exact Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul w hφ J hr
  · exact Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul
      (padicIntegersRegularEnd_hom_comp_residueField Y ℓ E ϖ hmem)
      (shortExact_padicIntegersRegularEnd Y ℓ E ϖ hϖ)
      ((((f)_*⟦_⟧).mapHomologicalComplex _).obj J) hY

end CondensedRing

end AlgebraicGeometry.ProEtale
