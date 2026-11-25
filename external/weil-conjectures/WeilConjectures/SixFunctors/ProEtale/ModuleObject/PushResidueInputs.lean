/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueShortExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralRegularEnd

/-!
# The uniformizer as an endomorphism of the regular `𝒪_{E,X}`-module

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
residue field `𝔽_E`, and `ϖ ∈ 𝒪_E`. The constant global section `ϖ` of `𝒪_{E,X}`
(`AlgebraicGeometry.ProEtale.padicIntegersConstSection`) defines an endomorphism
`AlgebraicGeometry.ProEtale.padicIntegersRegularEndOfAlgebra` of the regular `𝒪_{E,X}`-module, whose
underlying map is the multiplication `padicIntegersMulLeft X ℓ E ϖ`
(`AlgebraicGeometry.ProEtale.padicIntegersRegularEnd_hom`). Hence, for a uniformizer `ϖ`, the
reduction lemmas of `PushResidueIsoReduction` apply to the residue map `𝒪_{E,X} ⟶ 𝔽_{E,X}`
(`AlgebraicGeometry.ProEtale.shortExact_padicIntegersRegularEnd`). The action of `ϖ` commutes
with pushforward (`AlgebraicGeometry.ProEtale.CondensedRing.lowerStar_map_regularEndSMul`).

As an application, the underived (Push) comparison `𝔽_{E,Y} ⊗ f_* M ⟶ f_*(𝔽_{E,X} ⊗ M)` is an
isomorphism at every `𝒪_{E,X}`-module `M` on which `ϖ` acts injectively and whose underlying
abelian sheaf is `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_pushHom_residueField_app_of_mono`): both units
`f_* M ⟶ 𝔽_{E,Y} ⊗ f_* M` and `f_* M ⟶ f_*(𝔽_{E,X} ⊗ M)` are cokernels of the action of `ϖ`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- The action of an endomorphism `r` of the regular module on the regular module is `r`. -/
lemma regularEndSMul_unit (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) :
    regularEndSMul r (𝟙_ (Mod C R)) = r := by
  rw [regularEndSMul, unitors_equal, rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (ϖ : PadicAlgCl.integers ℓ E)

/-- The constant global section `ϖ` of `𝒪_{E,X}`: the image under `p_X^*` of the constant global
section `ϖ` of `𝒪̲_E`. -/
noncomputable def padicIntegersConstSection :
    𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map
    (Profinite.continuousMapConstRingHom.{u} (PadicAlgCl.integers ℓ E) ϖ).hom

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The action of `padicIntegersRegularEndOfAlgebra X ℓ E ϖ` on an `𝒪_{E,X}`-module is the action
of the constant global section `ϖ`. -/
lemma regularEndSMul_padicIntegersRegularEnd_hom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :
    (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M).hom =
      Mod.globalSmul (padicIntegersConstSection X ℓ E ϖ) M :=
  Mod.regularEndSMul_regularLift_hom _ M

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **The underlying map of `padicIntegersRegularEndOfAlgebra X ℓ E ϖ` is the multiplication by
`ϖ`.** -/
lemma padicIntegersRegularEnd_hom :
    (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom = padicIntegersMulLeft X ℓ E ϖ := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [← Mod.regularEndSMul_unit (padicIntegersRegularEndOfAlgebra X ℓ E ϖ)]
  refine (regularEndSMul_padicIntegersRegularEnd_hom X ℓ E ϖ _).trans ?_
  rw [padicIntegersConstSection]
  erw [Mod.globalSmul_regular_obj (upperStarFromPoint X)]
  rw [Profinite.globalSmul_continuousMapConstRingHom]
  rfl

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- An element `ϖ ∈ 𝔪_E` vanishes in `𝔽_{E,X}`. -/
lemma padicIntegersRegularEnd_hom_comp_residueField
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E)) :
    (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom ≫ padicIntegersToResidueField X ℓ E = 0 := by
  rw [padicIntegersRegularEnd_hom]
  exact padicIntegersMulLeft_comp_residueField X ℓ E ϖ hϖ

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact**, for a generator `ϖ` of the
maximal ideal, with `ϖ` seen as an endomorphism of the regular `𝒪_{E,X}`-module: this is the
hypothesis of the reduction lemmas `CategoryTheory.Mod.shortExact_regularEndSMul_extendUnit` and
`CategoryTheory.Mod.isIso_leftDerivedFunctorCounit_app_of_mono_regularEndSMul`. -/
lemma shortExact_padicIntegersRegularEnd
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ShortComplex.mk _ _ (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk _ _ (padicIntegersMulLeft_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [padicIntegersRegularEnd_hom]) (by simp))
    (shortExact_padicIntegersMulLeft_residueField X ℓ E ϖ hϖ)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- For a generator `ϖ` of the maximal ideal, the multiplication by `ϖ` on `𝒪_{E,X}` is a
monomorphism. -/
lemma mono_padicIntegersRegularEnd_hom
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    Mono (padicIntegersRegularEndOfAlgebra X ℓ E ϖ).hom :=
  (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ).mono_f

namespace CondensedRing

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **The action of `ϖ` commutes with pushforward**: the pushforward of the action of `ϖ` on an
`𝒪_{E,X}`-module `M` is the action of `ϖ` on `f_* M`. -/
lemma lowerStar_map_regularEndSMul
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :
    (f)_*[Ab.{u + 1}].map (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M).hom =
      (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj M)).hom := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [regularEndSMul_padicIntegersRegularEnd_hom, regularEndSMul_padicIntegersRegularEnd_hom,
    padicIntegersConstSection, padicIntegersConstSection]
  exact (globalSmul_lowerStar_obj f (PadicAlgCl.integers ℓ E) ϖ M).symm

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The underived (Push) comparison for `𝒪_E ⟶ 𝔽_E`** is an isomorphism at an
`𝒪_{E,X}`-module `M` on which a uniformizer `ϖ` acts injectively and whose underlying abelian
sheaf is `f_*`-acyclic: both units `f_* M ⟶ 𝔽_{E,Y} ⊗ f_* M` and `f_* M ⟶ f_*(𝔽_{E,X} ⊗ M)` are
cokernels of the action of `ϖ` on `f_* M`, the second one since `R¹f_* M = 0`. -/
theorem isIso_pushHom_residueField_app_of_mono
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    [Mono (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)]
    (hM : ((f)_*[Ab.{u + 1}]).rightAcyclic M.X) :
    IsIso ((pushHom (Profinite.padicIntegersRingObjToResidueField ℓ E) f).app M) := by
  have hmem := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have hX := Mod.shortExact_regularEndSMul_extendUnit
    (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ hmem)
    (shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ) M
  have := hX.mono_f
  have := hX.epi_g
  have : Mono ((Mod.forget _).map
      (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E ϖ) M)) :=
    (Mod.forget _).map_mono _
  have : Epi ((Mod.forget _).map (Mod.extendUnit (padicIntegersToResidueField X ℓ E) M)) :=
    (Mod.forget _).map_epi _
  have hX' := (hX.map (Mod.forget _)).map_of_rightAcyclic (F := (f)_*[Ab.{u + 1}]) hM
  obtain ⟨hY, _⟩ := Mod.exact_regularEndSMul_extendUnit
    (padicIntegersRegularEnd_hom_comp_residueField Y ℓ E ϖ hmem)
    (shortExact_padicIntegersRegularEnd Y ℓ E ϖ hϖ) ((f)_*⟦_⟧.obj M)
  have hY' := hY.map (Mod.forget _)
  have : Epi ((ShortComplex.mk _ _ (Mod.regularEndSMul_comp_extendUnit
      (padicIntegersRegularEnd_hom_comp_residueField Y ℓ E ϖ hmem)
      ((f)_*⟦_⟧.obj M))).map (Mod.forget _)).g :=
    (Mod.forget _).map_epi _
  have e := lowerStar_map_regularEndSMul ℓ E ϖ f M
  have w₂ : (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra Y ℓ E ϖ) ((f)_*⟦_⟧.obj M)).hom ≫
      (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom
        (coefficientMap (Profinite.padicIntegersRingObjToResidueField ℓ E) X) M) = 0 := by
    rw [← e, ← Functor.map_comp, ← Mod.extendUnit_hom, ← Mod.comp_hom',
      Mod.regularEndSMul_comp_extendUnit
        (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ hmem), Mod.zero_hom,
      Functor.map_zero]
  have hX'' : (ShortComplex.mk _ _ w₂).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk
      (S₁ := ((ShortComplex.mk _ _ (Mod.regularEndSMul_comp_extendUnit
        (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ hmem) M)).map (Mod.forget _)).map
          (f)_*[Ab.{u + 1}]) (S₂ := ShortComplex.mk _ _ w₂) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simpa using e.symm) (by simp)) hX'.exact
  have : Epi (ShortComplex.mk _ _ w₂).g := hX'.epi_g
  exact isIso_pushHom_app_of_isColimit _ f M _ _ w₂ hY'.gIsCokernel hX''.gIsCokernel

end CondensedRing

end AlgebraicGeometry.ProEtale
