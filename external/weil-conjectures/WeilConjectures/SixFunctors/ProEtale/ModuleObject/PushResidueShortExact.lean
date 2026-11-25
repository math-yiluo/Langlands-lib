/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction

/-!
# The residue field `𝔽_E` as the cokernel of a uniformizer

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
residue field `𝔽_E`, and `ϖ` a uniformizer of `𝒪_E`. The sequence
```
0 ⟶ 𝒪̲_E --ϖ--> 𝒪̲_E ⟶ 𝔽̲_E ⟶ 0
```
of condensed abelian groups is short exact
(`Profinite.shortExact_padicIntegersRingObjMulLeft_residueField`), and so is its pullback
```
0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0
```
to the pro-étale site of a scheme `X` (`ProEtale.shortExact_padicIntegersMulLeft_residueField`).
Thus `𝔽_E` has the free resolution `𝒪_E --ϖ--> 𝒪_E` also on `X_proét`; this is the input
computing the derived reduction `𝔽_{E,X} ⊗ᴸ_{𝒪_{E,X}} -` as the cone of `ϖ`.

The condensed statement is checked on sections over a profinite set `S`: multiplication by
`ϖ ≠ 0` is injective on `C(S, 𝒪_E)`, a continuous map `S → 𝒪_E` with values in `𝔪_E = ϖ 𝒪_E`
is `ϖ` times the continuous map `ϖ⁻¹ a`, and a continuous map `S → 𝔽_E` lifts along any section
of the residue map, `𝔽_E` being discrete.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The multiplication `𝒪̲_E ⟶ 𝒪̲_E` by a constant `ϖ ∈ 𝒪_E`, as a morphism of condensed abelian
groups. -/
noncomputable def padicIntegersRingObjMulLeft (ϖ : PadicAlgCl.integers ℓ E) :
    padicIntegersRingObj.{u} ℓ E ⟶ padicIntegersRingObj ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingObjMulLeft (PadicAlgCl.integers ℓ E) ϖ

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
lemma padicIntegersRingObjMulLeft_hom_app_apply (ϖ : PadicAlgCl.integers ℓ E)
    (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (padicIntegersRingObjMulLeft ℓ E ϖ).hom.app S a =
        ULift.up (ContinuousMap.const _ ϖ * a.down) :=
  fun _ ↦ rfl

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
lemma padicIntegersRingObjToResidueField_hom_app_apply (S : Profinite.{u}ᵒᵖ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    ∀ a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E),
      (padicIntegersRingObjToResidueField ℓ E).hom.app S a =
        ULift.up ((⟨PadicAlgCl.integersResidue ℓ E, PadicAlgCl.continuous_integersResidue ℓ E⟩ :
          C(PadicAlgCl.integers ℓ E, PadicAlgCl.integersResidueField ℓ E)).comp a.down) :=
  fun _ ↦ rfl

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- An element of the maximal ideal vanishes in `𝔽_E`: the multiplication by `ϖ ∈ 𝔪_E` on `𝒪̲_E`
followed by the residue map is zero. -/
lemma padicIntegersRingObjMulLeft_comp_residueField (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E)) :
    padicIntegersRingObjMulLeft.{u} ℓ E ϖ ≫ padicIntegersRingObjToResidueField ℓ E = 0 := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ext S a
  refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
  change PadicAlgCl.integersResidue ℓ E (ϖ * a.down s) = 0
  rw [map_mul, show PadicAlgCl.integersResidue ℓ E ϖ = 0 from
    (IsLocalRing.residue_eq_zero_iff _).2 hϖ, zero_mul]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`0 ⟶ 𝒪̲_E --ϖ--> 𝒪̲_E ⟶ 𝔽̲_E ⟶ 0` is short exact** for a generator `ϖ` of the maximal ideal of
`𝒪_E`, checked on sections over each profinite set `S`. -/
lemma shortExact_padicIntegersRingObjMulLeft_residueField (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ShortComplex.mk _ _ (padicIntegersRingObjMulLeft_comp_residueField.{u} ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))).ShortExact := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let T := ShortComplex.mk _ _ (padicIntegersRingObjMulLeft_comp_residueField.{u} ℓ E ϖ
    (hϖ ▸ Ideal.mem_span_singleton_self ϖ))
  have hne : ϖ ≠ 0 := fun h ↦ PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E (by
    rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hne' : (ϖ : E) ≠ 0 := fun h ↦ hne (Subtype.ext h)
  have hf (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) (s) :
      (T.f.hom.app S a).down s = ϖ * a.down s := rfl
  have hg (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E)) (s) :
      (T.g.hom.app S a).down s = PadicAlgCl.integersResidue ℓ E (a.down s) := rfl
  have hpre : (T.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun S ↦ ?_
    have h : ((T.map (sheafToPresheaf _ _)).map ((evaluation _ _).obj S)).Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro a ha
      have hz (s : S.unop) : a.down s ∈ Ideal.span {ϖ} := by
        rw [← hϖ, ← IsLocalRing.residue_eq_zero_iff]
        exact (hg S a s).symm.trans (congrArg (fun z : ULift.{u + 1} C(S.unop,
          PadicAlgCl.integersResidueField ℓ E) ↦ z.down s) ha)
      choose b hb using fun s ↦ Ideal.mem_span_singleton'.1 (hz s)
      have hbv (s : S.unop) : (b s : E) = (ϖ : E)⁻¹ * (a.down s : E) := by
        rw [← hb s, Subring.coe_mul, mul_comm (b s : E)]
        exact (inv_mul_cancel_left₀ hne' _).symm
      have hbc : Continuous b := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        simp only [Function.comp_def, hbv]
        exact continuous_const.mul (continuous_subtype_val.comp a.down.continuous)
      exact ⟨ULift.up ⟨b, hbc⟩, ULift.ext (ContinuousMap.ext fun s ↦
        (hf S _ s).trans ((mul_comm _ _).trans (hb s)))⟩
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((T.map (sheafToPresheaf _ _)).mapHomologyIso ((evaluation _ _).obj S)).symm
  have hmono (S : Profinite.{u}ᵒᵖ) : Mono (((sheafToPresheaf _ _).map T.f).app S) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have h := congrArg ULift.down hab
    exact ULift.ext (ContinuousMap.ext fun s ↦ mul_left_cancel₀ hne
      (((hf S a s).symm.trans (congrArg (fun z : C(S.unop, PadicAlgCl.integers ℓ E) ↦ z s)
        h)).trans (hf S b s)))
  have hepi (S : Profinite.{u}ᵒᵖ) : Epi (((sheafToPresheaf _ _).map T.g).app S) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro c
    refine ⟨ULift.up ⟨Function.surjInv (PadicAlgCl.integersResidue_surjective ℓ E) ∘ c.down,
      continuous_of_discreteTopology.comp c.down.continuous⟩,
      ULift.ext (ContinuousMap.ext fun s ↦ ?_)⟩
    exact (hg S _ s).trans (Function.surjInv_eq _ _)
  have : Mono T.f := (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have : Epi T.g := (sheafToPresheaf _ _).epi_of_epi_map (NatTrans.epi_of_epi_app _)
  refine ⟨?_⟩
  exact (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (asIso (sheafificationAdjunction _ _).counit))).1
    (hpre.map (presheafToSheaf _ _))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The multiplication `𝒪_{E,X} ⟶ 𝒪_{E,X}` by a constant `ϖ ∈ 𝒪_E`: the pullback along `p_X` of
the multiplication by `ϖ` on `𝒪̲_E`. -/
noncomputable abbrev padicIntegersMulLeft (ϖ : PadicAlgCl.integers ℓ E) :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X ⟶
      condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X :=
  (upperStarFromPoint X).map (Profinite.padicIntegersRingObjMulLeft ℓ E ϖ)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- An element `ϖ ∈ 𝔪_E` vanishes in `𝔽_{E,X}`. -/
lemma padicIntegersMulLeft_comp_residueField (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E)) :
    padicIntegersMulLeft X ℓ E ϖ ≫ padicIntegersToResidueField X ℓ E = 0 := by
  rw [← Functor.map_comp, Profinite.padicIntegersRingObjMulLeft_comp_residueField ℓ E ϖ hϖ,
    Functor.map_zero]

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact** for a generator `ϖ` of the
maximal ideal of `𝒪_E`: it is the inverse image along the exact functor `p_X^*` of the short
exact sequence `0 ⟶ 𝒪̲_E --ϖ--> 𝒪̲_E ⟶ 𝔽̲_E ⟶ 0` of condensed abelian groups. -/
lemma shortExact_padicIntegersMulLeft_residueField (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    (ShortComplex.mk _ _ (padicIntegersMulLeft_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ))).ShortExact := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    ((Profinite.shortExact_padicIntegersRingObjMulLeft_residueField.{u} ℓ E ϖ hϖ).map_of_exact
      (upperStarFromPoint X))

/-- `𝔽_{E,X}` is the cokernel of a uniformizer: there is `ϖ ∈ 𝒪_E` generating the maximal ideal
such that `0 ⟶ 𝒪_{E,X} --ϖ--> 𝒪_{E,X} ⟶ 𝔽_{E,X} ⟶ 0` is short exact. -/
lemma exists_shortExact_padicIntegersMulLeft_residueField :
    ∃ (ϖ : PadicAlgCl.integers ℓ E)
      (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}),
      (ShortComplex.mk _ _ (padicIntegersMulLeft_comp_residueField X ℓ E ϖ
        (hϖ ▸ Ideal.mem_span_singleton_self ϖ))).ShortExact := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  exact ⟨ϖ, hϖ, shortExact_padicIntegersMulLeft_residueField X ℓ E ϖ hϖ⟩

end AlgebraicGeometry.ProEtale
