/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection

/-!
# The first derived reduction preserves bounded constructible complexes

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` and `X` a noetherian scheme. This file proves
that the first derived reduction `K ↦ K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` sends bounded constructible
`𝒪_{E,X}`-complexes to bounded constructible complexes:

* `ProEtale.boundedConstructible_derivedExtendScalars_residueField`: in the condensed model,
  `K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` is a bounded constructible complex of `𝔽_{E,X}`-modules. The proof
  uses the reduction triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` for a uniformizer `ϖ` of `𝒪_E`
  (`CategoryTheory.Mod.exists_distinguished_regularEndSMul_derivedExtendScalars`) and the descent
  of constructibility along `𝒪_{E,X} ⟶ 𝔽_{E,X}`
  (`ProEtale.IsConstructibleModuleObject.of_comap_of_regularLift`).
* `ProEtale.boundedConstructible_derivedReduction_obj`: the first derived reduction
  `ProEtale.derivedReduction` lies in the étale-origin `Dᵇc(X, 𝔽_E)`. Indeed
  `ProEtale.residueFieldModuleSheaf` is the equivalence `finiteCoefficientModEquivalence`, which
  sends constructible module objects to constructible sheaves
  (`ProEtale.isConstructible_finiteCoefficientModEquivalence_functor_obj`), and for finite
  coefficients the intrinsic and étale-origin readings of `Dᵇc` agree
  (`ProEtale.DerivedCategory.boundedConstructibleIntrinsic_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  [IsNoetherian X]

/-- **Reduction modulo a uniformizer preserves bounded constructible complexes**: on a noetherian
scheme `X`, if `K ∈ D(Mod_{𝒪_{E,X}})` is bounded constructible, so is
`K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X} ∈ D(Mod_{𝔽_{E,X}})`. By the reduction triangle modulo a uniformizer `ϖ`,
its restriction of scalars is a bounded constructible `𝒪_{E,X}`-complex, and constructibility
descends along `𝒪_{E,X} ⟶ 𝔽_{E,X}`. -/
theorem boundedConstructible_derivedExtendScalars_residueField
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) K) :
    boundedConstructible (residueFieldRingObj X ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  have hS := shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ
  have hT := Mod.exists_distinguished_regularEndSMul_derivedExtendScalars _ hS K
  have h₃ : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _
      hT.choose_spec.choose_spec.choose_spec hK hK
  have hiso (i : ℤ) :=
    ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategoryHomologyFunctorIso
    i).app ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)
  rw [mem_boundedConstructible_iff] at h₃ ⊢
  obtain ⟨⟨a, b, hab⟩, hc⟩ := h₃
  exact ⟨⟨a, b, fun i hi ↦ Mod.isZero_of_isZero_comap _ ((hab i hi).of_iso (hiso i))⟩,
    fun i ↦ IsConstructibleModuleObject.of_comap_of_regularLift _ hS
      ((hc i).of_iso (hiso i).symm)⟩

/-- Blueprint `proposition-integral-constructibility-criterion` (section `chap-The-pro-etale-site`),
implication (1) ⇒ (2), its second half: on a noetherian scheme `X`, the first derived reduction
`K₁ = K ⊗ᴸ_{𝒪_{E,X}} 𝔽_{E,X}` of a bounded constructible `𝒪_E`-complex `K` lies in
`Dᵇc(X, 𝔽_E)`, read as the complexes of étale origin
(`ProEtale.DerivedCategory.boundedConstructible`). -/
theorem boundedConstructible_derivedReduction_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) K) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj K) := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E)))
  have hL := boundedConstructible_derivedExtendScalars_residueField X ℓ E K hK
  rw [← DerivedCategory.boundedConstructibleIntrinsic_eq]
  refine ⟨(residueFieldModuleSheaf X ℓ E).bounded_mapDerivedCategory_obj hL.1, fun n ↦ ?_⟩
  refine isConstructible_of_iso
    (((residueFieldModuleSheaf X ℓ E).mapDerivedCategoryHomologyFunctorIso n).app _) ?_
  exact isConstructible_of_iso
    (((residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E)).app _).symm)
    (isConstructible_finiteCoefficientModEquivalence_functor_obj (integersResidueField ℓ E)
      (hL.2 n))

end AlgebraicGeometry.ProEtale
