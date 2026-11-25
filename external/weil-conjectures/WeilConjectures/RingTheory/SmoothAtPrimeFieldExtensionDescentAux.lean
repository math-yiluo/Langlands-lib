/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import WeilConjectures.RingTheory.SingularIdeal

import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Kaehler.TensorProduct

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
private theorem h1_baseChange
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] :
    let := TensorProduct.rightAlgebra (R := k) (A := K) (B := S)
    IsBaseChange (K ⊗[k] S) (H1Cotangent.map k K S (K ⊗[k] S)) := by
  let := TensorProduct.rightAlgebra (R := k) (A := K) (B := S)
  let f := H1Cotangent.map k K S (K ⊗[k] S)
  let e := IsPushout.cancelBaseChange k K S (K ⊗[k] S) (H1Cotangent k S)
  let g := f.liftBaseChange (K ⊗[k] S)
  have he : g.restrictScalars K ∘ₗ e.symm.toLinearMap =
      (tensorH1CotangentOfFlat k S K).toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp_all only [map_add]
    | tmul a x =>
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, g, e, IsPushout.cancelBaseChange_symm_tmul,
        LinearMap.liftBaseChange_tmul, f, tensorH1CotangentOfFlat_tmul]
      exact algebraMap_smul (K ⊗[k] S) a _
  have hg : Function.Bijective g := by
    have hcomp : Function.Bijective (g ∘ e.symm) := by
      change Function.Bijective (g.restrictScalars K ∘ₗ e.symm.toLinearMap)
      rw [he]
      exact (tensorH1CotangentOfFlat k S K).bijective
    exact (Function.Bijective.of_comp_iff g e.symm.bijective).mp hcomp
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective g hg) (by
    intro x
    simp [g, f])


set_option backward.isDefEq.respectTransparency false in
private theorem kaehler_baseChange
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] :
    letI := TensorProduct.rightAlgebra (R := k) (A := K) (B := S)
    IsBaseChange (K ⊗[k] S) (KaehlerDifferential.map k K S (K ⊗[k] S)) := by
  let := TensorProduct.rightAlgebra (R := k) (A := K) (B := S)
  let e := KaehlerDifferential.tensorKaehlerEquiv k K S (K ⊗[k] S)
  have he : e.toLinearMap.restrictScalars S ∘ₗ _root_.TensorProduct.mk S (K ⊗[k] S)
      (KaehlerDifferential k S) 1 = KaehlerDifferential.map k K S (K ⊗[k] S) := by
    ext x
    simp [e, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, KaehlerDifferential.map_D]
  exact IsBaseChange.of_equiv e (fun x ↦ congr($he x))

set_option backward.isDefEq.respectTransparency false in
/-- The localized cotangent conditions descend along the field extension.
The proof is the faithful-flat cotangent descent argument of Stacks, Tag 00TG:
flat base change identifies the localized cotangent homology and differentials, and
faithful-flat descent reflects vanishing and finite projectivity.
(blueprint: lem-weil-pbc-formally-smooth-at-prime-field-extension-descent-cotangent-conditions) -/
theorem fieldExtension_cotangent_conditions
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    Module.Projective (Localization.AtPrime
      (PrimeSpectrum.comap
        (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)
      (KaehlerDifferential k (Localization.AtPrime
        (PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)) ∧
      Subsingleton (H1Cotangent k (Localization.AtPrime
        (PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)) := by
  let B := K ⊗[k] S
  let : Algebra S B := TensorProduct.rightAlgebra
  let q : PrimeSpectrum S := qK.comap (algebraMap S B)
  let A := Localization.AtPrime q.asIdeal
  let L := Localization.AtPrime qK.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver q.asIdeal qK.asIdeal
  have : Module.Flat S B := by
    let e : S ⊗[k] K ≃ₐ[S] B :=
      .ofRingEquiv (f := TensorProduct.comm k S K) (by intro x; rfl)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  have : IsLocalHom (algebraMap A L) := by
    exact Localization.isLocalHom_localRingHom q.asIdeal qK.asIdeal (algebraMap S B) rfl
  have : Module.FaithfullyFlat A L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : FinitePresentation K B := FinitePresentation.of_finiteType.mp inferInstance
  have hlocal : IsSmoothAt K qK.asIdeal := by
    obtain ⟨g, hg, hsm⟩ := hsmooth
    exact (basicOpen_subset_smoothLocus_iff_smooth.mpr hsm) hg
  let f := H1Cotangent.map k k S A
  let h := H1Cotangent.map k K A L
  have hf : IsBaseChange A f :=
    IsLocalizedModule.isBaseChange q.asIdeal.primeCompl A f
  have ht : IsBaseChange L (H1Cotangent.map k K S L) := by
    have hc := (h1_baseChange (k := k) (K := K) (S := S)).comp
      (IsLocalizedModule.isBaseChange qK.asIdeal.primeCompl L (H1Cotangent.map K K B L))
    convert hc using 1
    apply LinearMap.ext
    intro x
    change Extension.H1Cotangent.map _ x =
      Extension.H1Cotangent.map _ (Extension.H1Cotangent.map _ x)
    rw [← Extension.H1Cotangent.map_comp_apply]
    exact congrArg (fun f : H1Cotangent k S →ₗ[S] H1Cotangent K L ↦ f x)
      (Extension.H1Cotangent.map_eq
        ((Generators.self k S).defaultHom (Generators.self K L)).toExtensionHom
        (((Generators.self K B).defaultHom (Generators.self K L)).toExtensionHom.comp
          ((Generators.self k S).defaultHom (Generators.self K B)).toExtensionHom))
  have hh : IsBaseChange L h := by
    apply hf.of_comp
    convert ht using 1
    apply LinearMap.ext
    intro x
    change Extension.H1Cotangent.map _ (Extension.H1Cotangent.map _ x) =
      Extension.H1Cotangent.map _ x
    rw [← Extension.H1Cotangent.map_comp_apply]
    exact congrArg (fun f : H1Cotangent k S →ₗ[S] H1Cotangent K L ↦ f x)
      (Extension.H1Cotangent.map_eq
        (((Generators.self k A).defaultHom (Generators.self K L)).toExtensionHom.comp
          ((Generators.self k S).defaultHom (Generators.self k A)).toExtensionHom)
        ((Generators.self k S).defaultHom (Generators.self K L)).toExtensionHom)
  have : Subsingleton (L ⊗[A] H1Cotangent k A) := hh.equiv.subsingleton
  have hz : Subsingleton (H1Cotangent k A) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality A L (H1Cotangent k A)
  let fΩ := KaehlerDifferential.map k k S A
  let hΩ := KaehlerDifferential.map k K A L
  have hfΩ : IsBaseChange A fΩ :=
    IsLocalizedModule.isBaseChange q.asIdeal.primeCompl A fΩ
  have htΩ : IsBaseChange L (KaehlerDifferential.map k K S L) := by
    have hc := (kaehler_baseChange (k := k) (K := K) (S := S)).comp
      (IsLocalizedModule.isBaseChange qK.asIdeal.primeCompl L
        (KaehlerDifferential.map K K B L))
    convert hc using 1
    ext x
    simp [B, KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply S B L]
  have hhΩ : IsBaseChange L hΩ := by
    apply hfΩ.of_comp
    convert htΩ using 1
    ext x
    simp [hΩ, fΩ, KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply S A L]
  have : Module.Flat L (L ⊗[A] KaehlerDifferential k A) :=
    Module.Flat.of_linearEquiv hhΩ.equiv
  have : Module.Flat A (KaehlerDifferential k A) :=
    Module.Flat.of_flat_tensorProduct A (KaehlerDifferential k A) L
  have : EssFiniteType S A := .of_isLocalization A q.asIdeal.primeCompl
  have : EssFiniteType k A := .comp k S A
  have hp : Module.Projective A (KaehlerDifferential k A) := by
    have : Module.Free A (KaehlerDifferential k A) := Module.free_of_flat_of_isLocalRing
    infer_instance
  exact ⟨hp, hz⟩

/-- (blueprint: lem-weil-pbc-formally-smooth-at-prime-field-extension-descent)
Formal smoothness at the contracted local ring descends from a smooth tensor-product
localization.  This is the local cotangent descent step in the proof of field-extension
descent; it packages faithful-flat descent of the localized cotangent homology and
finite projectivity of differentials.  The proof uses finite presentation over the field,
faithful flatness after tensoring and localizing, flat base change for cotangent homology
and Kähler differentials, faithful-flat descent of vanishing and finite projectivity, and
the naive cotangent criterion for formal smoothness. -/
theorem formallySmoothAtPrime_of_fieldExtension
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    Algebra.IsSmoothAt k
      (PrimeSpectrum.comap
        (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal := by
  obtain ⟨hp, h₁⟩ := fieldExtension_cotangent_conditions qK hsmooth
  exact ⟨hp, h₁⟩

end Algebra
