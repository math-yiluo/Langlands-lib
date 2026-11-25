/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Base change of the first homology of the naive cotangent complex

Let `P` be an extension of the `R`-algebra `S` whose cotangent space `S ⊗[P] Ω[P⁄R]` is flat
(e.g. a polynomial presentation), and assume that `Ω[S⁄R]` is a projective `S`-module. Then
for every `S`-module `C`, tensoring the naive cotangent complex `I/I² → S ⊗[P] Ω[P⁄R]`
with `C` commutes with taking first homology: the map `H₁ ⊗ C → I/I² ⊗ C` is injective with
image the kernel of the tensored differential (Stacks, Tag 00S2).

## Main results

* `Algebra.Extension.rTensor_h1Cotangentι_injective` and
  `Algebra.Extension.range_rTensor_h1Cotangentι`: the general statement.
* `Algebra.H1Cotangent.rTensor_quotient`: the case of the canonical presentation and of
  `C = S ⧸ 𝔞`, when moreover `H₁(L_{S/R}) = 0`.
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable (P : Extension R S)

/-- If `Ω[S⁄R]` is projective and `P.CotangentSpace` is flat, then the image of the
cotangent complex `I/I² → S ⊗[P] Ω[P⁄R]` is a flat `S`-module. -/
lemma flat_range_cotangentComplex [Module.Flat S P.CotangentSpace]
    [Module.Projective S Ω[S⁄R]] : Module.Flat S (LinearMap.range P.cotangentComplex) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property P.toKaehler LinearMap.id
    P.toKaehler_surjective
  have hex := P.exact_cotangentComplex_toKaehler
  let r : P.CotangentSpace →ₗ[S] LinearMap.range P.cotangentComplex :=
    (LinearMap.id - σ ∘ₗ P.toKaehler).codRestrict _ fun x ↦ by
      rw [← hex.linearMap_ker_eq, LinearMap.mem_ker]
      have := congr($hσ (P.toKaehler x))
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      simp [this]
  refine Module.Flat.of_retract (LinearMap.range P.cotangentComplex).subtype r ?_
  ext ⟨x, hx⟩
  have : P.toKaehler x = 0 := by rwa [← LinearMap.mem_ker, hex.linearMap_ker_eq]
  simp [r, this]

variable {P}

variable (C : Type*) [AddCommGroup C] [Module S C]

/-- If `Ω[S⁄R]` is projective and `P.CotangentSpace` is flat, then
`H₁ ⊗ C → I/I² ⊗ C` is injective. -/
theorem rTensor_h1Cotangentι_injective [Module.Flat S P.CotangentSpace]
    [Module.Projective S Ω[S⁄R]] : Function.Injective (P.h1Cotangentι.rTensor C) := by
  have := P.flat_range_cotangentComplex
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  refine LinearMap.lTensor_injective_of_exact_of_flat (f := P.cotangentComplex.rangeRestrict)
    (P := LinearMap.range P.cotangentComplex)
    (hf := P.cotangentComplex.surjective_rangeRestrict) (g := P.h1Cotangentι)
    (hg := Subtype.val_injective) (A := C) ?_
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
    ← LinearMap.exact_iff.mp P.exact_hCotangentι_cotangentComplex]

/-- If `Ω[S⁄R]` is projective, then `(image of δ) ⊗ C → (S ⊗[P] Ω[P⁄R]) ⊗ C` is
injective. -/
lemma rTensor_range_cotangentComplex_subtype_injective [Module.Projective S Ω[S⁄R]] :
    Function.Injective ((LinearMap.range P.cotangentComplex).subtype.rTensor C) := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  refine LinearMap.lTensor_injective_of_exact_of_flat P.toKaehler P.toKaehler_surjective _
    (Submodule.injective_subtype _) ?_ C
  rw [LinearMap.exact_iff, Submodule.range_subtype,
    P.exact_cotangentComplex_toKaehler.linearMap_ker_eq]

/-- If `Ω[S⁄R]` is projective, then the image of
`H₁ ⊗ C → I/I² ⊗ C` is the kernel of `δ ⊗ id_C`. -/
theorem range_rTensor_h1Cotangentι [Module.Projective S Ω[S⁄R]] :
    LinearMap.range (P.h1Cotangentι.rTensor C) =
      LinearMap.ker (P.cotangentComplex.rTensor C) := by
  have hδ : P.cotangentComplex.rTensor C = (LinearMap.range P.cotangentComplex).subtype.rTensor C
      ∘ₗ P.cotangentComplex.rangeRestrict.rTensor C := by
    rw [← LinearMap.rTensor_comp]; rfl
  have hex : Function.Exact P.h1Cotangentι P.cotangentComplex.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      ← LinearMap.exact_iff.mp P.exact_hCotangentι_cotangentComplex]
  have hinj := rTensor_range_cotangentComplex_subtype_injective (P := P) C
  rw [← (rTensor_exact (P := LinearMap.range P.cotangentComplex) C hex
    P.cotangentComplex.surjective_rangeRestrict).linearMap_ker_eq, hδ]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
  exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦ hinj (by rw [h, map_zero])⟩

end Extension

/-- (blueprint: `theorem-finite-etale-covers-proper-henselian--2`)
Let `R → S` be a ring map with `H₁(L_{S/R}) = 0` and `Ω[S⁄R]` projective, let `𝔞` be an
ideal of `S` and `C = S ⧸ 𝔞`. For the naive cotangent complex
`δ : I/I² → S ⊗[P] Ω[P⁄R]`
of the canonical presentation `P = R[S] → S`, the map `H₁(L_{S/R}) ⊗ C → I/I² ⊗ C`
is injective with image `ker (δ ⊗ id_C)`, and `ker (δ ⊗ id_C) ≅ H₁(L_{S/R}) ⊗ C = 0`. -/
theorem H1Cotangent.rTensor_quotient [Subsingleton (H1Cotangent R S)]
    [Module.Projective S Ω[S⁄R]] (𝔞 : Ideal S) :
    Function.Injective ((Generators.self R S).toExtension.h1Cotangentι.rTensor (S ⧸ 𝔞)) ∧
    LinearMap.range ((Generators.self R S).toExtension.h1Cotangentι.rTensor (S ⧸ 𝔞)) =
      LinearMap.ker ((Generators.self R S).toExtension.cotangentComplex.rTensor (S ⧸ 𝔞)) ∧
    Nonempty (LinearMap.ker
      ((Generators.self R S).toExtension.cotangentComplex.rTensor (S ⧸ 𝔞))
      ≃ₗ[S] H1Cotangent R S ⊗[S] (S ⧸ 𝔞)) ∧
    Subsingleton (H1Cotangent R S ⊗[S] (S ⧸ 𝔞)) := by
  have hinj := Extension.rTensor_h1Cotangentι_injective
    (P := (Generators.self R S).toExtension) (S ⧸ 𝔞)
  have hrange := Extension.range_rTensor_h1Cotangentι
    (P := (Generators.self R S).toExtension) (S ⧸ 𝔞)
  refine ⟨hinj, hrange, ⟨(LinearEquiv.ofInjective _ hinj).trans
    (LinearEquiv.ofEq _ _ hrange)|>.symm⟩, inferInstance⟩

end Algebra
