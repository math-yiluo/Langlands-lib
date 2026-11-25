/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Homotopy equivalence of naive cotangent complexes

Let `S` be an `R`-algebra. For an extension `P` of `S` (a surjection `P.Ring → S` with kernel
`I`), the naive cotangent complex is `P.cotangentComplex : I/I² → S ⊗[P] Ω[P⁄R]`. We show
that for two presentations `P`, `P'` of `S` by polynomial rings, the naive cotangent complexes are
homotopy equivalent, the homotopy equivalence being induced by any pair of maps of
presentations (Stacks, Tag 00S1).

## Main results

* `Algebra.Extension.Hom.exists_homotopy`: for any maps `φ : P → P'`, `ψ : P' → P` of
  extensions of `S`, the induced maps of naive cotangent complexes are mutually inverse
  chain homotopy equivalences.
* `Algebra.Generators.exists_homotopyEquiv_cotangentComplex`: for two polynomial presentations
  maps between them exist, and any such maps induce a homotopy equivalence.
-/

@[expose] public section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

/-- Two maps of extensions `φ : P → P'` and `ψ : P' → P` of the same `R`-algebra `S` induce
mutually inverse homotopy equivalences between the naive cotangent complexes. -/
theorem Hom.exists_homotopy (P P' : Extension R S) (φ : P.Hom P') (ψ : P'.Hom P) :
    ∃ (h : P.CotangentSpace →ₗ[S] P.Cotangent)
      (h' : P'.CotangentSpace →ₗ[S] P'.Cotangent),
      P'.cotangentComplex ∘ₗ Cotangent.map φ =
        CotangentSpace.map φ ∘ₗ P.cotangentComplex ∧
      P.cotangentComplex ∘ₗ Cotangent.map ψ =
        CotangentSpace.map ψ ∘ₗ P'.cotangentComplex ∧
      LinearMap.id - Cotangent.map ψ ∘ₗ Cotangent.map φ = h ∘ₗ P.cotangentComplex ∧
      LinearMap.id - CotangentSpace.map ψ ∘ₗ CotangentSpace.map φ =
        P.cotangentComplex ∘ₗ h ∧
      LinearMap.id - Cotangent.map φ ∘ₗ Cotangent.map ψ = h' ∘ₗ P'.cotangentComplex ∧
      LinearMap.id - CotangentSpace.map φ ∘ₗ CotangentSpace.map ψ =
        P'.cotangentComplex ∘ₗ h' := by
  refine ⟨(Hom.id P).sub (ψ.comp φ), (Hom.id P').sub (φ.comp ψ),
    (CotangentSpace.map_comp_cotangentComplex φ).symm,
    (CotangentSpace.map_comp_cotangentComplex ψ).symm, ?_, ?_, ?_, ?_⟩
  · rw [← Cotangent.map_sub_map, Cotangent.map_id, Cotangent.map_comp]; rfl
  · have := CotangentSpace.map_sub_map (Hom.id P) (ψ.comp φ)
    rw [CotangentSpace.map_id, CotangentSpace.map_comp] at this
    exact this
  · rw [← Cotangent.map_sub_map, Cotangent.map_id, Cotangent.map_comp]; rfl
  · have := CotangentSpace.map_sub_map (Hom.id P') (φ.comp ψ)
    rw [CotangentSpace.map_id, CotangentSpace.map_comp] at this
    exact this

end Extension

namespace Generators

/-- (blueprint: `lem-weil-pbc-nl-presentations-homotopy-equivalent`)
Let `P = R[x_t, t ∈ ι]` and `P' = R[x'_u, u ∈ ι']` be two polynomial presentations of the
`R`-algebra `S`. Then there is a map of presentations `P → P'` (an `R`-algebra map compatible
with the projections to `S`), and for any maps of presentations `φ : P → P'` and
`ψ : P' → P`, the induced maps `φ₁ = Cotangent.map φ`, `φ₀ = CotangentSpace.map φ`,
`ψ₁ = Cotangent.map ψ`, `ψ₀ = CotangentSpace.map ψ` between the naive cotangent complexes
`I/I² → S ⊗[P] Ω[P⁄R]` and `I'/I'² → S ⊗[P'] Ω[P'⁄R]` are chain maps which are
mutually inverse homotopy equivalences, with homotopies `h`, `h'`. -/
theorem exists_homotopyEquiv_cotangentComplex {ι ι' : Type*} (P : Generators R S ι)
    (P' : Generators R S ι') :
    Nonempty (P.toExtension.Hom P'.toExtension) ∧
    Nonempty (P'.toExtension.Hom P.toExtension) ∧
    ∀ (φ : P.toExtension.Hom P'.toExtension) (ψ : P'.toExtension.Hom P.toExtension),
    ∃ (h : P.toExtension.CotangentSpace →ₗ[S] P.toExtension.Cotangent)
      (h' : P'.toExtension.CotangentSpace →ₗ[S] P'.toExtension.Cotangent),
      P'.toExtension.cotangentComplex ∘ₗ Extension.Cotangent.map φ =
        Extension.CotangentSpace.map φ ∘ₗ P.toExtension.cotangentComplex ∧
      P.toExtension.cotangentComplex ∘ₗ Extension.Cotangent.map ψ =
        Extension.CotangentSpace.map ψ ∘ₗ P'.toExtension.cotangentComplex ∧
      LinearMap.id - Extension.Cotangent.map ψ ∘ₗ Extension.Cotangent.map φ =
        h ∘ₗ P.toExtension.cotangentComplex ∧
      LinearMap.id - Extension.CotangentSpace.map ψ ∘ₗ Extension.CotangentSpace.map φ =
        P.toExtension.cotangentComplex ∘ₗ h ∧
      LinearMap.id - Extension.Cotangent.map φ ∘ₗ Extension.Cotangent.map ψ =
        h' ∘ₗ P'.toExtension.cotangentComplex ∧
      LinearMap.id - Extension.CotangentSpace.map φ ∘ₗ Extension.CotangentSpace.map ψ =
        P'.toExtension.cotangentComplex ∘ₗ h' :=
  ⟨⟨(defaultHom P P').toExtensionHom⟩, ⟨(defaultHom P' P).toExtensionHom⟩,
    fun φ ψ ↦ Extension.Hom.exists_homotopy _ _ φ ψ⟩

end Generators

end Algebra
