/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafColimit

/-!
# Cohomology of `E_X` and `ℚ̄_ℓ,X` on a qcqs scheme as colimits

Let `X` be a quasi-compact quasi-separated scheme. Pro-étale cohomology of `X` commutes with
filtered colimits (`AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`), so:

- `AlgebraicGeometry.ProEtale.H_padicSubfieldSheaf`: `H^q(X_proét, E_X)` is the colimit of
  `H^q(X_proét, 𝒪_{E,X})` along multiplication by `ℓ`, i.e. `H^q(X, E_X) = H^q(X, 𝒪_{E,X})[1/ℓ]`
  (`E_X = 𝒪_{E,X}[1/ℓ]` is `AlgebraicGeometry.ProEtale.isColimitPadicSubfieldSheafCocone`);
- `AlgebraicGeometry.ProEtale.H_adicConstantSheaf`: the cohomology of the abelian sheaf
  underlying the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` is `colim_E H^q(X_proét, E_X)` over the finite
  subextensions `E ⊆ ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.isColimitPadicAlgClSheafCoconeExtend`).

Both are spelled out elementwise, as in the étale analogue
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_small`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (l : ℕ) [Fact l.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl l)]


/-- **`H^q(X_proét, E_X) = H^q(X_proét, 𝒪_{E,X})[1/ℓ]`**: on a quasi-compact quasi-separated
scheme, every class of `H^q(X_proét, E_X)` is `ℓ⁻ⁿ` times a class of `H^q(X_proét, 𝒪_{E,X})`,
and a class of `H^q(X_proét, 𝒪_{E,X})` vanishing in `H^q(X_proét, E_X)` is killed by the
transition maps (multiplication by powers of `ℓ`) of the tower `𝒪_{E,X} --ℓ--> 𝒪_{E,X} ⋯`. -/
theorem H_padicSubfieldSheaf (q : ℕ) :
    letI := normedFieldOfAlgebra l E
    (∀ x : Sheaf.H (continuousMapAbSheaf X E) q, ∃ (n : ℕ)
      (y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q),
        Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app n) q y = x) ∧
    ∀ (n : ℕ) (y : Sheaf.H (continuousMapAbSheaf X (integers l E)) q),
      Sheaf.H.map ((padicSubfieldSheafCocone X l E).ι.app n) q y = 0 →
        ∃ (m : ℕ) (a : n ⟶ m),
          Sheaf.H.map ((padicIntegersSheafMulSequence X l E).map a) q y = 0 := by
  let := normedFieldOfAlgebra l E
  have hc := (isColimitPadicSubfieldSheafCocone X l E).whiskerEquivalence
    (AsSmall.equiv.{0, 0, u + 1} (C := ℕ)).symm
  obtain ⟨h₁, h₂⟩ := Scheme.ProEt.H_map_isColimit_of_isFiltered_small X hc q
  refine ⟨fun x ↦ ?_, fun n y hy ↦ ?_⟩
  · obtain ⟨k, y, hy⟩ := h₁ x
    exact ⟨AsSmall.down.obj k, y, hy⟩
  · obtain ⟨k', a, ha⟩ := h₂ (AsSmall.up.obj n) y hy
    exact ⟨AsSmall.down.obj k', AsSmall.down.map a, ha⟩


/-- **`H^q(X_proét, ℚ̄_ℓ,X) = colim_E H^q(X_proét, E_X)`**: on a quasi-compact quasi-separated
scheme, the cohomology of the abelian sheaf underlying the constant `ℓ`-adic sheaf is the colimit
of the cohomology of the sheaves `E_X` over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
theorem H_adicConstantSheaf (q : ℕ) :
    (∀ x : Sheaf.H ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj (adicConstantSheaf l X)) q,
      ∃ (F : FiniteIntermediateField l)
        (y : Sheaf.H ((padicSubfieldSheafFunctor X l ⋙ sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj F) q),
        Sheaf.H.map (((padicAlgClSheafCocone X l).extend
          (padicAlgClSheafIsoAdicConstantSheaf X l).hom).ι.app F) q y = x) ∧
    ∀ (F : FiniteIntermediateField l)
      (y : Sheaf.H ((padicSubfieldSheafFunctor X l ⋙ sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj F) q),
      Sheaf.H.map (((padicAlgClSheafCocone X l).extend
          (padicAlgClSheafIsoAdicConstantSheaf X l).hom).ι.app F) q y = 0 →
        ∃ (F' : FiniteIntermediateField l) (a : F ⟶ F'),
          Sheaf.H.map ((padicSubfieldSheafFunctor X l ⋙ sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map a) q y = 0 := by
  have hc := (isColimitPadicAlgClSheafCoconeExtend X l).whiskerEquivalence
    (AsSmall.equiv.{0, 0, u + 1} (C := FiniteIntermediateField l)).symm
  obtain ⟨h₁, h₂⟩ := Scheme.ProEt.H_map_isColimit_of_isFiltered_small X hc q
  refine ⟨fun x ↦ ?_, fun F y hy ↦ ?_⟩
  · obtain ⟨k, y, hy⟩ := h₁ x
    exact ⟨AsSmall.down.obj k, y, hy⟩
  · obtain ⟨k', a, ha⟩ := h₂ (AsSmall.up.obj F) y hy
    exact ⟨AsSmall.down.obj k', AsSmall.down.map a, ha⟩

end AlgebraicGeometry.ProEtale
