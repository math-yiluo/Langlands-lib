/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

/-!
# Lisse sheaves on a strictly henselian local scheme are constant

Let `R` be a strictly henselian local ring. A weakly étale morphism `f : V ⟶ Spec R` whose image
contains the closed point has a section: an affine open `Spec S ⊆ V` meeting the fibre over the
closed point is faithfully flat over `R` (flat morphisms lift generizations, and every point of
`Spec R` generizes the closed point), and a faithfully flat weakly étale `R`-algebra has a
retraction (`IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale`).

Consequently a lisse `ℓ`-adic sheaf on `Spec R` is constant: one member of a trivialising
pro-étale cover hits the closed point and has a section `s`, and `F ≅ s^* f^* F ≅ s^* ℚ̄_ℓⁿ`.

## Main statements

- `AlgebraicGeometry.exists_section_of_weaklyEtale_of_isStrictlyHenselianLocalRing`
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_unit_of_isStrictlyHenselian`
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

/-- A weakly étale morphism to the spectrum of a strictly henselian local ring whose image
contains the closed point has a section. -/
theorem exists_section_of_weaklyEtale_of_isStrictlyHenselianLocalRing {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] {V : Scheme.{u}} (f : V ⟶ Spec (.of R)) [WeaklyEtale f]
    (hf : IsLocalRing.closedPoint R ∈ Set.range f) :
    ∃ s : Spec (.of R) ⟶ V, s ≫ f = 𝟙 _ := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨u, hu⟩ := V.affineCover.covers v
  let p := V.affineCover.f (V.affineCover.idx v) ≫ f
  have : Surjective p := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨u', -, hu'⟩ := Flat.generalizingMap p (a := u) (b := x) (by
      simp only [p, Scheme.Hom.comp_apply, hu, hv]
      exact IsLocalRing.specializes_closedPoint x)
    exact ⟨u', hu'⟩
  have := IsStrictlyHenselianLocalRing.isWContractibleRing R
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (R := .of R) p
  exact ⟨s ≫ V.affineCover.f (V.affineCover.idx v), by rwa [Category.assoc]⟩

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- A lisse `ℓ`-adic sheaf on the spectrum of a strictly henselian local ring is constant: a
finite direct sum of copies of `ℚ̄_ℓ`. -/
theorem IsAdicLisseSheaf.exists_iso_biproduct_unit_of_isStrictlyHenselian {R : Type u}
    [CommRing R] [IsStrictlyHenselianLocalRing R] {F : AdicSheaf l (Spec (.of R))}
    (hF : IsAdicLisseSheaf F) :
    ∃ n : ℕ, Nonempty (F ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of R))) := by
  obtain ⟨P, hP, h⟩ := hF
  obtain ⟨𝒰, _, rfl⟩ :=
    (Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover (P := @WeaklyEtale)).1 hP
  let i := 𝒰.idx (IsLocalRing.closedPoint R)
  have : WeaklyEtale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨s, hs⟩ := exists_section_of_weaklyEtale_of_isStrictlyHenselianLocalRing (𝒰.f i)
    (𝒰.covers _)
  obtain ⟨n, ⟨e⟩⟩ := h (𝒰.f i) ⟨i⟩
  exact ⟨n, ⟨((adicUpperStarId l _).app F).symm ≪≫ (adicUpperStarCongr l hs.symm).app F ≪≫
    (adicUpperStarComp l s (𝒰.f i)).app F ≪≫ (s)^*ᵃ[l].mapIso e ≪≫
    (s)^*ᵃ[l].mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ adicUpperStarUnitIso l s⟩⟩

end ProEtale

end AlgebraicGeometry
