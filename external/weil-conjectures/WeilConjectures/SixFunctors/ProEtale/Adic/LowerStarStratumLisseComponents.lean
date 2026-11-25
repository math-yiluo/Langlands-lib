/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-!
# `Rⁱg_* ℚ̄_ℓ,T` is lisse on a stratum

Let `g : T ⟶ Y` be quasi-compact and quasi-separated and `j = i ≫ o : S ⟶ Y` a stratum (`i` a
closed immersion into a scheme `U` with noetherian underlying space, `o` an open immersion) over
which the torsion direct images `Rᵏg_* (𝒪_E ⧸ ℓ)_T` are finite locally constant, `E = ℚ_ℓ`. Then
`j^* Rⁱg_* ℚ̄_ℓ,T` is lisse, provided the integral identifications are semilinear
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit`).

The stratum need not be connected: being lisse is local
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_cover`), and the connected components of the
noetherian `S` are open. A connected component is `i⁻¹ U'` for an open `U' ⊆ U`, hence a stratum
`(i ∣_ U') ≫ U'.ι ≫ o` of the same form, connected, over which the torsion direct images are
still finite locally constant; it has universal covers, so that the connected case
(`isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit_of_universalCovers`) applies.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : FiniteIntermediateField l)

/-- The finite local constancy of the restricted torsion direct images passes to a smaller
stratum `j' = V.ι ≫ j`. -/
lemma flcProperty_upperStarRightDerivedIntegersModL_comp {T Y S S' : Scheme.{u}} (g : T ⟶ Y)
    (j : S ⟶ Y) (v : S' ⟶ S) (j' : S' ⟶ Y) (hj' : j' = v ≫ j) (k : ℕ)
    (h : Etale.flcProperty S (upperStarRightDerivedIntegersModL l E.1 g j k)) :
    Etale.flcProperty S' (upperStarRightDerivedIntegersModL l E.1 g j' k) := by
  subst hj'
  have : IsFiniteLocallyConstantSheaf
      (FA := fun M N : ModuleCat.{u + 1} (integersShrink.{u} l E.1 ⧸
        integersShrinkIdeal.{u} l E.1) ↦ M →ₗ[_] N) (CA := fun M ↦ M)
      (upperStarRightDerivedIntegersModL l E.1 g j k) := h
  exact (Etale.flcProperty S').prop_of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} (integersShrink.{u} l E.1 ⧸
      integersShrinkIdeal.{u} l E.1)) v j).app _).symm
    (IsFiniteLocallyConstantSheaf.upperStar v _)

/-- **`j^* Rⁱg_* ℚ̄_ℓ,T` is lisse on a stratum** `j = i ≫ o` (`i` a closed immersion into a scheme
with noetherian underlying space, `o` an open immersion) over which all the `Rᵏg_* (𝒪_E ⧸ ℓ)_T`
are finite locally constant, for `ℤ_ℓ → 𝒪_E` surjective (`E = ℚ_ℓ`), provided the integral
identifications are semilinear. -/
theorem isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit
    {T Y S U : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [NoetherianSpace U]
    (i : S ⟶ U) [IsClosedImmersion i] (o : U ⟶ Y) [IsOpenImmersion o]
    (h : ∀ k : ℕ, Etale.flcProperty S (upperStarRightDerivedIntegersModL l E.1 g (i ≫ o) k))
    (k : ℕ) (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    (hψι : IntegralLatticeSemilinear l g k E) :
    IsAdicLisseSheaf ((i ≫ o)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g k)) := by
  have : NoetherianSpace S := i.isClosedEmbedding.isInducing.noetherianSpace
  -- for each `s`, an open `U' ⊆ U` with `i⁻¹ U'` the connected component of `s`
  have hU' (s : S) : ∃ U' : U.Opens, i.base ⁻¹' U' = connectedComponent s := by
    obtain ⟨W, hW, hWs⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.1
      (NoetherianSpace.isOpen_connectedComponent s)
    exact ⟨⟨W, hW⟩, hWs⟩
  choose U' hU' using hU'
  let V (s : S) : S.Opens := i ⁻¹ᵁ U' s
  have hV (s : S) : ((V s : S.Opens) : Set S) = connectedComponent s := hU' s
  have hmem (s : S) : s ∈ V s := by
    change s ∈ ((V s : S.Opens) : Set S)
    rw [hV]
    exact mem_connectedComponent
  refine IsAdicLisseSheaf.of_cover (fun s ↦ (V s).ι)
    (ofArrows_opens_ι_mem_proetalePrecoverage V fun s ↦ ⟨s, hmem s⟩) fun s ↦ ?_
  have hcomp : (V s).ι ≫ i ≫ o = (i ∣_ U' s) ≫ (U' s).ι ≫ o := by
    rw [morphismRestrict_ι_assoc]
  refine IsAdicLisseSheaf.of_iso ((eqToIso (by rw [hcomp])).app _ ≪≫
    (adicUpperStarComp l (V s).ι (i ≫ o)).app _) ?_
  have : ConnectedSpace ((V s : S.Opens) : Set S) :=
    Subtype.connectedSpace (by rw [hV]; exact isConnected_connectedComponent)
  have : ConnectedSpace (V s) := this
  have : NoetherianSpace (U' s) := inferInstanceAs (NoetherianSpace (U' s : Set U))
  have : NoetherianSpace (V s) := inferInstanceAs (NoetherianSpace (V s : Set S))
  let s' : V s := ⟨s, hmem s⟩
  obtain ⟨Ũ⟩ := nonempty_universalCovers (V s) ((V s).toScheme.residueField s')
  let y : Spec (.of (AlgebraicClosure ((V s).toScheme.residueField s'))) ⟶ V s :=
    Spec.map (CommRingCat.ofHom (algebraMap ((V s).toScheme.residueField s')
      (AlgebraicClosure ((V s).toScheme.residueField s')))) ≫
        (V s).toScheme.fromSpecResidueField s'
  exact isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit_of_universalCovers l E g
    (i ∣_ U' s) ((U' s).ι ≫ o)
    (fun k ↦ flcProperty_upperStarRightDerivedIntegersModL_comp l E g (i ≫ o) (V s).ι _
      hcomp.symm k (h k)) Ũ y k hsurj hψι

end AlgebraicGeometry.ProEtale
