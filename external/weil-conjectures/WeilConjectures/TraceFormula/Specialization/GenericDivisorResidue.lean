/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisseLocus
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorResidueLisse

/-!

# Generic vanishing along a divisor for finite coefficients

Let `X` be normal, `Z = V(h)` a principal divisor with complement `j : X ∖ Z ⟶ X`, `ζ` a generic
point of `Z`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with residue field `𝔽_E`, and `F` a bounded
constructible complex of `𝔽_E`-module objects on `X ∖ Z`. The restriction `Le^* Ψ_X(j_! F)` of the
nearby cycles of the deformation to the normal cone to the zero section vanishes over a
neighbourhood of `ζ`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`). This is
blueprint `lemma-vanishing-generic-points-principal-divisor--1` for finite coefficients and
complexes `L = j_! F` with `Li^* L = 0`.

## Proof

The blueprint argument, with finite coefficients throughout:

* shrink `X` around `ζ` until the étale model of `F` has finite locally constant cohomology on
  `X ∖ Z` (`exists_opens_lisse_reduction`, `GenericDivisorLisseLocus.lean`);
* the lisse case (`nearbyCyclesVanishNear_lowerShriek_residueField_of_lisse`,
  `GenericDivisorResidueLisse.lean`): an `ℓ`-Sylow finite étale cover, its trace, the
  normalisation of `X` in it, the proper exchange of nearby cycles, and the dévissage of
  complexes with finite `ℓ`-group monodromy reduce to the constant case
  (`nearbyCyclesVanishNear_lowerShriek_unit_residueField`, `GenericDivisorResidueConstant.lean`).

The constant case over an imperfect base field is `sorry`ed (see
`GenericDivisorResidueConstant.lean`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Generic vanishing along a divisor for finite coefficients** (blueprint
`lemma-vanishing-generic-points-principal-divisor--1` with coefficients `𝔽_E`, for extensions by
zero from the complement of the divisor): let `X` be normal, `Z = V(h)` for a nonzero global
function `h`, `j : X ∖ Z ⟶ X` the complement, `ζ` a generic point of an irreducible component of
`Z`, and `F` a bounded constructible complex of `𝔽_E`-module objects on `X ∖ Z`. Then
`Le^* Ψ_X(j_! F)` vanishes over a neighbourhood of `ζ`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F : DerivedCategory (Mod (Sheaf (ProEt.topology (overRestrict X I.support.compl).left)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
        (overRestrict X I.support.compl).left)))
    (hF : boundedConstructible _ F) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
          (((deformationModel X I k').nearbyCycles
            (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))).obj
            (D(((overRestrictι X I.support.compl).left)_!open⟦
              Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj F)))) := by
  have hred := exists_opens_lisse_reduction k' hX hh hI ζ hζ E F hF
  obtain ⟨V, ζV, hζV, hXV, hhV, hIV, hζVg, K, F', -, ⟨a, b, ha, hb⟩, hl, ⟨e⟩, himp⟩ := hred
  exact himp (nearbyCyclesVanishNear_lowerShriek_residueField_of_lisse k' hXV hhV hIV ζV hζVg E K
    F' a b ha hb hl e)

end AlgebraicGeometry.ProEtale.CondensedRing
