/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier

/-!

# External products and Verdier duals with integral coefficients

The external product `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` (`ProEtale.CondensedRing.externalProduct`) and
the Verdier dual `𝔻_X K = RHom(K, Ra^! ℚ̄_ℓ)` (`ProEtale.CondensedRing.verdierDual`) of the trace
formula are defined with coefficients `ℚ̄_ℓ`. The passage from integral to `ℚ̄_ℓ`-coefficients
(blueprint `lemma-vanishing-local-term-zero-stalk`, through the integral models of
`lemma-integral-models-rational-frobenius-correspondences`) needs them for the ring of integers
`𝒪_E` of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` as well. As for the six functors on bounded
constructible complexes, they are defined for the coefficient ring
`𝒪̲_E = Profinite.padicIntegersRingObj ℓ E`, in the namespace
`ProEtale.CondensedRing.PadicIntegersRingObj`:

* `PadicIntegersRingObj.boundedConstructibleExternalProduct ℓ E M N = Lp_X^* M ⊗ Lp_Y^* N`;
* `PadicIntegersRingObj.boundedConstructibleDualizingComplex ℓ E a = Ra^! 𝒪_E`;
* `PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E a K = RHom(K, Ra^! 𝒪_E)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExternalProduct

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *external product* `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` of bounded constructible
`𝒪_E`-complexes (blueprint `prose-11-08`), with the projections `p_X = prod.fst` and
`p_Y = prod.snd`. -/
noncomputable def boundedConstructibleExternalProduct
    (M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Dᵇc((X ⨯ Y).left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
      (prod.fst : X ⨯ Y ⟶ X)).obj M ⊗
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ
      (prod.snd : X ⨯ Y ⟶ Y)).obj N

end ExternalProduct

section Dualizing

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (a : X ⟶ S)

/-- The *dualizing complex* `ω_X = Ra^! 𝒪_{E,S}` relative to `a : X ⟶ S`, with coefficients in
`𝒪̲_E`. -/
noncomputable def boundedConstructibleDualizingComplex :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (boundedConstructibleUpperShriek ℓ E a).obj (𝟙_ _)

/-- The *Verdier dual* `𝔻_X K = RHom(K, ω_X)` relative to `a : X ⟶ S`, with coefficients in
`𝒪̲_E`. -/
noncomputable def boundedConstructibleVerdierDual
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (ihom K).obj (boundedConstructibleDualizingComplex ℓ E a)

end Dualizing

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
