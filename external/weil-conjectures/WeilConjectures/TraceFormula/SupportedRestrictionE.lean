/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChange
public import WeilConjectures.TraceFormula.Product

/-!
# The supported restriction with `E`-coefficients

For a finite subextension `E` of `ℚ̄_ℓ / ℚ_ℓ` and a fixed locus `F` of a correspondence, the
compact-support base change isomorphism of the fixed square with `E`-coefficients
(`Correspondence.FixedLocus.lowerShriekBaseChangeIsoE`) and the supported restriction
`Lι^* Rc^! P ⟶ Rd^! LΔ^* P` it defines (`Correspondence.FixedLocus.supportedRestrictionE`).
Its compatibility with the extension of scalars to `ℚ̄_ℓ` is in
`WeilConjectures.TraceFormula.SupportedRestrictionRational`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

namespace Correspondence.FixedLocus

variable (F : c.FixedLocus) (E : FiniteIntermediateField ℓ)

/-- Compact-support base change `Rc_! ⋙ LΔ^* ≅ Lι^* ⋙ Rd_!` in the fixed square, with
`E`-coefficients. -/
noncomputable def lowerShriekBaseChangeIsoE :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E c.support ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ F.ι ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E F.d :=
  asIso (boundedConstructibleLowerShriekBaseChange_padicSubfield ℓ E F.isPullback)

/-- The supported restriction `Lι^* Rc^! P ⟶ Rd^! LΔ^* P` with `E`-coefficients: the mate
`Rc^! ⋙ Lι^* ⟶ LΔ^* ⋙ Rd^!` of the inverse of compact-support base change in the fixed square. -/
noncomputable def supportedRestrictionE
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E c.support).obj P) ⟶
      (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj P) :=
  (CategoryTheory.mateEquiv
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E c.support)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E F.d)
    (TwoSquare.mk _ _ _ _ (F.lowerShriekBaseChangeIsoE E).inv)).app P

end Correspondence.FixedLocus

end AlgebraicGeometry.ProEtale.CondensedRing
