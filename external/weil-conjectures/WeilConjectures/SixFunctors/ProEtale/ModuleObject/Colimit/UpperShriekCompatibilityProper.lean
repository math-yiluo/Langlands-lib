/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldPushCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility

/-!
# Compatibility of `Rf^!` with the extension of scalars `E ⟶ ℚ̄_ℓ`: the proper part

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `k` a field of characteristic
`p ≠ ℓ`. For a separated morphism `f : X ⟶ Y` of `k`-schemes of finite type we show that the
exchange `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriekToPadicAlgCl`) is an isomorphism
(`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl`): the clause on `f^!`
of blueprint `proposition-six-operations-change-coefficients` for the coefficient change `E ⟶ ℚ̄_ℓ`.

By `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso` it suffices
to treat the proper part `g` of a compactification. The category `Dᵇc(-)⟦ℚ̄_ℓ⟧` is the filtered
2-colimit of the categories `Dᵇc(-)⟦E⟧` over the finite subextensions
(`ProEtale.CondensedRing.boundedConstructibleCocone_isFilteredTwoColimit`), the (Push)
isomorphisms satisfy the cocycle condition
(`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq`), and the
exchanges for `g^!` between finite subextensions are isomorphisms
(`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield`);
so the exchange for `g^!` towards `ℚ̄_ℓ` is an isomorphism
(`CategoryTheory.CategoryCocone.isIso_mateEquiv_of_isFilteredTwoColimit`).
-/

@[expose] public section


universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper part `g` of a compactification
is an isomorphism: `Dᵇc(-)⟦ℚ̄_ℓ⟧` is the filtered 2-colimit of the `Dᵇc(-)⟦E⟧`, and the exchanges
for `g^!` between finite subextensions are isomorphisms. -/
instance isIso_boundedConstructibleProperUpperShriekToPadicAlgCl {f : X ⟶ Y}
    (c : Compactification f.left) :
    IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E c) := by
  have := noetherianSpace_left_of_over c.overObj
  have := noetherianSpace_left_of_over Y
  have hcocycle (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : F ≤ G) :=
    boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq ℓ h c.overG
  have hT (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : F ≤ G) :=
    isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG
  have H := CategoryCocone.isIso_mateEquiv_of_isFilteredTwoColimit
    (fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦ Adjunction.ofIsLeftAdjoint
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F c.overG))
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar ℓ c.overG))
    (fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦
      boundedConstructibleLowerStarToPadicAlgClIso ℓ F c.overG)
    (fun _ _ h ↦ asIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h c.overG))
    (boundedConstructibleCocone_isFilteredTwoColimit c.overObj.left ℓ)
    (boundedConstructibleCocone_isFilteredTwoColimit Y.left ℓ) hcocycle (fun F G h ↦ ?_) E
  · exact H
  · dsimp only [boundedConstructibleCocone, asIso_inv]
    with_reducible exact hT F G h

variable (f : X ⟶ Y)

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image`
(`proposition-six-operations-change-coefficients`), the clause on `f^!` for the coefficient change
`E ⟶ ℚ̄_ℓ`: the canonical comparison `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}` (the mate of the
lower-shriek comparison) is an isomorphism on bounded constructible complexes. -/
theorem isIso_boundedConstructibleUpperShriekToPadicAlgCl :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso ℓ E f

end AlgebraicGeometry.ProEtale.CondensedRing
