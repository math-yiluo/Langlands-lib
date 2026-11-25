/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionRationalConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Reduction and rationalization of `𝒪_E`-complexes: isomorphisms and constructibility

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and
residue field `𝔽_E`, and `X` a scheme.

* A morphism `f` of `𝒪_E`-complexes on `X_proét` is an isomorphism as soon as its reduction
  `𝔽_E ⊗ᴸ_{𝒪_E} f` and its rationalization `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} f)` are
  (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_of_isIso_extendScalars_residueField_padicAlgCl`):
  the three derived extensions of scalars are triangulated, being left adjoint to the
  triangulated restrictions of scalars, so they send the cone of `f` to the cones of the reduction
  and of the rationalization, which vanish; conclude by
  `AlgebraicGeometry.ProEtale.CondensedRing.isZero_of_isZero_extendScalars_residueField_padicAlgCl`.
* The rationalization `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K)` of a bounded constructible `𝒪_E`-complex `K` is
  bounded constructible
  (`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_extendScalars_padicAlgCl_obj`),
  both extensions of scalars being exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {X : Scheme.{u}}

/-- The derived extension of scalars along `a_X : Λ_X ⟶ Λ'_X` sends the third object of a
distinguished triangle whose first morphism it inverts to a zero object: it is triangulated,
being left adjoint to the triangulated restriction of scalars. -/
lemma isZero_leftDerivedFunctor_extendScalars_obj₃
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    {T : Triangle (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))} (hT : T ∈ distTriang _)
    (h : IsIso ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map T.mor₁)) :
    IsZero ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj T.obj₃) := by
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have := adj.isTriangulated_leftAdjoint
  exact (Triangle.isZero₃_iff_isIso₁ _
    ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map_distinguished _ hT)).2 h

-- the derived extensions of scalars are large terms
/-- **Isomorphisms are detected by reduction and rationalization**: a morphism `f` of
`𝒪_E`-complexes on `X_proét` whose reduction `𝔽_E ⊗ᴸ_{𝒪_E} f` and rationalization
`ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} f)` are isomorphisms is an isomorphism: the cone of `f` has vanishing
reduction and rationalization. -/
theorem isIso_of_isIso_extendScalars_residueField_padicAlgCl
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (f : K ⟶ L)
    (h₁ : IsIso ((Mod.extendScalars (coefficientMap
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.map f))
    (h₂ : IsIso ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).leftDerivedFunctor.map
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.map f))) :
    IsIso f := by
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hC₁ := isZero_leftDerivedFunctor_extendScalars_obj₃
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1) hT h₁
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have := adj.isTriangulated_leftAdjoint
  have hT₁ := (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X)).leftDerivedFunctor.map_distinguished _ hT
  have hC₂ := isZero_leftDerivedFunctor_extendScalars_obj₃
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) hT₁ h₂
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_extendScalars_residueField_padicAlgCl ℓ E C hC₁ hC₂)

/-- The rationalization `ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K)` of a bounded constructible `𝒪_E`-complex `K`
on `X_proét` is bounded constructible. -/
lemma boundedConstructible_extendScalars_padicAlgCl_obj
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
            X)).leftDerivedFunctor.obj K)) :=
  boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E
    ⟨_, boundedConstructible_derivedExtendScalars_obj X ℓ E ⟨K, hK⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
