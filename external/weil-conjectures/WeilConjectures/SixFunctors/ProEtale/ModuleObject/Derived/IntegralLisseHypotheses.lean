/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerived

/-!
# The integral coefficients satisfy the hypotheses of the closure of `Dᵇc` under `⊗ᴸ` and `RHom`

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. On a scheme `Z`
with noetherian underlying space, let `A` be a bounded complex of module objects over `𝒪̲_{E,Z}`
whose cohomology sheaves are pro-étale locally finitely presented (lisse `𝒪_E`-sheaves). If `L`
is a bounded complex with lisse cohomology sheaves, then `A ⊗ᴸ L` is bounded constructible
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_tensorObj_of_lisse_homology`);
if `L` is bounded constructible, then `RHom(A, L)` is bounded constructible
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_ihom_of_lisse_homology`). So
`𝒪̲_E` satisfies `ProEtale.CondensedRing.LisseHypotheses`
(`ProEtale.CondensedRing.PadicIntegersRingObj.lisseHypotheses`).

Unlike for the field coefficients, a lisse `𝒪_E`-sheaf is not locally free: it is pro-étale
locally isomorphic to a constant finitely generated `𝒪_E`-module `⊕ 𝒪_E/ϖ^{eᵢ} ⊕ 𝒪_E^r`
(Bhatt–Scholze, Section 6.8). Placed in any degree, it is nevertheless dualizable, with a lisse
dual
(`PadicIntegersRingObj.exists_exactPairing_singleFunctor_of_isLocallyFinitelyPresented`),
so that `RHom(P[q], L) ≅ P'[-q] ⊗ᴸ L` reduces the internal hom to the tensor product.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The coefficient ring `𝒪̲_E` satisfies `ProEtale.CondensedRing.LisseTensorHypotheses`. -/
theorem lisseTensorHypotheses : LisseTensorHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) where
  isTriangulated _ _ := inferInstance
  tensorObj Z _ _ _ hA hA' hL hL' :=
    boundedConstructible_tensorObj_of_lisse_homology ℓ E Z hA hA' hL hL'

/-- The derived internal hom `RHom(A, L)` from a bounded complex `A` of `𝒪̲_E`-module objects
with lisse cohomology sheaves to a bounded constructible complex `L` is bounded constructible: by
dévissage in `A` it suffices to treat `A = P[q]` with `P` lisse, and `P[q]` has a lisse left dual
`D`, so that `RHom(P[q], L) ≅ D ⊗ᴸ L`. -/
theorem boundedConstructible_ihom_of_lisse_homology (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {A L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))}
    (hA : DerivedCategory.TStructure.t.bounded A)
    (hA' : ∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((DerivedCategory.homologyFunctor _ n).obj A))
    (hL : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)
      ((ihom A).obj L) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)) :=
    ⟨fun e h ↦ h.of_iso e⟩
  let Q : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z))) :=
    fun A ↦ boundedConstructible _ ((ihom A).obj L)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (boundedConstructible _).prop_of_iso
      ((MonoidalClosed.internalHom.mapIso e.op).app L).symm h⟩
  refine DerivedCategory.prop_of_bounded_of_degreewise Q (fun A hA ↦ ?_)
    (fun T hT h₁ h₃ ↦ ?_) (fun _ ↦ IsLocallyFinitelyPresented _) (fun q P hP ↦ ?_) A hA hA'
  · refine boundedConstructible_of_isZero _ ?_
    rw [IsZero.iff_id_eq_zero]
    apply ((ihom.adjunction A).homEquiv _ _).symm.injective
    exact (((curriedTensor _).flip.obj ((ihom A).obj L)).map_isZero hA).eq_of_src _ _
  · have := isLeftDerivabilityStructure_localizerMorphismKFlat
      (Profinite.padicIntegersRingObj ℓ E) Z
    obtain ⟨h, hT'⟩ := DerivedCategory.exists_distinguished_ihom_pre T hT L
    exact (boundedConstructible _).ext_of_isTriangulatedClosed₂ _ hT' h₃ h₁
  · obtain ⟨D, hD, hD', ⟨e⟩⟩ :=
      exists_exactPairing_singleFunctor_of_isLocallyFinitelyPresented ℓ E Z hP q
    let := e
    exact (boundedConstructible _).prop_of_iso (MonoidalClosed.ihomObjIsoTensor _ _ L).symm
      (boundedConstructible_tensorObj (lisseTensorHypotheses ℓ E)
        (boundedConstructible_of_isLocallyFinitelyPresented_homology _ hD hD') hL)

/-- The coefficient ring `𝒪̲_E` satisfies `ProEtale.CondensedRing.LisseHypotheses`. -/
theorem lisseHypotheses : LisseHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) where
  toLisseTensorHypotheses := lisseTensorHypotheses ℓ E
  ihom Z _ _ _ hA hA' hL := boundedConstructible_ihom_of_lisse_homology ℓ E Z hA hA' hL

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
