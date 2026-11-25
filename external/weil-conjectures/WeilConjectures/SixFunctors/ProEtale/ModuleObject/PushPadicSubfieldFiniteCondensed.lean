/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextensionBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic

/-!
# `F_X` is a finite free `E_X`-module

Let `ℓ` be a prime and `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`. For a basis `b₁, …, bₙ` of
`F` over `E`, the map `E̲ⁿ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism of condensed abelian groups
(`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`, in
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextensionBasis`). Pulling back
along `p_X`, the same holds for `E_X ⟶ F_X` on any scheme `X`
(`AlgebraicGeometry.ProEtale.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Functor.LaxMonoidal

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ}
  (hF : E ≤ F)

/-- **`F_X` is a finite free `E_X`-module**: if `b₁, …, bₙ` is a basis of `F` over `E`, in the
sense that `E̲ⁿ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism, then so is its pullback
`E_Xⁿ ⟶ F_X`, `bᵢ` acting through the constant global section `p_X^* bᵢ`. -/
lemma isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul {n : ℕ} (b : Fin n → F)
    (h : IsIso (biproduct.desc fun i ↦
      Profinite.padicSubfieldRingObjMap ℓ hF ≫ Mod.globalSmul
        (Profinite.continuousMapConstRingHom F (b i)).hom
          (Mod.regular (Profinite.continuousMapRingObj F)) :
        ⨁ (fun _ : Fin n ↦ Profinite.continuousMapRingObj.{u} E) ⟶
          Profinite.continuousMapRingObj F)) :
    IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap X ℓ hF ≫ Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom F (b i)).hom)
        (Mod.regular (padicSubfieldRingObj X ℓ F)) :
        ⨁ (fun _ : Fin n ↦ padicSubfieldRingObj X ℓ E) ⟶ padicSubfieldRingObj X ℓ F) :=
  CondensedRing.isIso_biproductDesc_coefficientMap_globalSmul _
    (Profinite.continuousMapConstRingHom F) b h X

end AlgebraicGeometry.ProEtale
