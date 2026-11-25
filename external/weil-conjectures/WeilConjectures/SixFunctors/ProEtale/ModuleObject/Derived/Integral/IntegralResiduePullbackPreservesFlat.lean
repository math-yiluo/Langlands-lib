/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat

/-! Flatness preservation for the integral residue pullback.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-pullback-preserves-flat)

The proof is the local flatness argument for inverse image of module sheaves,
transported across the coefficient pullback isomorphism. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResiduePullbackPreservesFlat
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The inverse image of sheaves of modules over the continuous integral
coefficients sends flat objects to flat objects. The proof uses the local
relation criterion for flatness, invariance under extension along the
coefficient pullback isomorphism, and preservation of colimits by inverse
image.
Source: Stacks Project, Tag 05VD, lemma-pullback-flat.
(blueprint: new-integral-residue-pullback-preserves-flat)

Proof. Restriction along the inverse coefficient isomorphism is naturally
isomorphic to extension along the coefficient isomorphism. Whisker this
isomorphism with ambient inverse image on module objects. The resulting functor
preserves flatness by inverseImageModule_preservesFlat, and flatness is invariant
under each component of the comparison isomorphism. -/
theorem integralResidue_pullback_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat := by
  let G := (f)^*[Ab.{u + 1}]
  let R := condensedRingObj (integralCoeff ℓ E) Y
  let ρ := (asIso (condensedPullbackHom (integralCoeff ℓ E) f)).inv
  have h := inverseImageModule_preservesFlat f R
    (condensedRingObj (integralCoeff ℓ E) X) ρ
  let e : (f)^*⟦integralCoeff ℓ E⟧ ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom (integralCoeff ℓ E) f))
  exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _)
    (h.flat_obj hM)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
