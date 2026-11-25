/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullbackInterface
public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarRoot
public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarEquation
import WeilConjectures.Tactic.ExactModProofs

/-! # The scalar law immediately after rational coefficient change -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.K4Native

open CondensedRing

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

omit [Fact (ringChar k ≠ ℓ)] in
/-- Identify the whole descent isomorphism with its normalized native component. -/
lemma scalarSourceIso_eq :
    purityScalarSourceIso ℓ a =
      scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)) := by
  rw [purityScalarSourceIso_eq]
  rfl

omit [Fact (ringChar k ≠ ℓ)] in
/-- Identify the whole unit descent isomorphism. -/
lemma scalarSourceUnitIso_eq :
    purityScalarSourceUnitIso ℓ a =
      scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a (𝟙_ _) := by
  rw [purityScalarSourceUnitIso_eq]
  rfl

/-- Package the native law without changing the raw coefficient source. -/
lemma scalarRootEquation_native :
    CategoryTheory.K4Native.scalarEquation
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.hom)
      (scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ))).hom
      (scalarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a (𝟙_ _)).hom
      (purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
        (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
          (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)) (Nat.card k : ℤ) := by
  dsimp only [CategoryTheory.K4Native.scalarEquation]
  exact_mod_proofs purity_rationalRootTrivialization_weil a hζ hζ'

/-- Change only the data arguments of the scalar interface. -/
lemma scalarRootEquation_named :
    CategoryTheory.K4Native.scalarEquation (purityScalarFrobeniusPull ℓ a)
      (purityScalarSourceDatum ℓ a) (purityScalarSourceUnitDatum ℓ a)
      (purityScalarRootTrivialization ℓ a hζ hζ') (Nat.card k : ℤ) := by
  dsimp only [purityScalarFrobeniusPull]
  rw [purityScalarSourceDatum_eq_iso, purityScalarSourceUnitDatum_eq_iso,
    scalarSourceIso_eq, scalarSourceUnitIso_eq, purityScalarRootTrivialization_eq]
  exact_mod_proofs scalarRootEquation_native a hζ hζ'

end AlgebraicGeometry.ProEtale.K4Native
