/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackFactor
public import WeilConjectures.WeilSheaf.SmoothPurityRationalRootLaw
public import WeilConjectures.WeilSheaf.SmoothPurityFrobeniusFactorAlias
public import WeilConjectures.WeilSheaf.SmoothPurityCyclotomicField
public import WeilConjectures.WeilSheaf.SmoothPurityScalarIsoTransport
import WeilConjectures.Tactic.ExactModProofs

/-! # A module interface for the scalar Tate comparison

The coefficient-changed root object retains its original spelling. Pullback,
the comparison maps and their compatibility equations are exported separately.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

local instance : NeZero (ℓ : k) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k _) Fact.out]
  exact Fact.out⟩
local instance : NeZero (ℓ : AlgebraicClosure k) :=
  WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ

/-- Pullback from the finite-base model. -/
noncomputable def purityScalarBasePull :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj

/-- Frobenius pullback in the scalar interface. -/
noncomputable def purityScalarFrobeniusPull :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricGaloisFrobenius.asIso.hom

/-- The pulled-back Tate object, named separately from its pullback functor. -/
noncomputable def purityScalarSourceObject :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj).obj
    (tateTwistOne X ℓ)

/-- The pulled-back unit object. -/
noncomputable def purityScalarSourceUnit :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj).obj (𝟙_ _)

/-- The Tate pullback comparison in the original coefficient spelling. -/
noncomputable def purityScalarTateCompare :
    purityScalarSourceObject ℓ a ≅
      tateTwistOne a.geometricFiber ℓ :=
  upperStarTateTwistOneIso ℓ a.geometricFiberProj a

/-- The unit pullback comparison. -/
noncomputable def purityScalarUnitCompare :
    purityScalarSourceUnit ℓ a ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) a.geometricFiberProj)).symm

/-- The whole descent isomorphism on the pulled-back Tate object. -/
noncomputable def purityScalarSourceIso :
    (purityScalarFrobeniusPull ℓ a).obj (purityScalarSourceObject ℓ a) ≅
      purityScalarSourceObject ℓ a :=
  (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
    (tateTwistOne X ℓ)

omit [Fact (ringChar k ≠ ℓ)] in
/-- Identify the whole isomorphism before projecting its morphism. -/
lemma purityScalarSourceIso_eq :
    purityScalarSourceIso ℓ a =
      (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
        ((Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
          (tateModule X ℓ)) := (rfl)

/-- The whole descent isomorphism on the pulled-back unit. -/
noncomputable def purityScalarSourceUnitIso :
    (purityScalarFrobeniusPull ℓ a).obj (purityScalarSourceUnit ℓ a) ≅
      purityScalarSourceUnit ℓ a :=
  (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app (𝟙_ _)

omit [Fact (ringChar k ≠ ℓ)] in
lemma purityScalarSourceUnitIso_eq :
    purityScalarSourceUnitIso ℓ a =
      (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).app
        (𝟙_ _) := (rfl)

/-- The descent datum on the root module. -/
noncomputable def purityScalarSourceDatum :
    (purityScalarFrobeniusPull ℓ a).obj (purityScalarSourceObject ℓ a) ⟶
      purityScalarSourceObject ℓ a :=
  (purityScalarSourceIso ℓ a).hom

/-- The descent datum on the pulled-back unit. -/
noncomputable def purityScalarSourceUnitDatum :
    (purityScalarFrobeniusPull ℓ a).obj (purityScalarSourceUnit ℓ a) ⟶
      purityScalarSourceUnit ℓ a :=
  (purityScalarSourceUnitIso ℓ a).hom

/-- The canonical Tate datum on the geometric fibre. -/
noncomputable def purityScalarTargetDatum :
    (purityScalarFrobeniusPull ℓ a).obj (tateTwistOne a.geometricFiber ℓ) ⟶
      tateTwistOne a.geometricFiber ℓ :=
  (upperStarTateTwistOneIso ℓ a.geometricGaloisFrobenius.asIso.hom
    a.geometricFiberToAlgebraicClosure).hom

/-- The unit datum on the geometric fibre. -/
noncomputable def purityScalarTargetUnitDatum :
    (purityScalarFrobeniusPull ℓ a).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  (Functor.Monoidal.εIso
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      a.geometricGaloisFrobenius.asIso.hom)).inv

lemma purityScalarTateCompare_comm :
    (purityScalarFrobeniusPull ℓ a).map (purityScalarTateCompare ℓ a).hom ≫
        purityScalarTargetDatum ℓ a =
      purityScalarSourceDatum ℓ a ≫ (purityScalarTateCompare ℓ a).hom := by
  have h := purity_upperStarTateTwistOneIso_factor ℓ a.geometricFiberProj
    a.geometricGaloisFrobenius.asIso.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj a
  rw [purity_upperStarTateTwistOneIso_independent_base ℓ a.geometricGaloisFrobenius.asIso.hom
    (a.geometricFiberProj ≫ a) a.geometricFiberToAlgebraicClosure,
    ← purity_geometricFiberProjUpperStarFrobeniusIso_eq (Profinite.padicAlgClRingObj ℓ) a] at h
  dsimp only [purityScalarFrobeniusPull, purityScalarTateCompare,
    purityScalarTargetDatum, purityScalarSourceDatum, purityScalarSourceIso,
    purityScalarSourceObject, Iso.app_hom,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

omit [Fact (ringChar k ≠ ℓ)] in
lemma purityScalarUnitCompare_comm :
    (purityScalarFrobeniusPull ℓ a).map (purityScalarUnitCompare ℓ a).hom ≫
        purityScalarTargetUnitDatum ℓ a =
      purityScalarSourceUnitDatum ℓ a ≫ (purityScalarUnitCompare ℓ a).hom := by
  have h := purity_upperStar_unit_factor (Profinite.padicAlgClRingObj ℓ)
    a.geometricFiberProj a.geometricGaloisFrobenius.asIso.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
  rw [← purity_geometricFiberProjUpperStarFrobeniusIso_eq
    (Profinite.padicAlgClRingObj ℓ) a] at h
  dsimp only [purityScalarFrobeniusPull, purityScalarUnitCompare,
    purityScalarTargetUnitDatum, purityScalarSourceUnitDatum, purityScalarSourceUnitIso,
    purityScalarSourceUnit, Iso.app_hom,
    Iso.symm_hom, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

variable {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- The root trivialization before transporting to the canonical Tate line. -/
noncomputable def purityScalarRootTrivialization :
    purityScalarSourceObject ℓ a ≅
      purityScalarSourceUnit ℓ a :=
  purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
    (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
    (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
      a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
      (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso)

omit [Fact (ringChar k ≠ ℓ)] in
lemma purityScalarRootTrivialization_eq :
    purityScalarRootTrivialization ℓ a hζ hζ' =
      purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[ℓ])
        (Profinite.padicIntRingObjToPadicAlgCl ℓ) a.geometricFiberProj (tateModule X ℓ)
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ' ≪≫
          (a.geometricFiberProj)^*[Ab.{u + 1}].mapModUnitIso) := (rfl)

/-- The canonical geometric trivialization in the scalar interface. -/
noncomputable def purityScalarCanonicalTrivialization :
    tateTwistOne a.geometricFiber ℓ ≅
      𝟙_ (Mod (Sheaf (ProEt.topology a.geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) a.geometricFiber)) :=
  (purityScalarTateCompare ℓ a).symm ≪≫ purityScalarRootTrivialization ℓ a hζ hζ' ≪≫
    purityScalarUnitCompare ℓ a

lemma purityScalarCanonicalTrivialization_eq :
    purityScalarCanonicalTrivialization ℓ a hζ hζ' =
      (purityScalarTateCompare ℓ a).symm ≪≫ purityScalarRootTrivialization ℓ a hζ hζ' ≪≫
        purityScalarUnitCompare ℓ a := (rfl)

omit [Fact (ringChar k ≠ ℓ)] in
/-- Expose the source datum as a projection before using the native scalar law. -/
lemma purityScalarSourceDatum_eq_iso :
    purityScalarSourceDatum ℓ a = (purityScalarSourceIso ℓ a).hom := rfl

omit [Fact (ringChar k ≠ ℓ)] in
/-- Expose the source unit datum as a projection. -/
lemma purityScalarSourceUnitDatum_eq_iso :
    purityScalarSourceUnitDatum ℓ a = (purityScalarSourceUnitIso ℓ a).hom := rfl

/-- Export the scalar equation in the original Frobenius convention. -/
lemma purityScalarCanonicalEquation
    (h : (Nat.card k : ℤ) •
        (purityScalarTargetDatum ℓ a ≫ (purityScalarCanonicalTrivialization ℓ a hζ hζ').hom) =
      (purityScalarFrobeniusPull ℓ a).map
          (purityScalarCanonicalTrivialization ℓ a hζ hζ').hom ≫
        purityScalarTargetUnitDatum ℓ a) :
    (Nat.card k : ℤ) •
        ((upperStarTateTwistOneIso ℓ a.geometricGaloisFrobenius.asIso.hom
          a.geometricFiberToAlgebraicClosure).hom ≫
          (purityScalarCanonicalTrivialization ℓ a hζ hζ').hom) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          a.geometricGaloisFrobenius.asIso.hom).map
          (purityScalarCanonicalTrivialization ℓ a hζ hζ').hom ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            a.geometricGaloisFrobenius.asIso.hom)).inv := by
  dsimp only [purityScalarFrobeniusPull, purityScalarTargetDatum,
    purityScalarTargetUnitDatum, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
