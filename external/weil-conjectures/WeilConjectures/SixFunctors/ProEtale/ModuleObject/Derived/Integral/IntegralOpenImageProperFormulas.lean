/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperCohomologicalBounds
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralLocalizingProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.IntegralOpenDirectImage.IntegralOpenDirectImage

/-!
# Integral open direct image and proper formulas

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic/_section.md
(blueprint: lemma-projection-formula-integral-coefficients).

The three statements use internal modules over the pulled-back condensed ring of integers.
The base change and projection conclusions include membership of both endpoints in the
localizing closure. Since this is a full subcategory, ambient invertibility then says exactly
that these maps are isomorphisms in that subcategory. No completed tensor is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the coefficient inverse image opaque while elaborating derived endpoints.
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.derivedComapLowerStarIso

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

attribute [local irreducible] integerRingSheafIso

section OpenImage

variable {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]

/-- Quasi-compact open direct image preserves bounded constructible finite-Tor objects.
Source: blueprint main-20261015, lemma-projection-formula-integral-coefficients, first assertion
(blueprint: lemma-projection-formula-integral-coefficients).

Proof: the standing finite-type separated hypotheses give qcqs by
lem-weil-pbc-qcqs-over-affine. Apply clause (2) of
 det-def-localizing-closure-ctf-equals-bc to identify Dctf with Dbc for O_E.
The proved integer-ring isomorphism identifies the embedded and spectral coefficient
presentations. Exact scalar restriction preserves bounded constructible cohomology, and
its derived direct-image comparison transports proposition-direct-image-along-open-immersion--1 back
to the pulled-back embedded coefficient ring. Its final conclusion places Rj_*K in Dbc(X,O_E); the
same identification gives Dctf(X,O_E). That detail theorem proves derived completeness by
Stacks 099L, identifies residue reduction with the direct image of the reduction because
reduction is a cone, applies torsion open finiteness, then uses the residue criterion 09C1.
-/
theorem integralOpenDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of k))]
    (K : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E.val) U) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) j).obj K.obj) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) j).obj K.obj)   := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
  let e : Profinite.padicIntegersRingObj.{u} ℓ E.val ≅
      DerivedNakayama.integerRing ℓ (ULift.{u} E.val) :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := by
    dsimp only [e]
    exact Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom e.inv := by dsimp only [e]; infer_instance
  let T : Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) U) ⥤
      Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) U) :=
    Mod.comap (coefficientMap e.inv U)
  have hK := (bounded_transport_iff e U K.obj).2 K.property.1
  have h := (IntegralOpenDirectImage.integral_open_direct_image ℓ (ULift.{u} E.val)
    j k (T.mapDerivedCategory.obj K.obj) hK).2.2.1
  have (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let i := (derivedComapLowerStarIso e.inv j).app K.obj
  have hbc : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) j).obj K.obj) :=
    (bounded_transport_iff e X _).1
      ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso i.symm h.1,
        fun n ↦ constructible_iso
          (Λ := DerivedNakayama.integerRing ℓ (ULift.{u} E.val))
          ((DerivedCategory.homologyFunctor _ n).mapIso i.symm) (h.2 n)⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  have heq := (localizingClosure_ctf_equals_bc ℓ X
    (Profinite.padicIntegersRingObj ℓ E.val)
    (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.1
  change (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _) _
  rw [heq]
  exact hbc

end OpenImage

section ProperFormulas

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]

end ProperFormulas

end AlgebraicGeometry.ProEtale.CondensedRing
