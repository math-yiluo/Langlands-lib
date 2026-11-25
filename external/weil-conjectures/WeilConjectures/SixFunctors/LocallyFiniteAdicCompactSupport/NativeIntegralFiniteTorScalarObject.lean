/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # The finite-Tor integral representative of a scalar transition -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- Integral scalar extension has its prescribed finite-Tor representative.
Source: Bhatt--Scholze, Proposition 6.8.14, and the integral residue-Tor criterion.
Proof: the coefficient prime is a unit on X because X is over the finite field of
characteristic distinct from l. Its image in every residue field is invertible.
The integral transition already preserves constructibility. The integral residue-Tor
criterion therefore gives finite Tor amplitude to its underlying integral object.
Equip that same object with this proof. Its inclusion is the given transition object
by equality of full-subcategory objects; in particular, this equation determines the
representative up to equality, rather than selecting arbitrary existence data.
(blueprint: lem-sf-native-integral-finite-tor-scalar-object). -/
theorem finiteTorScalarObject
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X) :
    ∃ KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X,
      (PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj KE =
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        i E h).obj ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) i) X).obj K) ∧
      KE.obj = (integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
        (Coefficient.{u} l (PadicAlgCl l) E)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) i E h) X).obj
          K.obj := by
  classical
  let primeUnit : IsUnit (l : Γ(X, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using
      (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        ((primeUnit.map (X.presheaf.germ ⊤ x trivial).hom).map
          (X.residue x).hom)).invertible
  let Ke := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
    i E h).obj ((PurCompactSupport.finiteTorIntegralInclusion l
      (Coefficient.{u} l (PadicAlgCl l) i) X).obj K)
  refine ⟨⟨Ke.obj, ?_⟩, rfl, rfl⟩
  rw [← (integral_residue_tor D l hl (Coefficient.{u} l (PadicAlgCl l) E) X).2]
  exact Ke.property

end WeilConjectures.LocallyFiniteAdicCompactSupport
