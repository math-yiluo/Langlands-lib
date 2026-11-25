/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionAlgebraic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolutionContinuous

/-! # The finite integral coefficient point resolution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A finite discrete integral algebra has a two-term finite free point resolution.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.proof.md, paragraph "Finite free and finitely presented
coefficient extensions", the displayed sequence for O_E to A.
(blueprint: lem-s3-integral-finite-point-resolution).

Proof: take the continuous ring homomorphism phi specified by ha. Regard A as an O_E-module
via phi. It is finite, hence finitely generated. Choose a surjection O_E^r onto A, for
example by enumerating the elements of A. Its kernel is a finitely generated submodule
of a finite free module over the DVR O_E, hence finite free. The ell-power annihilator
is nonzero in O_E and annihilates A. Multiplication by it injects O_E^r into the kernel,
which also injects into O_E^r. Finite-free rank inequalities force equal rank r. Choose its
basis and obtain an injective square matrix T and a short exact module sequence
0 -> O_E^r -> O_E^r -> A -> 0, with the last map using the specified phi-action.
Equip the two free modules with their product valuation topologies. The last map is
continuous because phi is continuous and sums and multiplication are continuous. Its
kernel is open and closed. The matrix T is a homeomorphism onto its image because
O_E^r is compact and the ambient O_E^r is Hausdorff. Its inverse on the image is continuous.
Apply continuous functions from an arbitrary profinite set. Injectivity follows
pointwise; a continuous function into the kernel lifts continuously using this inverse.
A continuous function into finite discrete A lifts by choosing one preimage per value
and composing with that locally constant function, or by its finite clopen fibres.
Thus these sequences are sectionwise short exact. Continuous pointwise scalar action
makes all maps morphisms of condensed O_E-modules. The sectionwise short-exactness
criterion gives the condensed short complex P. Product/coproduct comparison identifies
the first two terms with the rank-r finite biproducts of the regular module. The equation
in ha identifies its last term with the regular A-module restricted along a.hom.hom,
giving t. The zero ring is included: take rank zero and the zero complex. No object is
defined by selecting this existence theorem; its witnesses are used only in proofs. -/
theorem integralFinitePointResolution
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩)
    (ha : IsIntegralFiniteScalarMap ell E A a) :
    ∃ (P : ShortComplex (IntegralFiniteScalar.PointModules
        (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}))) (r : ℕ),
      P.ShortExact ∧
      Nonempty (P.X₁ ≅ biproduct
        (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
      Nonempty (P.X₂ ≅ biproduct
        (fun _ : Fin r ↦ Mod.regular (Profinite.padicIntegersRingObj ell E.1))) ∧
      Nonempty (P.X₃ ≅ (Mod.comap a.hom.hom).obj
      (Mod.regular (cartesianFinitePointRing A))) := by
      letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
      letI : TopologicalSpace A := ⊥
      letI : DiscreteTopology A := discreteTopology_bot A
      letI : IsTopologicalRing A := inferInstance
      obtain ⟨φ, hφ, hsection⟩ := ha
      letI : Module (PadicAlgCl.integers ell E.1) A := Module.compHom A φ
      obtain ⟨r, f, g, hf, hfg, hg⟩ :=
        integralFinitePointResolution_algebraic ell E A hA φ
      obtain ⟨P, hP⟩ :=
        integralFinitePointResolution_continuous ell E A a φ hφ hsection r f g hf hfg hg
      exact ⟨P, r, hP⟩

end AlgebraicGeometry.ProEtale.CondensedRing
