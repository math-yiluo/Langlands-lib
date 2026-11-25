/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation

/-!
# Smoothness of the symmetric algebra of a finite projective module

Source: Stacks Project, More on Algebra, Lemma Tag 07M6, the finite-projective-to-smooth
implication (blueprint: lem-weil-pbc-symmetric-algebra-finite-projective-smooth).
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

/-- The symmetric algebra of a finite projective module is smooth over its base ring.
Source: Stacks Project, More on Algebra, Lemma Tag 07M6.
(blueprint: lem-weil-pbc-symmetric-algebra-finite-projective-smooth)

Proof, step 1: choose a finite standard free cover for `M`
(`lem-weil-pbc-finite-projective-standard-free-cover`). The images of its covering elements
in the symmetric algebra still generate the unit ideal.
Step 2: localization of the symmetric algebra at each covering element is the symmetric
algebra of the localized module, by `lem-weil-pbc-localization-tensor` and
`lem-weil-pbc-symmetric-algebra-base-change`.
Step 3: transport the localized free-module isomorphism using the universal property
(`lem-weil-pbc-symmetric-algebra-universal-property`). Then
`lem-weil-pbc-symmetric-algebra-free-module-polynomial` identifies that algebra with a
polynomial algebra over the localized base.
Step 4: polynomial algebras are smooth (`lem-weil-pbc-polynomial-ring-smooth`), principal
localizations preserve smoothness (`lem-weil-pbc-smooth-ring-map-principal-localization`),
and smooth maps compose (`lem-weil-pbc-smooth-ring-map-base-change-composition`). Thus each
localized symmetric algebra is smooth over the original base, using invariance under
algebra isomorphisms in `def-weil-pbc-smooth-ring-map`.
Step 5: smoothness is local on the resulting standard cover of the symmetric algebra
(`lem-weil-pbc-smooth-ring-map-local-on-cover`), so the structure map is smooth. -/
theorem smooth_of_finite_projective (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : Algebra.Smooth A (SymmetricAlgebra A M) := by
  -- Use infinitesimal lifting instead of the standard-cover plan above.
  have hfp : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  have hfin : Algebra.FinitePresentation A (SymmetricAlgebra A M) :=
    ((generators_and_finitePresentation A M).2 hfp).1
  refine ⟨?_, hfin⟩
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I _ f
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (Ideal.Quotient.mkₐ A I).toLinearMap (f.toLinearMap.comp (ι A M))
    Ideal.Quotient.mk_surjective
  refine ⟨lift g, ?_⟩
  apply algHom_ext
  ext m
  simpa using LinearMap.congr_fun hg m

end SymmetricAlgebra
