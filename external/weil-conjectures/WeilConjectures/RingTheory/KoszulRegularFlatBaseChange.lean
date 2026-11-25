/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Flat base change of Koszul regularity

Source: Stacks Project, More on Algebra, Lemma 15.31.5 (Tag 062H),
flat base change of Koszul regular sequences.
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- Flat base change preserves Koszul regularity.
Source: Stacks Project, More on Algebra, Lemma 15.31.5 (Tag 062H), flat base change
of the Koszul complex (blueprint: lem-sc-koszul-regular-flat-base-change).

Proof: Identify the Koszul complex on the images of the generators with the
base change of the original complex: in degree n, send a scalar times a basis
wedge to the same scalar times the wedge of the image basis vectors. The inverse
uses the same finite exterior bases. Evaluation of the contraction differential
on those wedges proves that these maps commute with the differentials. Flat
tensoring preserves kernels and images of the short complexes in each degree,
hence identifies homology with the tensor product of the original homology.
For every positive degree the latter is zero by hreg. Transport that vanishing
across the degreewise complex isomorphism. This also covers the empty sequence
and the zero ring, and imposes no proper-ideal hypothesis. -/
theorem isKoszulRegular_of_flat
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] [Module.Flat A S]
    (r : ℕ) (f : Fin r → A) (hreg : IsKoszulRegular f) :
    IsKoszulRegular (algebraMap A S ∘ f) := by
  let F := ModuleCat.extendScalars (algebraMap A S)
  let : CategoryTheory.Limits.PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      ((RingHom.flat_algebraMap_iff (R := A) (S := S)).mpr inferInstance)
  obtain ⟨e⟩ := ExteriorAlgebra.nonempty_koszulBaseChangeIso A S r f
  intro i hi
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_iso (e := e)
  have h := ((ExteriorAlgebra.koszulComplex A r f).exactAt_iff_isZero_homology i).mpr
    (hreg i hi)
  exact h.map F

end RingTheory.Sequence
