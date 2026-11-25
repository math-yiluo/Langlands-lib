/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.Algebra.Homology.FreeComplexResidueTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-!
# Perfectness detected by uniformly bounded maximal residue fibres

Source: Stacks Project, More on Algebra, Tag 068V, lemma-check-perfect-pointwise,
implication (3) to (1) (auxiliary; not a blueprint node).

The derived tensor is the existing monoidal structure on the module derived category.
For a maximal ideal, its quotient ring is regarded as an R-module in degree zero.
Vanishing of the underlying R-module cohomology is equivalent to vanishing of the
residue-field cohomology of derived scalar extension.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- A pseudo-coherent complex with maximal residue fibres concentrated in the fixed interval
is perfect, and its derived tensor with every module has cohomology in that same interval.

Source: Stacks Project, Tag 068V, implication (3) to (1).
Proof:
1. Choose a bounded-above finite-free model P supplied by pseudo-coherence. Its free
   terms are flat, so the proved bounded-above flat-complex criterion makes it K-flat.
   QObjTensorSingleFunctorObjIso identifies each derived module tensor with ordinary
   termwise tensor, compatibly with the chosen isomorphism Q(P) ≅ C.
2. For every degree outside [a,b], apply the single-degree finite-free residue criterion
   isZero_homology_tensor_of_residue. It uses degree cancellation on a principal
   neighborhood of each maximal ideal. Tensor preserves its homotopy equivalences,
   so all module tensors are exact locally in that degree; exactness descends along
   the principal cover. Transfer the result through the K-flat homology comparisons.
3. These vanishing statements give torAmplitudeIn R a b C using isGE_iff and isLE_iff.
   Apply isPerfect_of_pseudoCoherent_finiteTorAmplitude, which is already proved by
   good truncation with a finite projective bottom cokernel. Its bounded finite
   projective model witnesses IsPerfect C; the vanishing assertion is step 2.
(auxiliary; not a blueprint node) -/
theorem isPerfect_and_tensor_homology_vanish_of_maximal_fibres
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (hC : C.IsPseudoCoherent)
    (a b : ℤ) (hab : a ≤ b)
    (hfibres : ∀ (m : Ideal R), m.IsMaximal → ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ m))))) :
    C.IsPerfect ∧ ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  obtain ⟨P, c, hPc, hP, ⟨e⟩⟩ := hC
  have : P.IsStrictlyLE c := hPc
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P c fun j ↦ by
    have := (hP j).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  let eH (M : ModuleCat.{u} R) (i : ℤ) :
      (homologyFunctor (ModuleCat.{u} R) i).obj
          (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i :=
    (homologyFunctor (ModuleCat.{u} R) i).mapIso
      (whiskerRightIso e.symm _ ≪≫ QObjTensorSingleFunctorObjIso P hPk M) ≪≫
      (homologyFunctorFactors _ i).app _
  have htensor (M : ModuleCat.{u} R) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
    apply IsZero.of_iso _ (eH M i)
    apply CochainComplex.isZero_homology_tensor_of_residue P
      (fun j ↦ (hP j).1) (fun j ↦ (hP j).2) i
    intro m hm
    exact (hfibres m hm i hi).of_iso (eH (ModuleCat.of R (R ⧸ m)) i).symm
  have hTor : torAmplitudeIn (ModuleCat.{u} R) a b C := by
    intro M
    constructor
    · change (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M).IsGE a
      rw [isGE_iff]
      exact fun i hi ↦ htensor M i (Or.inl hi)
    · change (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M).IsLE b
      rw [isLE_iff]
      exact fun i hi ↦ htensor M i (Or.inr hi)
  obtain ⟨T, ⟨l, r, hT⟩, hfin, hproj, ⟨eT⟩⟩ :=
    isPerfect_of_pseudoCoherent_finiteTorAmplitude C
      ⟨P, c, hPc, hP, ⟨e⟩⟩ ⟨a, b, hab, hTor⟩
  refine ⟨⟨T, l, r, ?_, ?_, fun i ↦ ⟨hproj i, hfin i⟩, ⟨eT.symm⟩⟩, htensor⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hT i (Or.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hT i (Or.inr hi)

end DerivedCategory
