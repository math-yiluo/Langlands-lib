/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections

/-!
# Cohomology over w-contractible affine schemes and acyclicity for direct images

Let `Λ` be a ring. Sections over a weakly contractible object `W` of the small pro-étale site
form an exact functor on pro-étale sheaves of `Λ`-modules, so the higher derived sections over
`W` vanish
(`AlgebraicGeometry.ProEtale.isZero_rightDerived_sectionsFunctor_of_isWeaklyContractible`).
Through the comparison of pro-étale and étale cohomology, the higher étale cohomology of an
affine scheme with w-contractible ring of global sections vanishes
(`AlgebraicGeometry.ProEtale.isZero_rightDerived_etaleSectionsFunctor_of_isWContractibleRing`).

Since the objects of the pro-étale site of `V` whose underlying scheme is the spectrum of a
w-contractible ring cover the site and are weakly contractible, a pro-étale sheaf `G` on `U` is
acyclic for the direct image along `f : U ⟶ V` as soon as its higher derived sections over the
base changes `U ×_V W` of these objects vanish
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isWContractibleRing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Taking sections over a weakly contractible object is an exact functor on pro-étale sheaves
of `Λ`-modules. -/
lemma preservesHomology_sectionsFunctor_of_isWeaklyContractible {X : Scheme.{u}} {W : X.ProEt}
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    (sectionsFunctor (ModuleCat.{u + 1} Λ) W).PreservesHomology := by
  have : (sectionsFunctor (ModuleCat.{u + 1} Λ) W).PreservesEpimorphisms := ⟨fun φ _ ↦
    (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_isWeaklyContractible (R := Λ) hW φ)⟩
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The higher derived sections over a weakly contractible object of the pro-étale site vanish.
-/
lemma isZero_rightDerived_sectionsFunctor_of_isWeaklyContractible {X : Scheme.{u}} {W : X.ProEt}
    (hW : (ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ) W).rightDerived (q + 1)).obj F) := by
  have := preservesHomology_sectionsFunctor_of_isWeaklyContractible Λ hW
  have := (sectionsFunctor (ModuleCat.{u + 1} Λ) W).preservesFiniteColimits_of_preservesHomology
  exact Functor.isZero_rightDerived_obj_of_exact _ F q

/-- The higher étale cohomology of an affine scheme whose ring of global sections is
w-contractible vanishes: through the comparison `H^q(X_ét, F) ≅ H^q(X_proét, ν^* F)`, it is the
higher derived sections over the terminal object of `X_proét`, which is weakly contractible. -/
theorem isZero_rightDerived_etaleSectionsFunctor_of_isWContractibleRing (X : Scheme.{u})
    [IsAffine X] [IsWContractibleRing Γ(X, ⊤)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((Etale.sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived (q + 1)).obj F) :=
  (isZero_rightDerived_sectionsFunctor_of_isWeaklyContractible Λ
    (ProEt.isWeaklyContractible_of_iso.{u + 1}
      (W := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)) X.isoSpec) _ q).of_iso
    (rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ X F (q + 1)).symm

/-- A pro-étale sheaf `G` of `Λ`-modules on `U` is acyclic for the direct image along
`f : U ⟶ V` if its higher derived sections over `U ×_V W` vanish for every object `W` of the
pro-étale site of `V` whose underlying scheme is the spectrum of a w-contractible ring: these
objects are weakly contractible and cover the site, so they detect exactness. -/
theorem rightAcyclic_lowerStar_of_isWContractibleRing {U V : Scheme.{u}} (f : U ⟶ V)
    (G : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))
    (h : ∀ (W : V.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R], (W.left ≅ Spec R) →
      ∀ q : ℕ, IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ)
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj W)).rightDerived (q + 1)).obj G)) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightAcyclic G := by
  intro q
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine (GrothendieckTopology.exact_iff_of_forall_exists
    (fun W : V.ProEt ↦ ∃ R : CommRingCat.{u}, IsWContractibleRing R ∧ Nonempty (W.left ≅ Spec R))
    ProEt.exists_isWContractibleRing_cover
    (fun _ ⟨_, _, ⟨e⟩⟩ ↦ ProEt.isWeaklyContractible_of_iso e) _).2 fun W ⟨R', _, ⟨e⟩⟩ ↦ ?_
  have h' := (h W R' e q).of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

end AlgebraicGeometry.ProEtale
