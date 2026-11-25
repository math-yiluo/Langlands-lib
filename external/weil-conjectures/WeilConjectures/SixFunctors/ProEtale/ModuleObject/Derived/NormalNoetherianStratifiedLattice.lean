/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalStratifiedLatticeData

/-! # Integral lattices on finite strata of normal Noetherian schemes.

Source: blueprint `lemma-lattices-after-finite-stratification`, extended as directed by
Wei Yang, Zulip #1412, answer 17 (2026-11-01), for clause (4) of
`proposition-lattices-representations-normal-scheme`. This keeps the original finite-type theorem
and supplies the normal-Noetherian instance required by its dense-open argument.
(blueprint: lemma-lattices-after-finite-stratification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A lisse rational module on a normal Noetherian scheme admits an embedded
lisse integral lattice on each stratum of a finite locally closed stratification.
There is no base field, characteristic restriction, separatedness assumption,
connectedness assumption, or assumption that `l` is invertible on the scheme.

Source: blueprint `lemma-lattices-after-finite-stratification`, sheaf of lattices and trace proof;
Wei Yang #1412, answer 17, normal-Noetherian extension; Stacks 07RY and 07RZ.

Proof. The scheme has Noetherian underlying space and is qcqs. Split into the
finitely many locally constant rank pieces. The qcqs lattice-scheme theorem
represents lattices by a separated surjective etale scheme with its universal
lattice. Choose finitely many affine opens with images covering the base; their
disjoint union is a qcqs separated etale surjection. Stacks 07RY and 07RZ give a
finite locally closed stratification on which this cover is finite etale. Pull
back the universal lattice and its scalar-extension comparison to each cover.
The image under the sheet-sum trace is a locally free integral lattice on the
stratum: on splitting charts it is a finite sum of lattices. Exact scalar
extension and naturality of the localization counit show that the adjoint of
this actual inclusion is an isomorphism. These are precisely the atlas,
stratification and trace steps of exists_topologicalStratifiedLatticeData,
with the spectral norm and its valuation subring. No cover degree is inverted.
Normality is retained here for the expert-requested specialization, although
the construction itself only needs a Noetherian underlying space. Empty schemes,
zero rank, varying ranks, and residue characteristic `l` are included.
(blueprint: lemma-lattices-after-finite-stratification).
-/
theorem exists_stratified_lisse_integral_lattice_of_normal
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (_hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)
    let B := Profinite.continuousMapRingObj.{u} E
    let a : A ⟶ B :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X),
      LocallyFree (condensedRingObj B X) L →
      ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
        let T := S.domain i
        let aT := (upperStarFromPoint T).map a
        let LT := (CondensedRing.upperStar B (S.immersion i)).obj L
        ∃ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T),
          LocallyFree (condensedRingObj A T) M ∧
          ∃ ι : M ⟶ (Mod.comap aT).obj LT,
            Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
