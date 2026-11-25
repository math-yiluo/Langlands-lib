/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
import WeilConjectures.SixFunctors.FixProjectionCompactification.IdentityFactorCoefficientComparison

/-! # The coefficient compositor on identity-factor compactifications -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification

attribute [local implicit_reducible] sixFunctorFiniteSupport sixFunctorFiniteOpen
  sixFunctorFiniteRealization sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  sixFunctorFactorCompactification sixFunctorOpenCompactification
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  sfIntrinsicDerivedEquivalence sfIntrinsicCompactSupportComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local implicit_reducible] coherenceProEtaleFunctor coherenceBoundedSiteFunctor
  identityFactorPair
  refinementFiniteLevelFixedObject

private theorem identityFactor_witness_cancel
    {B T : Type*} [Category B] [Category T] (F G : B ⥤ T) (δ : F ≅ G)
    {L M : B} (e : L ≅ M) :
    F.map e.inv ≫ δ.hom.app L ≫ G.map e.hom = δ.hom.app M := by
  rw [← Category.assoc, δ.hom.naturality, Category.assoc, ← G.map_comp,
    e.inv_hom_id, G.map_id, Category.comp_id]

/-- The coefficient realization of the witnessed open/proper compositor cancels the
identity factors. This equation concerns only the canonical coefficient functors and
an etale-origin witness. It has no supplied finite operations, constructible input,
operation realization, or integral reduction.

Source: def-sf-operation-stages, composition and proper/open normalizations;
prop-sf-pf-coherence.proof.md, compatibility with counits and j_!.
(blueprint: lem-sf-finite-support-identity-factor-compositor).

Proof: expand sixFunctorFiniteCompositionComparison, retaining its two inverse
refinementFixedWitnessIso factors. By naturality of the three coefficient comparisons,
move those factors to the input and output. The middle coherenceProEtaleCompositor
is the etale compositor conjugated by the site comparison and the recorded changes
of compactification. For the identity-proper compactification of i followed by the
identity-open compactification of p, its etale proper/open construction is extension
by zero along i followed by proper image along p. The identity direct-image adjunction
and identity open-extension unit cancel, using the triangle identities. Transport
these cancellations through sfIntrinsicCompactSupportComparison: the first is exactly
sixFunctorOpenCandidateIso and the second is sixFunctorProperCandidateIso. Naturality
of the proper comparison orders the factors as displayed. The retained witness maps
then cancel against their inverses. The target compactification is the actual pair
(i,p), so no change-of-compactification map remains. This argument also applies to
the zero witness, the empty open, and identity i or p, by the same unit laws. -/
theorem finiteSupportIdentityFactorCompositor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Z Y : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    [QuasiCompact i.hom.left]
    (O : RefinementFiniteLevelOrigin C.l E n hn X.obj.left) :
    letI := hp
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := Padic.coefficientExtensionRing C.l E n
    let ci := sixFunctorOpenCompactification i hi
    let cp := Compactification.ofIsProper p.hom.left
    let c := sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl
    let M := refinementFiniteLevelFixedObject C.l E n hn X.obj.left O
    (sfIntrinsicCompactSupport cp A).map
        ((sfIntrinsicCompactSupportComparison A ci).hom.app M) ≫
      (sfIntrinsicCompactSupportComparison A cp).hom.app
        ((sfFixedCompactSupport A ci).obj M) ≫
      (sixFunctorFiniteRealization D C E n hn Y).functor.map
        (sixFunctorFiniteCompositionComparison C E n hn i p ci cp c O) =
    (sixFunctorProperCandidateIso A p.hom.left).hom.app
        ((sfIntrinsicCompactSupport ci A).obj
          ((sixFunctorFiniteRealization D C E n hn X).functor.obj M)) ≫
      (proEtaleConstantDerivedDirectImage p.hom.left A).map
        ((@sixFunctorOpenCandidateIso A _ _ X.obj.left Z.obj.left i.hom.left hi).hom.app
          ((sixFunctorFiniteRealization D C E n hn X).functor.obj M)) ≫
      (sfIntrinsicCompactSupportComparison A c).hom.app M := by
  let := hp
  let := hi
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let Λ := ULift.{u + 1} A
  let : TopologicalSpace Λ := ⊥
  let := discreteTopology_bot Λ
  let : IsNoetherian X.obj.left := by
    let := X.property.1
    let := X.property.2
    let := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
    let := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
    exact {}
  let : IsNoetherian Z.obj.left := by
    let := Z.property.1
    let := Z.property.2
    let := LocallyOfFiniteType.isLocallyNoetherian Z.obj.hom
    let := QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
    exact {}
  let : IsNoetherian Y.obj.left := by
    let := Y.property.1
    let := Y.property.2
    let := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
    let := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    exact {}
  let e := refinementFixedWitnessIso X.obj.left Λ O
  let δ := identityFactorFixedIso Λ i.hom.left p.hom.left
  have hgeom := identityFactorFixedCompositor Λ i.hom.left p.hom.left O.2.L
  have hgeom' : coherenceProEtaleCompositor Λ
      (sixFunctorOpenCompactification i hi) (Compactification.ofIsProper p.hom.left)
      (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) O.2.L =
      δ.hom.app ((coherenceBoundedSiteFunctor Λ X.obj.left).obj O.2.L) := hgeom
  have hcomp : sixFunctorFiniteCompositionComparison C E n hn i p
      (sixFunctorOpenCompactification i hi) (Compactification.ofIsProper p.hom.left)
      (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) O =
      δ.hom.app (refinementFiniteLevelFixedObject C.l E n hn X.obj.left O) := by
    change _ ≫ coherenceProEtaleCompositor Λ _ _ _ O.2.L ≫ _ = _
    rw [hgeom']
    exact identityFactor_witness_cancel _ _ δ e
  dsimp only
  rw [hcomp]
  exact identityFactorCoefficientComparison A i.hom.left p.hom.left _

end WeilConjectures.FixProjectionCompactification
