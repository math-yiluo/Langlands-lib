/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralFiniteEtaleTraceLattice

/-!
# Integral lattices after finite stratification

Source: Weil conjectures blueprint, main-20261015, six-functors basics,
`lemma-lattices-after-finite-stratification`, statement and proof; Bhatt--Scholze, Section 6.8,
Proposition 6.8.4(6) and Lemma 6.8.13 (blueprint: lemma-lattices-after-finite-stratification).

The coefficients are the pulled condensed topological rings, and modules are internal
module objects. The lattice inclusion is monic, and its scalar-extension adjoint is an
isomorphism. Thus the rationalization isomorphism is induced by that very inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Lattice existence for a fixed coefficient inclusion. -/
private def HasCoefficientLattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X),
    LocallyFree (condensedRingObj A X) N ∧
    ∃ ι : N ⟶ (Mod.comap (coefficientMap a X)).obj P,
      Mono ι ∧ IsIso (((Mod.extendRestrictAdjunction
        (coefficientMap a X)).homEquiv N P).symm ι)

/-- Pullback of a scalar-extension comparison around a cartesian square. -/
private theorem latticePullbackComparison
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (X U Y : Scheme.{u}) (f : U ⟶ X) (j : Y ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L) :
    Nonempty ((Mod.extendScalars (coefficientMap a (Limits.pullback f j))).obj
        ((upperStar A (Limits.pullback.fst f j)).obj M) ≅
      (upperStar B (Limits.pullback.snd f j)).obj ((upperStar B j).obj L)) := by
  exact ⟨(pullIso a (Limits.pullback.fst f j)).app M ≪≫
    (upperStar B (Limits.pullback.fst f j)).mapIso e ≪≫
    (upperStarComp B (Limits.pullback.fst f j) f).symm.app L ≪≫
    eqToIso (congrArg (fun g ↦ (upperStar B g).obj L)
      (Limits.pullback.condition (f := f) (g := j))) ≪≫
    (upperStarComp B (Limits.pullback.snd f j) j).app L⟩

/-- Restrict an integral lattice to a finite base change. -/
private theorem finite_stratum_lattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (descend : ∀ (Y V : Scheme.{u}) (q : V ⟶ Y) [IsFinite q] [Etale q] [Surjective q]
      (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)),
      LocallyFree (condensedRingObj B Y) P →
      ∀ N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj A V),
      LocallyFree (condensedRingObj A V) N →
      Nonempty ((Mod.extendScalars (coefficientMap a V)).obj N ≅ (upperStar B q).obj P) →
      HasCoefficientLattice A B a Y P)
    (X U Y : Scheme.{u}) (f : U ⟶ X) [Surjective f]
    (j : Y ⟶ X) [IsFinite (Limits.pullback.snd f j)] [Etale (Limits.pullback.snd f j)]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hL : LocallyFree (condensedRingObj B X) L)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U))
    (hM : LocallyFree (condensedRingObj A U) M)
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L) :
    HasCoefficientLattice A B a Y ((upperStar B j).obj L) := by
  exact descend Y (Limits.pullback f j) (Limits.pullback.snd f j) ((upperStar B j).obj L)
    (locallyFree_upperStar B j hL) ((upperStar A (Limits.pullback.fst f j)).obj M)
    (locallyFree_upperStar A (Limits.pullback.fst f j) hM)
    (latticePullbackComparison A B a X U Y f j L M e)

/-- Transfer a property of a finite base change to a finite stratification. -/
private theorem stratify_etale_cover_property
    (X U : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (f : U ⟶ X) [Etale f]
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ : ∀ (Y : Scheme.{u}) (j : Y ⟶ X),
      IsFinite (Limits.pullback.snd f j) → Etale (Limits.pullback.snd f j) → Q Y j) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i, Q (S.domain i) (S.immersion i) := by
  obtain ⟨S, _, hS⟩ := Scheme.exists_etale_stratified_finite f
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨T, fun i ↦ hQ (S.domain i) (S.immersion i) (hS i).1 (hS i).2⟩

/-- Assemble coefficient lattices from an etale cover and finite-cover descent. -/
private theorem coefficient_stratified_lattice
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (a : A ⟶ B) [IsMonHom a]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (hL : LocallyFree (condensedRingObj B X) L)
    (hlocal : ∃ (U : Scheme.{u}) (f : U ⟶ X), Etale f ∧ Surjective f ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj A U),
      LocallyFree (condensedRingObj A U) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar B f).obj L))
    (descend : ∀ (Y V : Scheme.{u}) (q : V ⟶ Y) [IsFinite q] [Etale q] [Surjective q]
      (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj B Y)),
      LocallyFree (condensedRingObj B Y) P →
      ∀ N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj A V),
      LocallyFree (condensedRingObj A V) N →
      Nonempty ((Mod.extendScalars (coefficientMap a V)).obj N ≅ (upperStar B q).obj P) →
      HasCoefficientLattice A B a Y P) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X, ∀ i,
      HasCoefficientLattice A B a (S.domain i) ((upperStar B (S.immersion i)).obj L) := by
  obtain ⟨U, f, hf, hs, hc, hq, M, hM, ⟨e⟩⟩ := hlocal
  have := hf
  have := hs
  have := hc
  have := hq
  apply stratify_etale_cover_property X U f
    (fun Y j ↦ HasCoefficientLattice A B a Y ((upperStar B j).obj L))
  intro Y j hf hj
  have := hf
  have := hj
  exact finite_stratum_lattice A B a descend X U Y f j L hL M hM e

/-- A lisse rational module on a standing scheme has a lisse integral lattice on each
stratum of some finite locally closed stratification. Finite ranks may vary, including
rank zero. The coefficient topology is the canonical spectral norm topology; the integral
ring has the subspace topology. Scalar extension along its inclusion is inversion of `l`.
No uniformizer enters this conclusion; any chosen uniformizer in the coefficient datum
is allowed. The nodal-curve example in the source explains why stratification is necessary.

Source: blueprint main-20261015, `lemma-lattices-after-finite-stratification`, and its proof
paragraphs "Sheaf of lattices", stratification, and "Pushing down by the trace";
Bhatt--Scholze, Section 6.8 (blueprint: lemma-lattices-after-finite-stratification).

Proof. The structure map makes X Noetherian. Apply the etale-local lattice theorem,
then stratify its qcqs etale cover so that its restrictions are finite etale.
Pull back the lattice and its scalar-extension isomorphism using the coefficient
pullback comparison and the base-change square. Local freeness survives pullback.
On each stratum the normalized finite-etale trace has locally free integral image:
its split-chart formula is summation of the sheet lattices, which become constant
on a common refinement, and the continuous finite-sum lattice theorem computes
this image. Exact scalar extension makes the image inclusion monic and epic,
so its actual adjoint is invertible. Finally continuousIntegers_eq identifies
the norm-at-most-one subring with the recorded valuation ring. No degree is divided
out, and the covers and images include empty schemes and rank zero.
-/
theorem exists_stratified_lisse_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hpl : p ≠ l)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
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
  dsimp only
  intro L hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hlocal := spectralLisse_etale_lattice l E X L hL
  apply coefficient_stratified_lattice _ _ _ X L hL hlocal
  intro Y V q _ _ _ P hP N hN he
  obtain ⟨e⟩ := he
  exact spectralFiniteEtaleTrace_lattice l E Y P hP q N hN e

end AlgebraicGeometry.ProEtale.CondensedRing
