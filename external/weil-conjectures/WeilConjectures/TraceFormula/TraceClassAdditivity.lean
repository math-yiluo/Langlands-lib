/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurvePieces
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Trace classes with another coefficient on the same support

This file defines the correspondence with the support of a correspondence `c` and another
coefficient object and map, its trace class on the fixed locus of `c`, and the graph
correspondences `(𝟙, Φ_m)` with the curve pieces `K^Z = Rx_* Lx^* K` and `K^U = j_! Lj^* K` of a
Weil object and their coefficient maps `u^Z`, `u^U` (blueprint
`proposition-frobenius-local-term-curve--1`). The additivity
`Tr_{c_m}(φ_m) = Tr_{c_m}(u^Z) + Tr_{c_m}(u^U)` of blueprint
`proposition-additivity-trace-classes--2`, item 2, is
`ProEtale.CondensedRing.WeilBoundedConstructible.traceClass_graph_eq_add` in
`WeilConjectures.TraceFormula.CurvePiecesAdditivity`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.withCoeff`: the correspondence with the same support and
  another coefficient object and map.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace BorelMooreSection

variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

/-- The restriction of Borel–Moore sections along an open immersion is additive. -/
lemma restrict_add (j : U ⟶ X) [IsOpenImmersion j.left] (α β : BorelMooreSection ℓ X) :
    (α + β).restrict j = α.restrict j + β.restrict j := by
  have := Functor.additive_of_iso (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).symm
  simp only [restrict, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [LocallyOfFiniteType U.hom] [IsSeparated U.hom] in
/-- Local terms are additive (blueprint `theorem-proper-pushforward-lefschetz-verdier--3`). -/
lemma localTerm_add (j : U ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    [IsProper U.hom] (α β : BorelMooreSection ℓ X) :
    (α + β).localTerm j = α.localTerm j + β.localTerm j := by
  rw [localTerm, localTerm, localTerm, restrict_add, integral_add]

end BorelMooreSection

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The correspondence with the support `(c₁, c₂)` of `c` and another coefficient object `K'`
and coefficient map `u' : Lc₂^* K' ⟶ Rc₁^! K'` (blueprint `definition-correspondence--2`). -/
noncomputable def withCoeff (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K') :
    Correspondence ℓ K' where
  C := c.C
  c₁ := c.c₁
  c₂ := c.c₂
  u := u'

variable {c}

/-- A fixed locus of `c` is a fixed locus of every correspondence with the same support. -/
noncomputable def FixedLocus.withCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K') :
    (c.withCoeff K' u').FixedLocus where
  F := F.F
  ι := F.ι
  w := F.w
  isLimit := F.isLimit

/-- The trace class of the correspondence with the support of `c` and the coefficient map `u'`,
as a Borel–Moore section of the fixed locus `F` of `c`. -/
noncomputable def FixedLocus.traceClassWithCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K') :
    BorelMooreSection ℓ F.F :=
  (c.withCoeff K' u').traceClass (F.withCoeff K' u')

end Correspondence

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) {U : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
  [IsOpenImmersion j.left]

/-- The graph correspondence `(𝟙, Φ_m)` with the closed curve piece `K^Z = Rx_* Lx^* K` and its
coefficient map `u^Z` (blueprint `proposition-frobenius-local-term-curve--1`). -/
noncomputable abbrev closedPieceGraph (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : Correspondence ℓ (K.closedPiece x) :=
  (K.graph m).withCoeff (K.closedPiece x) (K.closedPieceCoeff m x hx)

/-- The graph correspondence `(𝟙, Φ_m)` with the open curve piece `K^U = j_! Lj^* K` and its
coefficient map `u^U` (blueprint `proposition-frobenius-local-term-curve--1`). -/
noncomputable abbrev openPieceGraph (m : ℕ) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m)) : Correspondence ℓ (K.openPiece j) :=
  (K.graph m).withCoeff (K.openPiece j)
    (K.openPieceCoeff j m sq ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app _)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
