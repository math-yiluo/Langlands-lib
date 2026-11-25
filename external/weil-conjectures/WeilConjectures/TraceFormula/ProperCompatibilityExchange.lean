/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateComp
public import WeilConjectures.TraceFormula.ProperPushforwardKernel

/-!

# Exchange lemmas for the proper pushforward of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` (blueprint
`definition-pushforward-correspondence--1`), with `q = f × f`:

* the kernel class of `[f, g]_! u` is the transported kernel class of `u` (blueprint
  `theorem-proper-pushforward-lefschetz-verdier--1`; proved in
  `WeilConjectures.TraceFormula.SourceExchange`);
* the evaluation kernels are exchanged by the kernel pushforward (blueprint
  `theorem-proper-pushforward-lefschetz-verdier--1`, (1); proved in
  `WeilConjectures.TraceFormula.ProperCompatibilityEvaluation`);
* the support isomorphisms are exchanged by the exchange map of the support square (blueprint
  `theorem-proper-pushforward-lefschetz-verdier--1`, (2); proved in
  `WeilConjectures.TraceFormula.ProperCompatibilitySupport`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

section Transport

variable {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
  [IsSeparated A.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- `Rp_*` and `Rq_*` agree on morphisms for `p = q`, through the casts. -/
lemma lowerStar_map_comp_eqToHom_of_eq {p q : A ⟶ B} (h : p = q)
    {a b : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : a ⟶ b) :
    (boundedConstructibleLowerStar ℓ p).map x ≫ eqToHom (congrArg (fun r : A ⟶ B ↦
      (boundedConstructibleLowerStar ℓ r).obj b) h) =
      eqToHom (congrArg (fun r : A ⟶ B ↦
        (boundedConstructibleLowerStar ℓ r).obj a) h) ≫
        (boundedConstructibleLowerStar ℓ q).map x := by
  subst h
  simp

/-- The points `𝟙 ⟶ Rp_* 𝟙` of `p = q` agree through the cast. -/
lemma unit_comp_map_εIso_inv_comp_eqToHom_of_eq {p q : A ⟶ B} (h : p = q) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ p).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ p).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ p)).inv) ≫
      eqToHom (congrArg (fun r : A ⟶ B ↦
        (boundedConstructibleLowerStar ℓ r).obj (𝟙_ _)) h) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ q).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ q).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ q)).inv := by
  subst h
  simp

end Transport

namespace Correspondence

/-- The trace morphism followed by the support isomorphism is the exceptional adjoint of the
kernel class followed by the evaluation kernel (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 1). -/
lemma mate_comp_traceMap_comp_supportIso (c : Correspondence ℓ K) (F : c.FixedLocus) :
    c.mate ≫ c.traceMap F ≫ F.supportIso.hom =
      (boundedConstructibleUpperShriekAdjunction ℓ c.support).homEquiv _ _
        (c.kernelClass ≫ evaluationKernel ℓ K) := by
  rw [traceMap_eq, Adjunction.homEquiv_naturality_right, kernelClass,
    Equiv.apply_symm_apply]
  simp

end Correspondence

namespace Correspondence.ProperPushforwardDiagram


variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

/-- The support square `g ≫ b = c ≫ (f × f)` of a proper pushforward diagram. -/
lemma g_comp_support : P.g ≫ P.pushforward.support = c.support ≫ prod.map P.f P.f := by
  apply prod.hom_ext <;> simp [Correspondence.support, P.w₁, P.w₂]

omit [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The diagonal square `Δ_X ≫ (f × f) = f ≫ Δ_Y`. -/
lemma diag_comp_prodMap : diag X ≫ prod.map P.f P.f = P.f ≫ diag Y := by
  apply prod.hom_ext <;> simp


end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
