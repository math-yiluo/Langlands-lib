/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarRestrictions
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalFiniteQuotientLeftComparison
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalFiniteScalarLeftComparison
import WeilConjectures.SmoothPurity.Completed.CompletedQuotientProperMate
import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteFreeRestrictionDirectImageMate

/-! # Invertibility of the canonical left scalar comparison

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-integral-left-comparison-invertible)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem comparison_iso_transport {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (q : F ⟶ G) {A B : C} (e : A ≅ B) [IsIso (q.app A)] :
    IsIso (q.app B) := by
  exact IsIso.of_isIso_fac_left (q.naturality e.hom)

private theorem completedComparison_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier)
    (K : DerivedCategory (scalarReductionSource l E.carrier X)) :
    IsIso ((PurCompactSupport.comparison
      (PurCompactSupport.completedChange l E.carrier L.carrier i) c).app K) := by
  have hproper : IsIso (PurCompactSupport.properComparison
      (PurCompactSupport.completedChange l E.carrier L.carrier i) c.g) := by
    unfold PurCompactSupport.properComparison
    exact PurCompactSupport.finiteFreeRestrictionDirectImageMate_isIso
      (PurCompactSupport.completedChange l E.carrier L.carrier i) c.g
      (completedScalarRelativeDegree l E.carrier L.carrier i)
      (finiteFreeCompletedScalarComparison l E.carrier L.carrier i Y).1
  have hopen := PurCompactSupport.openComparison_isIso
    (PurCompactSupport.completedChange l E.carrier L.carrier i) c.i K
  rw [PurCompactSupport.comparison_factorization]
  infer_instance

private theorem reductionComparison_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (E : FieldStage.{u} l) (n : ℕ+)
    (K : DerivedCategory (scalarReductionSource l E.carrier X)) :
    IsIso ((PurCompactSupport.comparison
      (PurCompactSupport.reduction l E.carrier n n.pos) c).app K) := by
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n =>
    change IsIso ((PurCompactSupport.comparison
      (PurCompactSupport.reduction l E.carrier (n + 1) hn) c).app K)
    have hp := completedQuotientProperMate l E.carrier c.g n
      (PurCompactSupport.reduction l E.carrier (n + 1) hn) (fun _ ↦ rfl)
      ((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E.carrier) c.i).mapDerivedCategory.obj K)
    have hproper : IsIso ((PurCompactSupport.properComparison
        (PurCompactSupport.reduction l E.carrier (n + 1) hn) c.g).app
        ((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E.carrier) c.i).mapDerivedCategory.obj K)) := by
      simpa only [PurCompactSupport.properComparison, PurCompactSupport.finiteProperComparison]
        using hp
    have hopen := PurCompactSupport.openComparison_isIso
      (PurCompactSupport.reduction l E.carrier (n + 1) hn) c.i K
    rw [PurCompactSupport.comparison_factorization]
    apply IsIso.comp_isIso' hproper
    infer_instance

/-- The specified ambient proper/open scalar comparison is invertible on the
constructible finite-Tor domain for every allowed actual coefficient change.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.

Proof: finite quotient and ramified generators use the finite coefficient scalar
comparison, obtained on bounded-below etale models and transported to the pro-etale
site through the counit-normalized proper and open comparisons. For integral reduction,
use the quotient projection formula on the complete finite-Tor input; the proper
factor and the open tensor factor are invertible. For completed integral extension,
the finite-free completed coefficient sheaf makes the proper restriction mate a finite
biproduct comparison, and open extension commutes with coefficient extension. This
argument needs only separatedness of f, not absolute separatedness of X or Y.
Identity changes use the normalized tensor unitor. For a composite, the ambient
coefficient-comparison composition law conjugates the composite of the two generator
isomorphisms by tensor associators. The scalar-preservation argument ensures that the
second comparison is evaluated on its finite-Tor domain. Invertibility is preserved
under composition and conjugation. No exceptional right mate occurs in this proof.
(blueprint: lem-sf-integral-left-comparison-invertible). -/
theorem integralLeftComparison_isIso
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : Allowed l a) :
    IsIso (whiskerLeft (RingStage.inclusion.{u} l Ω X s)
      (PurCompactSupport.comparison a c)) := by
  classical
  obtain ⟨sc⟩ := scalarRestrictions_exists l Ω D hl X
  have pointwise {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) : ∀ K : C.{u} l Ω X (s.stage l),
        IsIso ((PurCompactSupport.comparison a c).app
          ((RingStage.inclusion.{u} l Ω X s).obj K)) := by
    induction ha with
    | quotient E m n h =>
      intro K
      exact finiteQuotientLeftComparison_isIso l Ω D hl c E m n h K
    | ramified E L i e he n =>
      intro K
      apply finiteScalarLeftComparison_isIso l Ω D hl c E L n
        ⟨e * n, Nat.mul_pos e.pos n.pos⟩
        (PurCompactSupport.ramifiedMap l E.carrier L.carrier i e he n) _ _ K
      intro T
      rfl
    | reduction E n =>
      intro K
      exact reductionComparison_isIso l c E n K.obj
    | integral E L i =>
      intro K
      exact completedComparison_isIso l c E L i K.obj
    | identity s a h =>
      intro K
      exact IsIso.of_isIso_fac_right
        (PurCompactSupport.comparison_identity a h c ((RingStage.inclusion l Ω X s).obj K))
    | @comp s t r a b d h ha hb iha ihb =>
      intro K
      have hca := iha K
      let S := sc.scalar a ha
      have hcb : IsIso ((PurCompactSupport.comparison b c).app
          ((S.functor ⋙ RingStage.inclusion l Ω X t).obj K)) := ihb (S.functor.obj K)
      have hcb' : IsIso ((PurCompactSupport.comparison b c).app
          ((pbcDerivedExtend (a.map X)).obj
            ((RingStage.inclusion l Ω X s).obj K))) :=
        comparison_iso_transport (PurCompactSupport.comparison b c) (S.realization.app K)
      have hc := PurCompactSupport.comparison_composition a b d h c
        ((RingStage.inclusion.{u} l Ω X s).obj K)
      have hfirst : IsIso ((pbcDerivedExtend (b.map Y)).map
          ((PurCompactSupport.comparison a c).app
            ((RingStage.inclusion l Ω X s).obj K))) := inferInstance
      have hpair := IsIso.comp_isIso' hfirst hcb'
      have hlast : IsIso ((PurCompactSupport.image (r.coefficients l) c).map
          ((PurCompactSupport.tensorComposition (a.map X) (b.map X) (d.map X) (h X)).hom.app
            ((RingStage.inclusion l Ω X s).obj K))) := inferInstance
      have hall := IsIso.comp_isIso' hpair hlast
      exact IsIso.of_isIso_fac_left hc.symm
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (pointwise a ha)

end WeilConjectures.ExceptionalIntegralScalar
