/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.RingTheory.PopescuCorrectionReduction
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth

/-! Finite-presentation factorization used by the reduced Popescu factor. -/
@[expose] public section
universe u v w
open CategoryTheory
namespace Algebra

/-- Factor through a stage of the given standard smooth diagram.
The proof adapts the ring-colimit argument of
`Algebra.exists_smooth_factorization_of_ind_smooth` to retain standard smoothness,
using a small polynomial quotient of the source to handle all source universes.
Source: Stacks Project, Tags 00QO and 07C3. -/
private theorem exists_standard_factor
    {R : Type u} {A : Type w} {L : Type (max u v)}
    [CommRing R] [CommRing A] [CommRing L] [Algebra R A] [Algebra R L]
    [FinitePresentation R A] (f : A →ₐ[R] L)
    (hind : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R ↦ IsStandardSmooth R B) (CommAlgCat.of R L)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      IsStandardSmooth R B ∧ ∃ (β : A →ₐ[R] B) (δ : B →ₐ[R] L), δ.comp β = f := by
  classical
  let R' := ULift.{v} R
  let E : CommAlgCat.{max u v} R ⥤ Under (CommRingCat.of R') :=
    { obj := fun B ↦ Under.mk (CommRingCat.ofHom
        ((algebraMap R B).comp ULift.ringEquiv.toRingHom))
      map := fun g ↦ Under.homMk (CommRingCat.ofHom g.hom.toRingHom)
        (by ext r; exact g.hom.commutes r.down)
      map_id := by intro B; ext x; rfl
      map_comp := by intros; ext x; rfl }
  let G : Under (CommRingCat.of R') ⥤ CommAlgCat.{max u v} R :=
    { obj := fun B ↦ let := (B.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
                    CommAlgCat.of R B.right
      map := fun {X Y} g ↦ by
        let := (X.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        let := (Y.hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.ofHom
          { toRingHom := g.right.hom
            commutes' := fun r ↦ congrArg (fun h ↦ h.hom (ULift.up r)) g.w }
      map_id := by intro B; rfl
      map_comp := by intros; rfl }
  have hE : E.IsEquivalence := by
    apply Functor.IsEquivalence.mk' G
    · exact NatIso.ofComponents (fun B ↦ by
        let := ((E.obj B).hom.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.isoMk
          { toRingEquiv := RingEquiv.refl B, commutes' := fun _ ↦ rfl })
        (by intros; ext x; rfl)
    · exact NatIso.ofComponents (fun B ↦ Under.isoMk (Iso.refl _)
        (by ext r; rfl)) (by intros; ext x; rfl)
  let := hE
  obtain ⟨J, hcat, hfiltered, pres, hsmooth⟩ := hind
  let := hcat
  let := hfiltered
  have : IsConnected J := IsFiltered.isConnected J
  let F := pres.diag ⋙ E ⋙ Under.forget (CommRingCat.of R')
  have hcol : Limits.IsColimit ((E ⋙ Under.forget (CommRingCat.of R')).mapCocone pres.cocone) :=
    Limits.isColimitOfPreserves (E ⋙ Under.forget (CommRingCat.of R')) pres.isColimit
  let α : (Functor.const J).obj (CommRingCat.of R') ⟶ F :=
    { app := fun j ↦ CommRingCat.ofHom
        ((algebraMap R (pres.diag.obj j)).comp ULift.ringEquiv.toRingHom)
      naturality := by intro i j g; ext r; exact ((pres.diag.map g).hom.commutes r.down).symm }
  -- A finite polynomial quotient fits in the diagram universe even when A does not.
  obtain ⟨n, K, e, _hK⟩ := FinitePresentation.iff.mp (inferInstance : FinitePresentation R A)
  let Q := MvPolynomial (Fin n) R ⧸ K
  have : FinitePresentation R Q := FinitePresentation.equiv e.symm
  let A' := ULift.{v} Q
  let : Algebra R' R := ULift.algebra' R _
  let : Algebra R' A' := ULift.algebra' R _
  have : IsScalarTower R' R A' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let eR : R' ≃ₐ[R'] R :=
    { toRingEquiv := ULift.ringEquiv, commutes' := fun _ ↦ rfl }
  have : FinitePresentation R' R := FinitePresentation.equiv eR
  have : FinitePresentation R A' := FinitePresentation.equiv ULift.algEquiv.symm
  have : FinitePresentation R' A' := FinitePresentation.trans R' R A'
  let ee : A' ≃ₐ[R] A := (ULift.algEquiv (R := R)).trans e
  let g := f.comp ee.toAlgHom
  obtain ⟨j, g', hg'R, hg'⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of R') F α (CommRingCat.ofHom (algebraMap R' A')) _ hcol
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (CommRingCat.ofHom g.toRingHom) (by
        intro j
        ext r
        exact (g.commutes r.down).trans ((pres.ι.app j).hom.commutes r.down).symm)
  let β' : A' →ₐ[R] pres.diag.obj j :=
    { toRingHom := g'.hom
      commutes' := fun r ↦ congrArg (fun h ↦ h.hom (ULift.up r)) hg'R }
  refine ⟨pres.diag.obj j, inferInstance, inferInstance, hsmooth j,
    β'.comp ee.symm.toAlgHom, (pres.ι.app j).hom, ?_⟩
  ext x
  have hx := congrArg (fun h ↦ h.hom (ee.symm x)) hg'
  change g (ee.symm x) = (pres.ι.app j).hom (β' (ee.symm x)) at hx
  simpa [g] using hx.symm

/-- Lift a presentation of any finitely presented algebra over the reduced source.
The quotient of the lifted relations is isomorphic to the given algebra; no smoothness
or filtered-colimit hypothesis is needed.
Source: Stacks Project, Tag 07CK (lemma-lift-once), coefficientwise lifting. -/
private theorem exists_lifted_presentation
    (R : Type u) [CommRing R] (Λ : Type v) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A] (φ : A →ₐ[R] Λ)
    (C : Type*) [CommRing C] [Algebra (A ⧸ I.map (algebraMap R A)) C]
    [FinitePresentation (A ⧸ I.map (algebraMap R A)) C]
    (δ : C →+* (Λ ⧸ I.map (algebraMap R Λ)))
    (hfactor : ∀ a : A,
      δ (algebraMap (A ⧸ I.map (algebraMap R A)) C
        (Ideal.Quotient.mk (I.map (algebraMap R A)) a)) =
      Ideal.Quotient.mk (I.map (algebraMap R Λ)) (φ a)) :
    ∃ (n m : ℕ) (g : Fin m → MvPolynomial (Fin n) A) (lifts : Fin n → Λ),
      (∀ i, MvPolynomial.eval₂ φ.toRingHom lifts (g i) ∈ I.map (algebraMap R Λ)) ∧
      Nonempty ((MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
        Ideal.span (Set.range fun i ↦
          MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i)))
        ≃ₐ[A ⧸ I.map (algebraMap R A)] C) := by
  classical
  let IA := I.map (algebraMap R A)
  let IL := I.map (algebraMap R Λ)
  let Q := A ⧸ IA
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin Q C
  choose g hg using (fun i : Fin m ↦
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective (P.relation i))
  choose lifts hlifts using (fun i : Fin n ↦ Ideal.Quotient.mk_surjective (δ (P.val i)))
  refine ⟨n, m, g, lifts, ?_, ?_⟩
  · have heval (p : MvPolynomial (Fin n) A) :
        Ideal.Quotient.mk IL (MvPolynomial.eval₂ φ.toRingHom lifts p) =
          δ (MvPolynomial.aeval P.val (MvPolynomial.map (Ideal.Quotient.mk IA) p)) := by
      induction p using MvPolynomial.induction_on with
      | C a =>
        simp only [MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
        have hh := hfactor a
        exact hh.symm
      | add p q hp hq =>
        simp only [MvPolynomial.eval₂_add, map_add, hp, hq]
      | mul_X p i hp =>
        simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul,
          MvPolynomial.map_X, MvPolynomial.aeval_X, hp]
        rw [show Ideal.Quotient.mk IL (lifts i) = δ (P.val i) from hlifts i]
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := heval (g i)
    rw [hg i] at hh
    rw [P.aeval_val_relation, map_zero] at hh
    exact hh
  · have e : (MvPolynomial (Fin n) Q ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[Q] C :=
      (Ideal.quotientEquivAlgOfEq Q P.span_range_relation_eq_ker).trans
        (P.quotientEquiv.restrictScalars Q)
    have heq : (fun i ↦ MvPolynomial.map (Ideal.Quotient.mk IA) (g i)) = P.relation :=
      funext hg
    rw [heq]
    exact ⟨e⟩

/-- Express membership in the image ideal of any ring homomorphism as a finite sum.
Source: Stacks Project, Tag 07CK (lemma-lift-once), the coefficients εᵢⱼ and μᵢⱼ. -/
private theorem exists_sum_of_mem_ringHom_map
    {R : Type u} [CommRing R] {Λ : Type v} [CommRing Λ]
    (f : R →+* Λ) (I : Ideal R) (x : Λ) (hx : x ∈ I.map f) :
    ∃ (k : ℕ) (ε : Fin k → I) (μ : Fin k → Λ),
      x = ∑ j, f (ε j) * μ j := by
  classical
  have hrange : f '' (I : Set R) =
      Set.range (fun a : I ↦ f a) := by
    ext y
    simp
  rw [Ideal.map, hrange, Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, hc⟩ := hx
  let e := (Fintype.equivFin c.support).symm
  refine ⟨Fintype.card c.support, (fun j ↦ (e j).val), (fun j ↦ c (e j).val), ?_⟩
  rw [← hc]
  change (∑ a ∈ c.support, c a * f a) = _
  rw [← Finset.sum_attach]
  simpa only [mul_comm, Finset.attach_eq_univ] using
    (e.sum_comp (fun a : c.support ↦ c a.val * f a.val)).symm

/-- Finite-presentation factorization through a standard smooth reduction.
Source: Stacks Project, Tag 07CK, finite-presentation factorization.
The proof applies the filtered-colimit finite-presentation factorization to the
reduced map and retains the standard smooth stage and its factor maps.
(blueprint: new-lem-popescu-reduction-factor-core) -/
theorem exists_standardSmooth_reduction_factorization_core
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra R C),
      FinitePresentation R C ∧
      ∃ (ι : A →ₐ[R] C) (φ' : C →ₐ[R] Λ), φ'.comp ι = φ ∧
        IsStandardSmooth (R ⧸ I) (C ⧸ I.map (algebraMap R C)) := by
  classical
  -- Factor the reduced source, then apply the general coefficientwise lifting lemma.
  let IA := I.map (algebraMap R A)
  let IL := I.map (algebraMap R Λ)
  let Q := A ⧸ IA
  let L := Λ ⧸ IL
  have : FinitePresentation (R ⧸ I) Q :=
    FinitePresentation.equiv (TensorProduct.quotIdealMapEquivQuotTensor A I).symm
  let f : Q →ₐ[R] L := Ideal.Quotient.liftₐ IA
    ((Ideal.Quotient.mkₐ R IL).comp φ) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hmap : IA ≤ IL.comap φ.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change φ (algebraMap R A r) ∈ IL
        rw [φ.commutes]
        exact Ideal.mem_map_of_mem _ hr
      exact hmap ha)
  let fbar : Q →ₐ[R ⧸ I] L :=
    f.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
  obtain ⟨C, hCring, hCalg, hC, β, δ, hfactor⟩ := exists_standard_factor fbar hΛ
  let : Algebra Q C := β.toRingHom.toAlgebra
  have : IsScalarTower (R ⧸ I) Q C := IsScalarTower.of_algebraMap_eq
    (fun r ↦ (β.commutes r).symm)
  have : IsStandardSmooth (R ⧸ I) C := hC
  have : FinitePresentation Q C :=
    FinitePresentation.of_restrict_scalars_finitePresentation (R ⧸ I) Q C
  obtain ⟨n, m, g, lifts, hg, ⟨epres⟩⟩ :=
    exists_lifted_presentation R Λ I A φ C δ.toRingHom (fun a ↦
      AlgHom.congr_fun hfactor (Ideal.Quotient.mk IA a))
  have hstd := IsStandardSmooth.of_algEquiv (epres.restrictScalars (R ⧸ I)).symm
  choose N ε μ hsum using
    (fun i ↦ exists_sum_of_mem_ringHom_map (algebraMap R Λ) I _ (hg i))
  -- Correct each relation by finitely many variables so evaluation vanishes in Λ.
  let V := PopescuCorrectionVariables.{max u v w} n m N
  let P := MvPolynomial V A
  let J : Ideal P := popescuCorrectionIdeal.{u, w, max u v w} R A I n m N g ε
  let A' := P ⧸ J
  let values : V → Λ := Sum.elim lifts (fun j ↦ μ j.down.1 j.down.2)
  let ev : P →ₐ[R] Λ :=
    { toRingHom := MvPolynomial.eval₂Hom φ.toRingHom values
      commutes' := fun r ↦ by
        exact (MvPolynomial.eval₂Hom_C φ.toRingHom values (algebraMap R A r)).trans
          (φ.commutes r) }
  have hrel (i : Fin m) :
      ev (popescuCorrectionRelation.{u, w, max u v w} R A I n m N g ε i) = 0 := by
    change MvPolynomial.eval₂Hom φ.toRingHom values
      (popescuCorrectionRelation.{u, w, max u v w} R A I n m N g ε i) = 0
    dsimp only [popescuCorrectionRelation, V, PopescuCorrectionVariables] at values ⊢
    rw [map_sub, map_sum]
    simp only [MvPolynomial.eval₂Hom_rename, map_mul, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X']
    apply sub_eq_zero.mpr
    calc
      _ = MvPolynomial.eval₂ φ.toRingHom lifts (g i) := rfl
      _ = ∑ j, algebraMap R Λ (ε i j) * μ i j := hsum i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        exact (φ.commutes (ε i j)).symm
  have hJ : J ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let φ' : A' →ₐ[R] Λ := Ideal.Quotient.liftₐ J ev (fun p hp ↦ hJ hp)
  let ι : A →ₐ[R] A' := (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R A P)
  have hcomp : φ'.comp ι = φ := by
    ext a
    change ev (algebraMap A P a) = φ a
    exact MvPolynomial.eval₂_C _ _ _
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have : FinitePresentation R A' := FinitePresentation.quotient hfg
  refine ⟨A', inferInstance, inferInstance, inferInstance, ι, φ', hcomp, ?_⟩
  -- Modulo I, the correction terms vanish and only free variables remain.
  obtain ⟨e⟩ := nonempty_popescuCorrectionQuotient_reduction_equiv.{u, w, max u v w}
    R A I n m N g ε
  let B := MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
    Ideal.span (Set.range fun i ↦
      MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i))
  let D := ULift.{max u v w} (Σ i : Fin m, Fin (N i))
  have : IsStandardSmooth (R ⧸ I) B := hstd
  have : IsStandardSmooth B (MvPolynomial D B) :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth (Nat.card D)
  have : IsStandardSmooth (R ⧸ I) (MvPolynomial D B) :=
    IsStandardSmooth.trans (R ⧸ I) B (MvPolynomial D B)
  exact IsStandardSmooth.of_algEquiv e.symm

end Algebra
