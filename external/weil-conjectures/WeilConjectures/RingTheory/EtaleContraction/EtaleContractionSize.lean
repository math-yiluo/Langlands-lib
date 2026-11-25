/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.EtaleContraction.ThmPeIndetaleRefinementPart1
public import Mathlib.SetTheory.Cardinal.Aleph
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.PrincipalWLocalizationSize
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Algebra.MvPolynomial.Cardinal

/-! # Cardinality of the étale contraction

Source: Stacks Project, Tag 097S (blueprint: lem-weil-pbc-etale-contraction-size).
-/

@[expose] public section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

namespace CommRingCat.EtaleContraction

private theorem polynomial_bound (R : Type u) [CommRing R] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) (n : ℕ) : #(MvPolynomial (Fin n) R) ≤ κ := by
  apply MvPolynomial.cardinalMk_le_max_lift.trans
  simpa using max_le (max_le hR (natCast_le_aleph0.trans hκ)) hκ

private theorem finiteType_bound (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [hS : Algebra.FiniteType R S] (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) :
    #S ≤ κ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hS
  exact (mk_le_of_surjective hf).trans (polynomial_bound R κ hκ hR n)

private theorem representatives_bound (R : CommRingCat.{u}ᵒᵖ) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R.unop ≤ κ) : #(Representatives R) ≤ κ := by
  classical
  let C := ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)
  let F : Representatives R ⥤ C :=
    fromSkeleton (SmallModel.{u} C) ⋙ (equivSmallModel C).inverse
  let B (i : Representatives R) : CommRingCat.{u} := (F.obj i).left.unop
  let (i : Representatives R) : Algebra R.unop (B i) :=
    (F.obj i).hom.unop.hom.toAlgebra
  have hpres (i : Representatives R) :
      ∃ p : Σ n : ℕ, Finset (MvPolynomial (Fin n) R.unop),
        Nonempty ((MvPolynomial (Fin p.1) R.unop ⧸
          Ideal.span (↑p.2 : Set (MvPolynomial (Fin p.1) R.unop))) ≃ₐ[R.unop] B i) := by
    have he : (F.obj i).hom.unop.hom.Etale := (F.obj i).prop.1
    have : Algebra.FinitePresentation R.unop (B i) :=
      RingHom.finitePresentation_algebraMap.mp he.2
    obtain ⟨n, I, e, s, hs⟩ := Algebra.FinitePresentation.iff.mp this
    subst I
    exact ⟨⟨n, s⟩, ⟨e⟩⟩
  choose p ep using hpres
  have hp : Function.Injective p := by
    intro i j hij
    have epj : Nonempty
        ((MvPolynomial (Fin (p i).1) R.unop ⧸
          Ideal.span (↑(p i).2 : Set (MvPolynomial (Fin (p i).1) R.unop))) ≃ₐ[R.unop] B j) :=
      hij.symm ▸ ep j
    let e : B i ≃ₐ[R.unop] B j := (ep i).some.symm.trans epj.some
    have hB : F.obj i ≅ F.obj j :=
      MorphismProperty.Over.isoMk (e.symm.toRingEquiv.toCommRingCatIso).op (by
        apply Quiver.Hom.unop_inj
        apply CommRingCat.hom_ext
        ext x
        exact e.symm.commutes x)
    exact skeleton_skeletal _ ⟨F.preimageIso hB⟩
  refine (mk_le_of_injective hp).trans ?_
  rw [mk_sigma]
  apply (sum_le_lift_mk_mul_iSup _).trans
  apply mul_le_of_le hκ
  · simpa using hκ
  · exact ciSup_le' (fun n ↦
      PrincipalWLocalization.finset_bound hκ (polynomial_bound R.unop κ hκ hR n))

private theorem finite_stage_bound (R : CommRingCat.{u}ᵒᵖ) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R.unop ≤ κ) (U : FiniteFamilies (Representatives R)) :
    #((finiteDiagram R).obj (op U)).left.unop ≤ κ := by
  let V := (FiniteFamilies.map (fromSkeleton (SmallModel.{u}
    ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)))).obj U
  have he : CommRingCat.etale.op ((finiteDiagram R).obj (op U)).hom := by
    change CommRingCat.etale.op (WidePullback.base V.hom)
    exact MorphismProperty.widePullbackBase CommRingCat.etale.op
      (fun i ↦ (FiniteFamilies.property_hom V i).1)
  let := ((finiteDiagram R).obj (op U)).hom.unop.hom.toAlgebra
  have : Algebra.FiniteType R.unop ((finiteDiagram R).obj (op U)).left.unop :=
    RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_finitePresentation he.2)
  exact finiteType_bound R.unop _ κ hκ hR

private theorem finite_families_bound {C : Type u} [Category C] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hC : #C ≤ κ) : #(FiniteFamilies C) ≤ κ := by
  classical
  let f : FiniteFamilies C → Finset C := fun U ↦ U.finite.toFinset
  have hf : Function.Injective f := by
    intro U V h
    apply FiniteFamilies.ext
    simpa [f] using congrArg (fun s : Finset C ↦ (s : Set C)) h
  exact (mk_le_of_injective hf).trans (PrincipalWLocalization.finset_bound hκ hC)

private theorem step_bound (R : CommRingCat.{u}ᵒᵖ) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R.unop ≤ κ) : #(step R).left.unop ≤ κ := by
  let : Nonempty (FiniteFamilies (Representatives R)) := ⟨⟨∅, Set.finite_empty⟩⟩
  let D := finiteDiagram R ⋙ Over.forget R
  let c := (Over.forget R).mapCone (limit.cone (finiteDiagram R))
  have hc : IsLimit c := isLimitOfPreserves (Over.forget R) (limit.isLimit _)
  have hc' := isColimitCoconeUnopOfCone D hc
  have hsurj := Concrete.from_union_surjective_of_isColimit D.unop hc'
  exact (mk_le_of_surjective hsurj).trans
    (PrincipalWLocalization.sigma_bound hκ
      (finite_families_bound κ hκ (representatives_bound R κ hκ hR))
      (finite_stage_bound R κ hκ hR))

/-- The successive étale contraction preserves an infinite cardinal bound.
Source: Stacks Project, Tag 097S (blueprint: lem-weil-pbc-etale-contraction-size).

Proof: choose finite polynomial presentations of the faithfully flat étale representatives.
Equality of presentation codes gives an algebra isomorphism and hence equality in the skeleton,
so there are at most κ representatives. Their finite subsets have at most κ elements. A stage
of the finite diagram is étale, since finite tensor coproducts preserve étaleness, and hence
is finitely generated over the base and has at most κ elements. The filtered colimit step has
at most κ elements by stage representatives. Induction bounds each successive step, and the
countable sequential colimit has the same bound. -/
theorem cardinalMk_le (R : CommRingCat.{u}) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) : #R.etaleContraction ≤ κ := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hstage (n : ℕ) : #(stage (op R) n).unop ≤ κ := by
    induction n with
    | zero => exact hR
    | succ n ih => exact step_bound _ κ hκ ih
  have hc := isColimitCoconeUnopOfCone (sequence (op R))
    (limit.isLimit (sequence (op R)))
  have hsurj := Concrete.from_union_surjective_of_isColimit (sequence (op R)).unop hc
  refine (mk_le_of_surjective hsurj).trans ?_
  rw [mk_sigma]
  apply (sum_le_lift_mk_mul_iSup _).trans
  apply mul_le_of_le hκ
  · simpa using hκ
  · exact ciSup_le' hstage

end CommRingCat.EtaleContraction
