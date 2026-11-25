/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat
import WeilConjectures.RingTheory.FlatColimitRings
import WeilConjectures.RingTheory.PairHenselizationCompletionData
import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Faithful flatness of the completion comparison for a pair henselization

Source: Stacks Project, More on Algebra, Tag 0AGV, middle paragraphs of the proof.
(blueprint: lem-weil-pbc-henselization-completion-faithfully-flat).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

private theorem stage_completion_flat
    (A B H : Type u) [CommRing A] [CommRing B] [CommRing H] [IsNoetherianRing B]
    (I : Ideal A) (f : A →+* B) (η : A →+* H) (ι : B →+* H)
    (hι : ι.comp f = η) (hf : f.Flat)
    (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (θ : AdicCompletion I A ≃+* AdicCompletion (I.map η) H)
    (hθ : ∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
      AdicCompletion.evalₐ (I.map η) n (θ x) =
        Ideal.Quotient.mk ((I.map η) ^ n) (η a)) :
    ((θ.symm.toRingHom.comp (algebraMap H (AdicCompletion (I.map η) H))).comp ι).Flat := by
  classical
  obtain ⟨α, hα, _⟩ := pair_henselization_completion_data A B I f
    (RingHom.bijective_quotientMap_pow_of_flat f hf I hq)
  have heq :
      (θ.symm.toRingHom.comp (algebraMap H (AdicCompletion (I.map η) H))).comp ι =
        α.symm.toRingHom.comp (algebraMap B (AdicCompletion (I.map f) B)) := by
    apply RingHom.ext
    intro b
    apply θ.injective
    change θ (θ.symm (algebraMap H _ (ι b))) =
      θ (α.symm (algebraMap B _ b))
    rw [RingEquiv.apply_symm_apply]
    apply AdicCompletion.ext_evalₐ
    intro n
    let x := α.symm (algebraMap B (AdicCompletion (I.map f) B) b)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hαa := hα n x a ha.symm
    have hθa := hθ n x a ha.symm
    have hxa : α x = algebraMap B (AdicCompletion (I.map f) B) b :=
      α.apply_symm_apply _
    rw [hxa] at hαa
    simp only [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Algebra.algebraMap_self, RingHom.id_apply] at hαa
    let qBH := Ideal.quotientMap ((I.map η) ^ n) ι
      (show (I.map f) ^ n ≤ (((I.map η) ^ n).comap ι) by
        apply Ideal.map_le_iff_le_comap.mp
        rw [Ideal.map_pow, Ideal.map_map, hι])
    have hb := congrArg qBH hαa
    change Ideal.Quotient.mk ((I.map η) ^ n) (ι b) =
      Ideal.Quotient.mk ((I.map η) ^ n) (ι (f a)) at hb
    rw [show ι (f a) = η a from RingHom.congr_fun hι a] at hb
    change AdicCompletion.evalₐ (I.map η) n (algebraMap H _ (ι b)) =
      AdicCompletion.evalₐ (I.map η) n (θ x)
    rw [hθa]
    simpa only [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Algebra.algebraMap_self, RingHom.id_apply] using hb
  rw [heq]
  exact ((RingHom.flat_algebraMap_iff).mpr inferInstance).comp
    (RingHom.Flat.of_bijective α.symm.bijective)

/-- The canonical map from a pair henselization to the base completion is faithfully flat.
Source: Stacks Project, More on Algebra, Tag 0AGV, middle paragraphs of the proof.
(blueprint: lem-weil-pbc-henselization-completion-faithfully-flat).

Proof: The pair-henselization theorem presents the vertex as a filtered colimit of
étale A-algebras B trivial modulo I and makes its extended ideal J henselian.
These properties transfer to the specified cocone by the unique colimit isomorphism
in the under category, which carries the structure map and extended ideal with it.
Each B is finitely presented over A, hence Noetherian. Étale flatness and the
flat quotient-power lemma identify A/I^n with B/(IB)^n for every positive n.
These identifications commute with transitions, hence identify the B-completion
with the A-completion. For the coprojection B → Aʰ, its composite with the map
γ = θ⁻¹ ∘ completion has, on every quotient coordinate, precisely this comparison:
both composites send a representative b to its image in the henselization quotient.
Thus B → A^ is the completion map B → B^ followed by the comparison isomorphism.
It is flat since B is Noetherian. Flatness over a filtered colimit now makes γ flat.
The henselian-pair factorization criterion gives J ⊆ Jac(Aʰ). Evaluate the base
completion at n = 1. The given compatibility for θ and the isomorphism A/I → Aʰ/J
show that this projection composed with γ is the quotient map Aʰ → Aʰ/J followed
by that isomorphism's inverse. For each maximal ideal m of Aʰ, J ⊆ m, and the
image of m in Aʰ/J is proper. Consequently m A^ is proper, since its image under
the projection A^ → A/I lies in that proper ideal. The maximal-ideal criterion
for faithful flatness applies to the flat map γ. No Noetherianity of Aʰ is used. -/
theorem pair_henselization_completion_faithfullyFlat
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c)
    (θ : AdicCompletion I A ≃+*
      AdicCompletion (I.map c.pt.hom.hom) c.pt.right)
    (hθ : ∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
      AdicCompletion.evalₐ (I.map c.pt.hom.hom) n (θ x) =
        Ideal.Quotient.mk ((I.map c.pt.hom.hom) ^ n) (c.pt.hom.hom a)) :
    RingHom.FaithfullyFlat
      (θ.symm.toRingHom.comp
        (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))) := by
  classical
  let J := I.map c.pt.hom.hom
  let γ := θ.symm.toRingHom.comp (algebraMap c.pt.right (AdicCompletion J c.pt.right))
  obtain ⟨hsmall, hfiltered, d, ⟨hd⟩, hH, hq⟩ := pair_henselization A I
  let e := (Under.forget (CommRingCat.of A)).mapIso (hd.coconePointUniqueUpToIso hc)
  let E : d.pt.right ≃+* c.pt.right := e.commRingCatIsoToRingEquiv
  have hη : E.toRingHom.comp d.pt.hom.hom = c.pt.hom.hom := by
    exact congrArg CommRingCat.Hom.hom (Under.w (hd.coconePointUniqueUpToIso hc).hom)
  have hJ : J = (I.map d.pt.hom.hom).map E.toRingHom := by
    rw [Ideal.map_map, hη]
  have hjac : J ≤ Ideal.jacobson (⊥ : Ideal c.pt.right) := by
    rw [hJ]
    have hmap := Ideal.map_mono (f := E.toRingHom) hH.jac
    have heq := Ideal.map_jacobson_of_bijective (I := (⊥ : Ideal d.pt.right))
      (f := E.toRingHom) E.bijective
    rw [Ideal.map_bot] at heq
    exact hmap.trans_eq heq
  let q := Ideal.quotientMap J c.pt.hom.hom Ideal.le_comap_map
  have hqbij : Function.Bijective q := by
    let Q := Ideal.quotientEquiv (I.map d.pt.hom.hom) J E hJ
    have hcomp : q = Q.toRingHom.comp
        (Ideal.quotientMap (I.map d.pt.hom.hom) d.pt.hom.hom Ideal.le_comap_map) := by
      ext a
      change Ideal.Quotient.mk J (c.pt.hom.hom a) =
        Ideal.Quotient.mk J (E (d.pt.hom.hom a))
      exact congrArg (Ideal.Quotient.mk J) (RingHom.congr_fun hη a).symm
    rw [hcomp]
    exact Q.bijective.comp hq
  let Q := RingEquiv.ofBijective q hqbij
  let π := (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)).comp
    (AdicCompletion.evalₐ I 1).toRingHom
  have hπ (h : c.pt.right) : Q (π (γ h)) = Ideal.Quotient.mk J h := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ I 1 (γ h))
    have ht : AdicCompletion.evalₐ J 1 (θ (γ h)) =
        Ideal.Quotient.mk (J ^ 1) (c.pt.hom.hom a) := hθ 1 (γ h) a ha.symm
    have heval : AdicCompletion.evalₐ J 1
        (algebraMap c.pt.right (AdicCompletion J c.pt.right) h) =
        Ideal.Quotient.mk (J ^ 1) h := by
      exact AdicCompletion.evalₐ_of J 1 h
    have hγ : θ (γ h) = algebraMap c.pt.right (AdicCompletion J c.pt.right) h :=
      θ.apply_symm_apply _
    have hb : Ideal.Quotient.mk (J ^ 1) h =
        Ideal.Quotient.mk (J ^ 1) (c.pt.hom.hom a) :=
      heval.symm.trans ((congrArg (AdicCompletion.evalₐ J 1) hγ).symm.trans ht)
    have hπa : π (γ h) = Ideal.Quotient.mk I a := by
      change Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)
        (AdicCompletion.evalₐ I 1 (γ h)) = _
      rw [← ha, Ideal.Quotient.factor_mk]
    apply (congrArg Q hπa).trans
    change Ideal.Quotient.mk J (c.pt.hom.hom a) = _
    exact congrArg (Ideal.Quotient.factor (show J ^ 1 ≤ J by simp)) hb.symm
  have hflat : γ.Flat := by
    let P : ObjectProperty (Under (CommRingCat.of A)) := fun C ↦
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
          Ideal.le_comap_map)
    let : EssentiallySmall.{u} P.FullSubcategory := hsmall
    let : IsFiltered P.FullSubcategory := hfiltered
    let s := equivSmallModel.{u} P.FullSubcategory
    let : IsFiltered (SmallModel.{u} P.FullSubcategory) := IsFiltered.of_equivalence s
    let cs := c.whisker s.inverse
    have hcs : IsColimit cs := hc.whiskerEquivalence s.symm
    let U := Under.forget (CommRingCat.of A)
    let F := s.inverse ⋙ P.ι ⋙ U
    let cr : Cocone F := U.mapCocone cs
    have hcr : IsColimit cr := isColimitOfPreserves U hcs
    let : HasColimit F := ⟨⟨cr, hcr⟩⟩
    let E := (hcr.coconePointUniqueUpToIso (colimit.isColimit F)).commRingCatIsoToRingEquiv
    have hE : ∀ i, E.toRingHom.comp (cr.ι.app i).hom = (colimit.ι F i).hom := by
      intro i
      exact congrArg CommRingCat.Hom.hom
        (hcr.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) i)
    have hstage : ∀ i, (γ.comp (cr.ι.app i).hom).Flat := by
      intro i
      let B := (s.inverse.obj i).obj
      let : Algebra A B.right := B.hom.hom.toAlgebra
      let : Algebra.Etale A B.right :=
        (AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.Etale)).mp (s.inverse.obj i).property.1
      let : IsNoetherianRing B.right := Algebra.FiniteType.isNoetherianRing A B.right
      have hf : B.hom.hom.Flat := inferInstanceAs (Module.Flat A B.right)
      exact stage_completion_flat A B.right c.pt.right I B.hom.hom c.pt.hom.hom
        (cr.ι.app i).hom
        (congrArg CommRingCat.Hom.hom (Under.w (cs.ι.app i))) hf
        (s.inverse.obj i).property.2 θ hθ
    have hψ : (γ.comp E.symm.toRingHom).Flat := by
      apply RingHom.flat_of_flat_comp_colimit_ι F
      intro i
      have he : E.symm.toRingHom.comp (colimit.ι F i).hom = (cr.ι.app i).hom := by
        rw [← hE i, ← RingHom.comp_assoc]
        simp
      rw [RingHom.comp_assoc, he]
      exact hstage i
    have h := (RingHom.Flat.of_bijective E.bijective).comp hψ
    have he : (γ.comp E.symm.toRingHom).comp E.toRingHom = γ := by
      apply RingHom.ext
      intro x
      change γ (E.symm (E x)) = γ x
      rw [RingEquiv.symm_apply_apply]
    exact he ▸ h
  let : Algebra c.pt.right (AdicCompletion I A) := γ.toAlgebra
  change Module.FaithfullyFlat c.pt.right (AdicCompletion I A)
  apply (Module.faithfullyFlat_iff _ _).mpr
  refine ⟨hflat, ?_⟩
  intro m hm
  let : m.IsMaximal := hm
  have hJm : J ≤ m := hjac.trans (by
    rw [Ideal.jacobson]
    exact sInf_le ⟨bot_le, hm⟩)
  let mQ := m.map (Ideal.Quotient.mk J)
  have hmQ : mQ ≠ ⊤ := by
    exact (Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by simpa using hJm)).ne_top
  let ρ := Q.toRingHom.comp π
  have hmap : m.map γ ≤ mQ.comap ρ := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    change Q (π (γ h)) ∈ mQ
    rw [hπ]
    exact Ideal.mem_map_of_mem _ hh
  intro htop
  have htop' : m.map γ = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have h1 : (1 : AdicCompletion I A) ∈ m • (⊤ : Submodule c.pt.right _) := by
      rw [htop]
      trivial
    rw [Ideal.smul_top_eq_map] at h1
    exact h1
  exact (Ideal.comap_ne_top ρ hmQ) (top_le_iff.mp (htop' ▸ hmap))

end RingTheory
