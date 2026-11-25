/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.EtaleContraction.ThmPeIndetaleRefinementPart1
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Properties of the étale contraction

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1227;
Stacks Project, proetale.tex, lemma-first-construction and Tag 097V
(blueprint: theorem-existence-contractible-covers--1).
-/

@[expose] public section

universe u

namespace CommRingCat

-- The finite tensors present the step map as a pro-morphism in the opposite category.
open CategoryTheory CategoryTheory.Limits Opposite in
private theorem step_pro
    (Q : MorphismProperty CommRingCat.{u}ᵒᵖ)
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQ : etale.op ⊓ faithfullyFlat.op ≤ Q) (R : CommRingCat.{u}ᵒᵖ) :
    MorphismProperty.pro.{u} Q (EtaleContraction.step R).hom := by
  let : Nonempty (FiniteFamilies (EtaleContraction.Representatives R)) :=
    ⟨⟨∅, Set.finite_empty⟩⟩
  refine ⟨(FiniteFamilies (EtaleContraction.Representatives R))ᵒᵖ,
    inferInstance, inferInstance, EtaleContraction.finiteDiagram R ⋙ Over.forget R,
    ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
  · exact { app i := ((EtaleContraction.finiteDiagram R).obj i).hom }
  · exact Functor.whiskerRight (limit.cone (EtaleContraction.finiteDiagram R)).π
      (Over.forget R)
  · exact isLimitOfPreserves (Over.forget R) (limit.isLimit _)
  · change Q (WidePullback.base _)
    apply MorphismProperty.widePullbackBase
    intro i
    exact hQ _ (FiniteFamilies.property_hom _ i)
  · exact (limit.π (EtaleContraction.finiteDiagram R) j).w

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_prop
    (Q : MorphismProperty CommRingCat.{u}ᵒᵖ) [Q.IsMultiplicative]
    (hQ : MorphismProperty.pro.{u} Q = Q)
    (hstep : ∀ R : CommRingCat.{u}ᵒᵖ, Q (EtaleContraction.step R).hom)
    (R : CommRingCat.{u}) (n : ℕ) : Q (limit.π (EtaleContraction.sequence (op R)) (op n)) := by
  have hπ : MorphismProperty.pro.{0} Q
      (limit.π (EtaleContraction.sequence (op R)) (op n)) := by
    apply MorphismProperty.pro_coneπ (P := Q) (limit.isLimit _) (op n)
    intro k f
    apply MorphismProperty.ofOpSequence_map_of_isMultiplicative
    intro m
    exact hstep _
  exact hQ.le _ (MorphismProperty.pro_of_univLE.{0, u} _ hπ)

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_faithfullyFlat (R : CommRingCat.{u}) (n : ℕ) :
    (EtaleContraction.ι R n).hom.FaithfullyFlat := by
  have hQ : MorphismProperty.pro.{u} faithfullyFlat.op = faithfullyFlat.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  exact projection_prop faithfullyFlat.op hQ
    (fun A ↦ hQ.le _ (step_pro faithfullyFlat.op inf_le_right A)) R n

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem projection_indEtale (R : CommRingCat.{u}) (n : ℕ) :
    (EtaleContraction.ι R n).hom.IndEtale := by
  let P := CommRingCat.etale.op
  have hfp := MorphismProperty.le_isFinitelyPresentable_op_op
    CommRingCat.etale_le_isFinitelyPresentable.{u}
  let : (MorphismProperty.pro.{u} P).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.pro_of_le_isFinitelyPresentable hfp
  rw [RingHom.IndEtale.iff_ind_etale, MorphismProperty.ind_eq_unop_pro_op]
  exact projection_prop (MorphismProperty.pro.{u} P) (MorphismProperty.pro_pro hfp)
    (step_pro P inf_le_left) R n

-- The singleton containing the chosen isomorphism class supplies the next-stage map.
open CategoryTheory CategoryTheory.Limits Opposite in
private theorem step_factor (X : CommRingCat.{u}ᵒᵖ) {Y : CommRingCat.{u}ᵒᵖ}
    (f : Y ⟶ X) (hf : (etale.op ⊓ faithfullyFlat.op) f) :
    ∃ g : (EtaleContraction.step X).left ⟶ Y, g ≫ f = (EtaleContraction.step X).hom := by
  classical
  let P := etale.op ⊓ faithfullyFlat.op
  let A : P.Over ⊤ X := .mk _ _ hf
  let E := equivSmallModel.{u} (P.Over ⊤ X)
  let M := E.functor.obj A
  let r := toSkeleton M
  let U : FiniteFamilies (EtaleContraction.Representatives X) :=
    ⟨{r}, Set.finite_singleton _⟩
  let V := (FiniteFamilies.map (fromSkeleton (SmallModel.{u} (P.Over ⊤ X)))).obj U
  let i : V.Index := ⟨(fromSkeleton _).obj r, r, rfl, rfl⟩
  let e : E.inverse.obj ((fromSkeleton _).obj r) ≅ A :=
    E.inverse.mapIso (fromSkeletonToSkeletonIso M) ≪≫ (E.unitIso.app A).symm
  let p : (EtaleContraction.step X) ⟶ Over.mk f :=
    limit.π (EtaleContraction.finiteDiagram X) (op U) ≫
      Over.homMk (WidePullback.π V.hom i) (WidePullback.π_arrow _ _) ≫
      (Functor.mapIso (MorphismProperty.Over.forget P ⊤ X) e).hom
  exact ⟨p.left, p.w⟩

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem contraction_retraction (R : CommRingCat.{u})
    {Y : CommRingCat.{u}ᵒᵖ} (f : Y ⟶ op R.etaleContraction)
    (hf : etale.op f) (hf' : faithfullyFlat.op f) :
    ∃ g : op R.etaleContraction ⟶ Y, g ≫ f = 𝟙 (op R.etaleContraction) := by
  let P := etale.op
  let : MorphismProperty.PreProSpreads.{0} P := by
    rw [MorphismProperty.PreProSpreads.op_iff]
    exact MorphismProperty.PreIndSpreads.of_univLE.{u} _
  -- Algebraic étale descent already supplies an affine model and its pullback square.
  obtain ⟨⟨n⟩, D', u, v, hv, hu⟩ := P.exists_isPullback_of_isCofiltered
    (limit.cone (EtaleContraction.sequence (op R))) (limit.isLimit _) f hf
  have hu' : faithfullyFlat.op u := by
    have hfg : faithfullyFlat.op (v ≫ u) := by
      rw [← hv.w]
      exact faithfullyFlat.op.comp_mem _ _ hf' (projection_faithfullyFlat R n)
    change faithfullyFlat u.unop
    -- The composite is surjective on spectra; the descended étale map is flat.
    rw [CommRingCat.faithfullyFlat_eq] at ⊢ hfg
    refine ⟨hu.smooth.flat, ?_⟩
    exact Function.Surjective.of_comp (g := PrimeSpectrum.comap v.unop.hom) hfg.2
  obtain ⟨p, hp⟩ := step_factor (EtaleContraction.stage (op R) n) u ⟨hu, hu'⟩
  let l : op R.etaleContraction ⟶ Y :=
    hv.lift (𝟙 _) (limit.π (EtaleContraction.sequence (op R)) (op (n + 1)) ≫ p) (by
      rw [Category.id_comp, Category.assoc, hp]
      have h := limit.w (EtaleContraction.sequence (op R))
        (homOfLE (Nat.le_succ n)).op
      simpa [EtaleContraction.sequence, Functor.ofOpSequence] using h.symm)
  exact ⟨l, by simp [l]⟩

open CategoryTheory CategoryTheory.Limits Opposite in
private theorem ring_retraction (R : CommRingCat.{u})
    (B : Type u) [CommRing B] [Algebra R.etaleContraction B]
    (hB : Algebra.Etale R.etaleContraction B)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R.etaleContraction B))) :
    ∃ g : B →+* R.etaleContraction,
      g.comp (algebraMap R.etaleContraction B) = RingHom.id R.etaleContraction := by
  have het : (algebraMap R.etaleContraction B).Etale := RingHom.etale_algebraMap.mpr hB
  have hff : (algebraMap R.etaleContraction B).FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨het.smooth.flat, hsurj⟩
  obtain ⟨g, hg⟩ := contraction_retraction R
    (CommRingCat.ofHom (algebraMap R.etaleContraction B)).op het hff
  exact ⟨g.unop.hom, congr($(hg).unop.hom)⟩

/-- The canonical map to the étale contraction is faithfully flat and ind-étale;
faithfully flat étale algebras of finite presentation over it admit a section,
and its maximal localizations are strictly henselian.
Source: blueprint order 1227; Stacks, lemma-first-construction and Tag 097V
(blueprint: theorem-existence-contractible-covers--1).

Proof plan:
1. Each chosen factor is faithfully flat. Tensor base change and composition preserve
faithful flatness, by the tensor identities on complexes, so all finite tensors and their
transition maps are faithfully flat, including the empty tensor.
2. Apply lem-weil-pbc-directed-colimit-faithfully-flat-algebras to finite-subset colimits
and then the sequential colimit. Apply lemma-stability to finite tensors,
base changes, compositions and these filtered colimits to get ind-étaleness.
3. An étale finitely presented algebra over the contraction descends to a stage by
lemma-acyclicity-pulled-back-injectives. Use lem-weil-pbc-limit-affine-transition and
lem-weil-pbc-limit-affine-stage to make the model affine; its quasi-compactness and
quasi-separatedness and affine transitions follow from
lem-weil-pbc-affine-morphism-permanence. Faithful flatness descends by applying the
faithfully flat stage-to-colimit extension to complexes and the tensor identities.
4. The descended algebra is isomorphic to a chosen representative. Its singleton tensor
factor maps into the next stage and hence into the contraction. The tensor universal
property (lem-weil-pbc-algebra-tensor-base-change-universal-property) gives the retraction
by sending s ⊗ b to s h(b).
5. Every étale map of affine spectra is of finite presentation, since it is locally so
and affine maps are quasi-compact and quasi-separated. Thus the section property applies
to all faithfully flat étale algebras. Apply
lem-weil-pbc-split-etale-covers-maximal-local-criterion (Tag 097V) to each maximal ideal.
-/
theorem etaleContraction_properties (R : CommRingCat.{u}) :
    (EtaleContraction.ι R 0).hom.FaithfullyFlat ∧
    (EtaleContraction.ι R 0).hom.IndEtale ∧
    (∀ (B : Type u) [CommRing B] [Algebra R.etaleContraction B],
      Module.FaithfullyFlat R.etaleContraction B →
      Algebra.Etale R.etaleContraction B →
      Algebra.FinitePresentation R.etaleContraction B →
      Nonempty (B →ₐ[R.etaleContraction] R.etaleContraction)) ∧
    (∀ (m : Ideal R.etaleContraction) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m)) := by
  refine ⟨projection_faithfullyFlat R 0, projection_indEtale R 0, ?_, ?_⟩
  · intro B _ _ hff het _
    have hff' : (algebraMap R.etaleContraction B).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr hff
    obtain ⟨g, hg⟩ := ring_retraction R B het
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff').2
    exact ⟨{ g with commutes' := fun r ↦ congrFun (congrArg DFunLike.coe hg) r }⟩
  · intro m _
    exact IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
      (ring_retraction R) m

end CommRingCat
