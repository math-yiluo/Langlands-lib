/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.RegularBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.Algebra.IndSmoothQuotientCompatibility
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Maximal bad quotients for Popescu's theorem -/

@[expose] public section

universe u v
open CategoryTheory

private theorem regular_of_algEquiv
    {R : Type u} {S T : Type (max u v)} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T)
    (h : (algebraMap R S).IsRegular) : (algebraMap R T).IsRegular := by
  rw [RingHom.IsRegular, toAlgebra_algebraMap] at h ⊢
  refine ⟨?_, ?_⟩
  · have he : e.toRingHom.comp (algebraMap R S) = algebraMap R T := by
      ext x
      exact e.commutes x
    rw [← he]
    exact h.1.comp (RingHom.Flat.of_bijective e.bijective)
  · intro p _
    let e' := Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField) e
    have hn : IsNoetherianRing (p.Fiber S) := (h.2 p).1
    refine ⟨isNoetherianRing_of_ringEquiv (p.Fiber S) e'.toRingEquiv, ?_⟩
    intro K _ _ _ _
    have := (h.2 p).2 K
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[K] K) e').toRingEquiv

private theorem nontrivial_of_bad
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    (hbad : ¬ ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R ↦ Algebra.Smooth R B) (CommAlgCat.of R Λ)) :
    Nontrivial R := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · let : Subsingleton R := hs
    let : Subsingleton Λ := Algebra.subsingleton R Λ
    have hsmooth : Algebra.Smooth R Λ := inferInstance
    exact False.elim (hbad (ObjectProperty.le_ind _ _ hsmooth))
  · exact hn

/-- A failure of ind-smoothness has a nonzero maximal bad quotient.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F5,
first paragraph, lines 2011--2026 (blueprint: lem-weil-pbc-popescu-maximal-bad-quotient).

Proof: For the given regular map, consider the ideals I for which the induced map
R/I → Λ/IΛ is not ind-smooth. The zero ideal belongs to this set: the quotient by
zero is canonically isomorphic to the original algebra. The ascending chain condition
on ideals gives a maximal member I. Quotients are Noetherian, and regular base change
along R → R/I gives regularity of the quotient map, using the tensor-quotient
isomorphism. Every nonzero ideal J of R/I comes from an ideal strictly containing I;
maximality and the quotient-of-quotient isomorphisms give ind-smoothness modulo J.
The quotient R/I is nonzero, since a zero base forces a zero target, which is itself
smooth over that base and hence a constant filtered colimit. All algebra and colimit
properties are transported along the canonical quotient isomorphisms. -/
theorem exists_popescu_maximal_bad_quotient
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (hbad : ¬ ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} R ↦ Algebra.Smooth R B) (CommAlgCat.of R Λ)) :
    ∃ (R' : Type u) (Λ' : Type (max u v)) (_ : CommRing R') (_ : CommRing Λ')
      (_ : Algebra R' Λ') (_ : IsNoetherianRing R') (_ : IsNoetherianRing Λ')
      (_ : Nontrivial R'),
      RingHom.IsRegular (algebraMap R' Λ') ∧
      (¬ ObjectProperty.ind.{max u v}
        (fun B : CommAlgCat.{max u v} R' ↦ Algebra.Smooth R' B) (CommAlgCat.of R' Λ')) ∧
      ∀ (I : Ideal R'), I ≠ ⊥ →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} (R' ⧸ I) ↦ Algebra.Smooth (R' ⧸ I) B)
          (CommAlgCat.of (R' ⧸ I) (Λ' ⧸ I.map (algebraMap R' Λ'))) := by
  classical
  let bad : Set (Ideal R) := {I | I = ⊥ ∨ ¬ ObjectProperty.ind.{max u v}
    (fun B : CommAlgCat.{max u v} (R ⧸ I) ↦ Algebra.Smooth (R ⧸ I) B)
    (CommAlgCat.of (R ⧸ I) (Λ ⧸ Ideal.map (algebraMap R Λ) I))}
  obtain ⟨I, hI, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R)
      bad ⟨⊥, Or.inl rfl⟩
  rcases hI with hzero | hbadquot
  · subst I
    refine ⟨R, Λ, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, nontrivial_of_bad R Λ hbad, hreg, hbad, ?_⟩
    intro J hJ
    by_contra h
    exact hmax J (Or.inr h) (bot_lt_iff_ne_bot.mpr hJ)
  · have hregular : RingHom.IsRegular
        (algebraMap (R ⧸ I) (Λ ⧸ Ideal.map (algebraMap R Λ) I)) := by
      let : Algebra (R ⧸ I) (TensorProduct R Λ (R ⧸ I)) :=
        Algebra.TensorProduct.rightAlgebra
      let e : (Λ ⧸ Ideal.map (algebraMap R Λ) I) ≃ₐ[R ⧸ I]
          TensorProduct R Λ (R ⧸ I) :=
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ I).trans
          (Algebra.TensorProduct.commRight R (R ⧸ I) Λ)
      exact regular_of_algEquiv e.symm (RingHom.regular_base_change hreg)
    refine ⟨R ⧸ I, Λ ⧸ Ideal.map (algebraMap R Λ) I, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance,
      nontrivial_of_bad (R ⧸ I) (Λ ⧸ Ideal.map (algebraMap R Λ) I) hbadquot,
      hregular, hbadquot, ?_⟩
    intro J hJ
    have hle : I ≤ J.comap (Ideal.Quotient.mk I) := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hne : I ≠ J.comap (Ideal.Quotient.mk I) := by
      intro heq
      apply hJ
      have hh := congrArg (Ideal.map (Ideal.Quotient.mk I)) heq
      simpa only [Ideal.map_quotient_self,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] using hh.symm
    have hgood : ObjectProperty.ind.{max u v}
        (fun B : CommAlgCat.{max u v} (R ⧸ J.comap (Ideal.Quotient.mk I)) ↦
          Algebra.Smooth (R ⧸ J.comap (Ideal.Quotient.mk I)) B)
        (CommAlgCat.of (R ⧸ J.comap (Ideal.Quotient.mk I))
          (Λ ⧸ Ideal.map (algebraMap R Λ) (J.comap (Ideal.Quotient.mk I)))) := by
      by_contra h
      exact hmax _ (Or.inr h) (lt_of_le_of_ne hle hne)
    have htower := Algebra.ind_smooth_quotient_compatibility R Λ
      (J.comap (Ideal.Quotient.mk I)) I hle hgood
    dsimp only at htower
    have he : Ideal.map (Ideal.Quotient.mk I) (J.comap (Ideal.Quotient.mk I)) = J :=
      Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J
    rw [he] at htower
    exact htower
