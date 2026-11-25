/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.RingTheory.PopescuLocalizedIndSmooth
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.FiniteStability
import Mathlib.Algebra.Category.Ring.FinitePresentation
@[expose] public section
open CategoryTheory
open Algebra
open scoped nonZeroDivisors
universe u v

private noncomputable def forgetRingIsColimit
    (A : Type u) [CommRing A] {I : Type (max u v)} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{max u v} A) (c : Limits.Cocone B) (hc : Limits.IsColimit c) :
    Limits.IsColimit ((forget₂ (CommAlgCat A) CommRingCat).mapCocone c) := by
  classical
  let U := forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let i : I := Classical.choice IsFiltered.nonempty
  have comm (s : Limits.Cocone (B ⋙ U)) (j : I) (a : A) :
      (s.ι.app j).hom (algebraMap A (B.obj j) a) =
        (s.ι.app i).hom (algebraMap A (B.obj i) a) := by
    let k := IsFiltered.max i j
    have hi := ConcreteCategory.congr_hom (s.w (IsFiltered.leftToMax i j))
      (algebraMap A (B.obj i) a)
    have hj := ConcreteCategory.congr_hom (s.w (IsFiltered.rightToMax i j))
      (algebraMap A (B.obj j) a)
    change (s.ι.app k).hom ((B.map _).hom (algebraMap A (B.obj i) a)) = _ at hi
    change (s.ι.app k).hom ((B.map _).hom (algebraMap A (B.obj j) a)) = _ at hj
    simp only [AlgHom.commutes] at hi hj
    exact hj.symm.trans hi
  let liftCocone (s : Limits.Cocone (B ⋙ U)) : Limits.Cocone B :=
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    { pt := CommAlgCat.of A s.pt
      ι :=
        { app := fun j ↦ CommAlgCat.ofHom
            { __ := (s.ι.app j).hom
              commutes' := comm s j }
          naturality := by
            intro j k f
            ext x
            exact ConcreteCategory.congr_hom (s.w f) x } }
  let desc (s : Limits.Cocone (B ⋙ U)) := U.map (hc.desc (liftCocone s))
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    exact congrArg (fun f ↦ U.map f) (hc.fac (liftCocone s) j)
  · intro s m hm
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    let ma : c.pt ⟶ (liftCocone s).pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' := by
          intro a
          have h := ConcreteCategory.congr_hom (hm i) (algebraMap A (B.obj i) a)
          change m.hom ((c.ι.app i).hom (algebraMap A (B.obj i) a)) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a) at h
          simp only [AlgHom.commutes] at h
          change m.hom (algebraMap A ↥(c.pt) a) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a)
          exact h }
    have he : ma = hc.desc (liftCocone s) := by
      apply hc.hom_ext
      intro j
      rw [hc.fac]
      ext x
      exact ConcreteCategory.congr_hom (hm j) x
    exact congrArg (fun f ↦ U.map f) he



set_option backward.isDefEq.respectTransparency false in
/-- The field hypothesis gives a smooth factorization after localizing at nonzerodivisors.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F5, third paragraph
(blueprint: lem-weil-pbc-popescu-standard-nonzerodivisor-aux).

Proof: Put S = R⁰ and Q = S⁻¹R. Since R is reduced and Noetherian, its total fraction
ring is a finite product of its localizations at minimal primes, which are fields.
Since R is nonzero there is at least one minimal prime. Each such localization is
canonically its residue field. Localization is base change, and tensor product
commutes with finite products, so S⁻¹Λ is the corresponding product of the fibres
Λᵢ = κ(qᵢ) ⊗[R] Λ. Each Λᵢ is Noetherian: it is a quotient of a localization of Λ.
Regularity of R → Λ says these fibres are geometrically regular. The map κ(qᵢ) → Λᵢ
is flat because its base is a field, and its sole fibre is Λᵢ itself, so it is regular.
The hypothesis therefore supplies a filtered colimit of smooth algebras for each Λᵢ.
Iterating `Algebra.ind_smooth_prod` gives such a colimit for their product over Q,
transported along the canonical product identifications. Finite presentation survives
base change, so S⁻¹A is finitely presented over Q. The finite-presentation factorization
lemma applied to S⁻¹α into this filtered colimit gives one smooth term B', a map β'
into it and its colimit coprojection γ', with γ'β' = S⁻¹α. The diagram and its terms
are in universe max u v, so B' has exactly the universe required here. The equality
of underlying ring homomorphisms expresses this same factorization. -/
theorem exists_localized_smooth_factorization
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) :
    ∃ (B' : Type (max u v)) (_ : CommRing B')
      (_ : Algebra (Localization R⁰) B') (_ : Algebra.Smooth (Localization R⁰) B')
      (β' : Localization (Algebra.algebraMapSubmonoid A R⁰) →ₐ[Localization R⁰] B')
      (γ' : B' →ₐ[Localization R⁰]
        Localization (Algebra.algebraMapSubmonoid Λ R⁰)),
      γ'.toRingHom.comp β'.toRingHom =
        IsLocalization.map (Localization (Algebra.algebraMapSubmonoid Λ R⁰))
          α.toRingHom (Algebra.algebraMapSubmonoid_le_comap R⁰ α) := by
  classical
  let Q := Localization R⁰
  let C := Localization (Algebra.algebraMapSubmonoid A R⁰)
  let L := Localization (Algebra.algebraMapSubmonoid Λ R⁰)
  let : IsScalarTower R Q C :=
    isScalarTower_localizationAlgebra (Rₘ := Q) (Sₘ := C) R⁰ A
  let : IsScalarTower R Q L :=
    isScalarTower_localizationAlgebra (Rₘ := Q) (Sₘ := L) R⁰ Λ
  let : Algebra.FinitePresentation Q C :=
    Algebra.FinitePresentation.equiv (R := Q) (A := TensorProduct R Q A)
      (Localization.tensorRightAlgEquiv R⁰ A)
  let fr : C →+* L := IsLocalization.map L α.toRingHom
    (Algebra.algebraMapSubmonoid_le_comap R⁰ α)
  have hfr : fr.comp (algebraMap Q C) = algebraMap Q L := by
    apply IsLocalization.ringHom_ext R⁰
    ext r
    change fr (algebraMap Q C (algebraMap R Q r)) =
      algebraMap Q L (algebraMap R Q r)
    rw [← IsScalarTower.algebraMap_apply R Q C,
      ← IsScalarTower.algebraMap_apply R Q L,
      IsScalarTower.algebraMap_apply R A C]
    change IsLocalization.map L α.toRingHom _ (algebraMap A C (algebraMap R A r)) = _
    rw [IsLocalization.map_eq]
    change algebraMap Λ L (α (algebraMap R A r)) = algebraMap R L r
    rw [α.commutes, ← IsScalarTower.algebraMap_apply R Λ L]
  let f : C →ₐ[Q] L := { __ := fr, commutes' := RingHom.congr_fun hfr }
  obtain ⟨J, _, _, pres, hsm⟩ := localized_target_is_ind_smooth h R Λ hreg
  let U := forget₂ (CommAlgCat.{max u v} Q) CommRingCat.{max u v}
  let T := ULift.{max u v} Q
  let e : T ≃+* Q := ULift.ringEquiv
  let a : (Functor.const J).obj (CommRingCat.of T) ⟶ pres.diag ⋙ U :=
    { app := fun j ↦ CommRingCat.ofHom ((algebraMap Q (pres.diag.obj j)).comp e.toRingHom)
      naturality := by
        intro i j g
        ext x
        exact ((pres.diag.map g).hom.commutes (e x)).symm }
  let c := U.mapCocone pres.cocone
  have hc := forgetRingIsColimit Q pres.diag pres.cocone pres.isColimit
  have hfp : ((algebraMap Q C).comp e.toRingHom).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (RingHom.FinitePresentation.of_bijective e.bijective)
  obtain ⟨j, b, hb, hfac⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of T) (pres.diag ⋙ U) a
    (CommRingCat.ofHom ((algebraMap Q C).comp e.toRingHom)) c hc hfp
    (CommRingCat.ofHom f.toRingHom) (by
      intro j
      ext x
      exact (f.commutes (e x)).trans ((pres.ι.app j).hom.commutes (e x)).symm)
  let β : C →ₐ[Q] pres.diag.obj j :=
    { __ := b.hom
      commutes' := by
        intro q
        have hx := congrArg (fun g ↦ g.hom (e.symm q)) hb
        change b.hom (algebraMap Q C (e (e.symm q))) =
          algebraMap Q (pres.diag.obj j) (e (e.symm q)) at hx
        rw [e.apply_symm_apply] at hx
        change b.hom (algebraMap Q C q) = algebraMap Q (pres.diag.obj j) q
        exact hx }
  refine ⟨pres.diag.obj j, inferInstance, inferInstance, hsm j,
    β, (pres.ι.app j).hom, ?_⟩
  exact congrArg CommRingCat.Hom.hom hfac.symm
