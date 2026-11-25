/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.LimitModuleRingData
import WeilConjectures.RingTheory.LocalizedPushoutTensor
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.Algebra.LimitFinitePresentation.Colimits
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.FiniteType
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
/-!
# Polynomial-quotient descent with localization base change
Source: Stacks Project, Algebra, Tag 00QV, as used in Tag 00QX.
(blueprint: lem-limit-module-localization-ring-data)
-/
@[expose] public section
universe u p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom
private theorem localizedSystem
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) (T : CommRingCat.{u}) [IsLocalRing T]
    (g : (colimit D : CommRingCat.{u}) →+* T) (W : Submonoid (colimit D : CommRingCat.{u}))
    (hT : letI := g.toAlgebra; IsLocalization W T) :
    ∃ (B : J ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T) (ιB : D ⟶ B),
      Nonempty (IsColimit (Cocone.mk T β)) ∧
      (∀ i, (ιB.app i).hom.EssFiniteType) ∧
      (∀ i, IsLocalHom (β.app i).hom) ∧
      (∀ i, (β.app i).hom.comp (ιB.app i).hom = g.comp (colimit.ι D i).hom) ∧
      (∀ i, letI := (ιB.app i).hom.toAlgebra
        IsLocalization
          (Ideal.comap (g.comp (colimit.ι D i).hom)
            (IsLocalRing.maximalIdeal T)).primeCompl (B.obj i)) := by
  classical
  let := g.toAlgebra
  have : IsLocalization W T := hT
  let q : Ideal (colimit D : CommRingCat.{u}) := Ideal.comap g (IsLocalRing.maximalIdeal T)
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hqT : IsLocalization q.primeCompl T := by
    apply IsLocalization.of_le W q.primeCompl
    · intro x hx
      change ¬ g x ∈ IsLocalRing.maximalIdeal T
      exact fun hn ↦ hn (IsLocalization.map_units T ⟨x, hx⟩)
    · intro x hx
      change ¬ ¬ IsUnit (g x) at hx
      exact not_not.mp hx
  let e : Localization.AtPrime q ≃ₐ[(colimit D : CommRingCat.{u})] T :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T
  obtain ⟨_, _, B, hB, hnat, s, hs, hcompat, ⟨hcol⟩⟩ :=
    AlgebraicGeometry.filteredColimitLocalizationAtPrime D q
  let qi (i : J) : Ideal (D.obj i) := Ideal.comap (colimit.ι D i).hom q
  let ei (i : J) : B.obj i ≅ CommRingCat.of (Localization.AtPrime (qi i)) :=
    eqToIso (hB i)
  let j : s.pt ≅ T := eqToIso hs ≪≫ e.toRingEquiv.toCommRingCatIso
  let β : B ⟶ (Functor.const J).obj T := (s.extend j.hom).ι
  let ιB : D ⟶ B :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (D.obj i)
          (Localization.AtPrime (qi i))) ≫ (ei i).inv
      naturality := by
        intro i k a
        simpa only [ei, eqToIso.inv, Category.assoc] using (hnat i k a).symm }
  have hcomp (i : J) :
      (β.app i).hom.comp (ιB.app i).hom = g.comp (colimit.ι D i).hom := by
    ext x
    have h := ConcreteCategory.congr_hom (hcompat i) x
    change e ((eqToHom hs).hom ((s.ι.app i).hom
      ((ei i).inv.hom (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x)))) = _
    change (eqToHom hs).hom ((s.ι.app i).hom
      ((ei i).inv.hom (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x))) =
        algebraMap (colimit D : CommRingCat.{u}) (Localization.AtPrime q)
          ((colimit.ι D i).hom x) at h
    rw [h, e.commutes]
    rfl
  refine ⟨B, β, ιB, ⟨hcol.extendIso j.hom⟩, ?_, ?_, hcomp, ?_⟩
  · intro i
    have hloc : (algebraMap (D.obj i) (Localization.AtPrime (qi i))).EssFiniteType :=
      essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _ (qi i).primeCompl)
    exact hloc.comp (FiniteType.of_surjective (ei i).inv.hom
      (ei i).symm.commRingCatIsoToRingEquiv.surjective).essFiniteType
  · intro i
    let li : Localization.AtPrime (qi i) →+* Localization.AtPrime q :=
      Localization.localRingHom (qi i) q (colimit.ι D i).hom rfl
    have hli : IsLocalHom li :=
      Localization.isLocalHom_localRingHom (qi i) q (colimit.ι D i).hom rfl
    have he : IsLocalHom e.toRingHom :=
      isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
    have hei : IsLocalHom (ei i).hom.hom :=
      isLocalHom_of_leftInverse (ei i).inv.hom
        (ei i).commRingCatIsoToRingEquiv.left_inv
    have hb : (β.app i).hom = e.toRingHom.comp (li.comp (ei i).hom.hom) := by
      have hb' : (β.app i).hom.comp (ei i).inv.hom = e.toRingHom.comp li := by
        apply IsLocalization.ringHom_ext (qi i).primeCompl
        ext x
        have hx := DFunLike.congr_fun (hcomp i) x
        change (β.app i).hom ((ei i).inv.hom
          (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x)) = _ at hx
        change _ = e (li (algebraMap (D.obj i) (Localization.AtPrime (qi i)) x))
        rw [Localization.localRingHom_to_map, e.commutes]
        exact hx
      ext x
      have hx := DFunLike.congr_fun hb' ((ei i).hom.hom x)
      change (β.app i).hom ((ei i).inv.hom ((ei i).hom.hom x)) =
        e (li ((ei i).hom.hom x)) at hx
      have hi : (ei i).inv.hom ((ei i).hom.hom x) = x :=
        (ei i).commRingCatIsoToRingEquiv.left_inv x
      rw [hi] at hx
      exact hx
    rw [hb]
    infer_instance
  · intro i
    let := (ιB.app i).hom.toAlgebra
    have : (qi i).IsPrime := Ideal.IsPrime.comap _
    let e' : Localization.AtPrime (qi i) ≃ₐ[D.obj i] B.obj i :=
      { (ei i).symm.commRingCatIsoToRingEquiv with
        commutes' := fun x ↦ rfl }
    change IsLocalization (qi i).primeCompl (B.obj i)
    exact IsLocalization.isLocalization_of_algEquiv (qi i).primeCompl e'

private theorem presentationSystem
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (Q : CommRingCat.{u}) (aQ : c.pt →+* Q) (hfp : aQ.FinitePresentation) :
    ∃ i₀ : I, ∃ D : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u},
      ∃ (σ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* D.obj i)
        (e : (colimit D : CommRingCat.{u}) ≃+* Q),
        (∀ i, (σ i).FiniteType) ∧
        (∀ i, e.toRingHom.comp ((colimit.ι D i).hom.comp (σ i)) =
          aQ.comp (c.ι.app i.1).hom) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
          (D.map (homOfLE h)).hom.comp (σ i) =
            (σ j).comp (F.map (homOfLE h)).hom) ∧
        (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
          IsPushout (CommRingCat.ofHom (σ i)) (F.map (homOfLE h))
            (D.map (homOfLE h)) (CommRingCat.ofHom (σ j))) ∧
        (∀ i, IsPushout (CommRingCat.ofHom (σ i)) (c.ι.app i.1)
          (colimit.ι D i) (CommRingCat.ofHom (e.symm.toRingHom.comp aQ))) := by
  classical
  obtain ⟨i₀, Q₀, g₀, hg₀, k₀, hp⟩ :=
    CommRingCat.exists_isPushout_of_finitePresentation F c hc
      (CommRingCat.ofHom aQ) hfp
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let U : J ⥤ I :=
    { obj := fun i ↦ i.val
      map := fun {i j} h ↦ homOfLE (show i ≤ j from leOfHom h) }
  have : U.Final := by
    change (Subtype.mono_coe (p := fun i ↦ i₀ ≤ i)).functor.Final
    apply (Subtype.mono_coe _).final_functor_iff.mpr
    intro i
    obtain ⟨j, hij, h₀j⟩ := exists_ge_ge i i₀
    exact ⟨⟨j, h₀j⟩, hij⟩
  let a (i : J) : F.obj i₀ ⟶ F.obj i.1 := F.map (homOfLE i.property)
  have ha {i j : J} (h : i ⟶ j) : a i ≫ F.map (U.map h) = a j := by
    rw [← F.map_comp]
    rfl
  have hac (i : J) : a i ≫ c.ι.app i.1 = c.ι.app i₀ := c.w _
  let D : J ⥤ CommRingCat.{u} :=
    { obj := fun i ↦ pushout (a i) g₀
      map := fun {i j} h ↦ pushout.desc
        (F.map (U.map h) ≫ pushout.inl (a j) g₀) (pushout.inr (a j) g₀) (by
          rw [← Category.assoc, ha, pushout.condition])
      map_id := by
        intro i
        apply pushout.hom_ext
        · simp only [pushout.inl_desc, U.map_id, Category.comp_id]
          change F.map (𝟙 i.val) ≫ pushout.inl (a i) g₀ = pushout.inl (a i) g₀
          rw [F.map_id, Category.id_comp]
        · simp
      map_comp := by intro i j k h h'; apply pushout.hom_ext <;> simp [Category.assoc] }
  let η : U ⋙ F ⟶ D :=
    { app := fun i ↦ pushout.inl (a i) g₀
      naturality := by intro i j h; simp [D] }
  let d : Cocone D :=
    { pt := Q
      ι :=
        { app := fun i ↦ pushout.desc (c.ι.app i.1 ≫ CommRingCat.ofHom aQ) k₀ (by
            rw [← Category.assoc, hac, hp.w])
          naturality := by
            intro i j h
            apply pushout.hom_ext
            · dsimp only [D, Functor.const_obj_map]
              rw [← Category.assoc, pushout.inl_desc, Category.assoc, pushout.inl_desc]
              erw [Category.comp_id, pushout.inl_desc]
              rw [← Category.assoc, c.w]
            · simp [D] } }
  have hfinal (i : J) : IsPushout (η.app i) (c.ι.app i.1) (d.ι.app i)
      (CommRingCat.ofHom aQ) := by
    apply IsPushout.of_top (t := (IsPushout.of_hasPushout (a i) g₀).flip)
      (p := by simp [d])
    simpa [d, hac] using hp.flip
  have hd : IsColimit d :=
    (Algebra.colimits_of_limit_finite_presentation_core η (c.whisker U) d
      (CommRingCat.ofHom aQ) (fun i ↦ ⟨hfinal i⟩)
      ((Functor.Final.isColimitWhiskerEquiv U c).symm hc)).some
  let eIso : (colimit D : CommRingCat.{u}) ≅ Q :=
    (colimit.isColimit D).coconePointUniqueUpToIso hd
  let e := eIso.commRingCatIsoToRingEquiv
  have he (i : J) : colimit.ι D i ≫ eIso.hom = d.ι.app i :=
    (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hd i
  refine ⟨i₀, D, (fun i ↦ (η.app i).hom), e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact RingHom.finiteType_isStableUnderBaseChange.pushout_inl
      RingHom.finiteType_respectsIso (a i) g₀ (RingHom.FiniteType.of_finitePresentation hg₀)
  · intro i
    have hh : η.app i ≫ colimit.ι D i ≫ eIso.hom =
        c.ι.app i.1 ≫ CommRingCat.ofHom aQ := by
      rw [he]
      exact (hfinal i).w
    exact congrArg CommRingCat.Hom.hom hh
  · intro i j h
    exact congrArg CommRingCat.Hom.hom (η.naturality (homOfLE h)).symm
  · intro i j h
    apply IsPushout.flip
    apply IsPushout.of_left (t := IsPushout.of_hasPushout (a i) g₀)
      (p := η.naturality (homOfLE h))
    simpa [η, D, ha] using IsPushout.of_hasPushout (a j) g₀
  · intro i
    apply (hfinal i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eIso.symm
    · simp
    · simp
    · dsimp only [Iso.refl_hom, Iso.symm_hom]
      rw [Category.id_comp, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · ext x
      rfl

/-- Descend a localized finitely presented algebra with its ring base-change properties.
Source: Stacks Project, Algebra, Tag 00QV (proof) and Tag 00QX (ring construction).
Proof: Replace the given localization of P by localization at the inverse image of
T's maximal ideal; since T is local this gives the same ring. Write P as a finite
polynomial quotient. Lift the finitely many coefficients of its defining relations
along the given colimit to a common index i₀. At each later index take that polynomial
quotient over F(i), and localize it at the inverse image of T's maximal ideal.
The contraction to F(i) is maximal because the maps F(i) → c.pt → T are local.
Hence these rings and their structure, transition and limit maps are local; their
structure maps are essentially of finite type. Maps of polynomials carry the lifted
relations to the later relations and induce the required naturality and composition.
Polynomial and quotient base change give the unlocalized scalar-extension identities.
Base change of localization followed by localization at the contracted prime proves
both displayed localization predicates, with the canonical pure-tensor formulas.
For the ring colimit, lift the finitely many numerator and denominator coefficients
of any element to a stage; denominators outside the prime remain outside its inverse
image. A fraction mapping to zero has a finite ideal-membership witness after
multiplication by a denominator. Lift that witness and its finitely many equalities
to a later stage, so the fraction is zero there. These two properties give the
colimit universal property. The tail is cofinal by directedness.
(blueprint: lem-limit-module-localization-ring-data) -/
theorem exists_limit_module_localization_ring_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              letI := (τ₀ i).toAlgebra
              letI := (F.map (homOfLE h)).hom.toAlgebra
              (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
                (∀ (x : B.obj i) (y : F.obj j.1),
                  φ (x ⊗ₜ[F.obj i.1] y) =
                    (B.map (homOfLE h)).hom x * τ₀ j y) ∧
                (letI := φ.toAlgebra
                 ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
                   IsLocalization U (B.obj j)))) ∧
            (∀ i : {i : I // i₀ ≤ i},
              letI := (τ₀ i).toAlgebra
              letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
              (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
                (∀ (x : B.obj i) (y : c.pt),
                  φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
                (letI := φ.toAlgebra
                 ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T))) := by
  classical
  have _ := hF
  have : Small.{u} P := Algebra.FiniteType.small (R := c.pt) (S := P)
  let Q := Shrink.{u} P
  let r : Q ≃ₐ[c.pt] P := Shrink.algEquiv c.pt P
  have : Algebra.FinitePresentation c.pt Q := Algebra.FinitePresentation.equiv r.symm
  let aQ : c.pt →+* Q := algebraMap c.pt Q
  let fQ : Q →+* T := f.comp r.toRingHom
  have hfQ : fQ.comp aQ = τ := by
    ext x
    change f (r (algebraMap c.pt Q x)) = τ x
    rw [r.commutes]
    exact DFunLike.congr_fun hf x
  have hTQ : letI := fQ.toAlgebra; IsLocalization (W.map r.symm.toMonoidHom) T := by
    let := f.toAlgebra
    let := fQ.toAlgebra
    have : IsLocalization W T := hT
    apply IsLocalization.of_ringEquiv_left (M₁ := W)
      (M₂ := W.map r.symm.toMonoidHom) r.toRingEquiv
    · ext x
      simp
    · intro x
      rfl
  obtain ⟨i₀, D, σ, e, hσfinite, hσcomp, hσnat, hpush, hfinal⟩ :=
    presentationSystem F c hc (CommRingCat.of Q) aQ
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let g : (colimit D : CommRingCat.{u}) →+* T := fQ.comp e.toRingHom
  let V := (W.map r.symm.toMonoidHom).map e.symm.toMonoidHom
  have hV : letI := g.toAlgebra; IsLocalization V T := by
    let := fQ.toAlgebra
    let := g.toAlgebra
    have : IsLocalization (W.map r.symm.toMonoidHom) T := hTQ
    apply IsLocalization.of_ringEquiv_left (M₁ := W.map r.symm.toMonoidHom)
      (M₂ := V) e
    · ext x
      simp [V]
    · intro x
      rfl
  obtain ⟨B, β, ιB, hcol, hιBfinite, hβlocal, hιBcomp, hιBloc⟩ :=
    localizedSystem D T g V hV
  let τ₀ (i : J) : F.obj i.1 →+* B.obj i := (ιB.app i).hom.comp (σ i)
  have hcomp (i : J) :
      (β.app i).hom.comp (τ₀ i) = τ.comp (c.ι.app i.1).hom := by
    change (β.app i).hom.comp ((ιB.app i).hom.comp (σ i)) = _
    rw [← RingHom.comp_assoc, hιBcomp]
    change fQ.comp (e.toRingHom.comp ((colimit.ι D i).hom.comp (σ i))) = _
    rw [hσcomp, ← RingHom.comp_assoc, hfQ]
  let q (i : J) : Ideal (D.obj i) :=
    Ideal.comap (g.comp (colimit.ι D i).hom) (IsLocalRing.maximalIdeal T)
  let qL : Ideal (colimit D : CommRingCat.{u}) :=
    Ideal.comap g (IsLocalRing.maximalIdeal T)
  have hqL : letI := g.toAlgebra; IsLocalization qL.primeCompl T := by
    let := g.toAlgebra
    have : IsLocalization V T := hV
    apply IsLocalization.of_le V qL.primeCompl
    · intro x hx
      change ¬ g x ∈ IsLocalRing.maximalIdeal T
      exact fun hn ↦ hn (IsLocalization.map_units T ⟨x, hx⟩)
    · intro x hx
      change ¬ ¬ IsUnit (g x) at hx
      exact not_not.mp hx
  refine ⟨i₀, B, β, hcol, (fun i ↦ (β.app i).hom), (fun _ _ ↦ rfl), ?_,
    hβlocal, ?_, τ₀, ?_, ?_, hcomp, ?_, ?_, ?_⟩
  · intro i
    have : IsLocalHom (β.app i).hom := hβlocal i
    exact (show B.obj i →+* T from (β.app i).hom).domain_isLocalRing
  · intro i j h
    have : IsLocalHom (β.app i).hom := hβlocal i
    have hnat := congrArg CommRingCat.Hom.hom (β.naturality (homOfLE h))
    change (β.app j).hom.comp (B.map (homOfLE h)).hom = (β.app i).hom at hnat
    have : IsLocalHom ((β.app j).hom.comp (B.map (homOfLE h)).hom) := by
      rw [hnat]
      infer_instance
    exact isLocalHom_of_comp (B.map (homOfLE h)).hom (β.app j).hom
  · intro i
    have : IsLocalHom (c.ι.app i.1).hom := hcLocal i.1
    have : IsLocalHom ((β.app i).hom.comp (τ₀ i)) := by
      rw [hcomp]
      infer_instance
    exact isLocalHom_of_comp (τ₀ i) (β.app i).hom
  · intro i
    exact (hσfinite i).essFiniteType.comp (hιBfinite i)
  · intro i j h
    change (B.map (homOfLE h)).hom.comp ((ιB.app i).hom.comp (σ i)) = _
    have hnat := congrArg CommRingCat.Hom.hom (ιB.naturality (homOfLE h))
    change (ιB.app j).hom.comp (D.map (homOfLE h)).hom =
      (B.map (homOfLE h)).hom.comp (ιB.app i).hom at hnat
    rw [← RingHom.comp_assoc, ← hnat, RingHom.comp_assoc, hσnat]
    rfl
  · intro i j h
    have hn : (q i).primeCompl.map (D.map (homOfLE h)).hom ≤ (q j).primeCompl := by
      rintro x ⟨y, hy, rfl⟩
      change ¬ g ((colimit.ι D j).hom ((D.map (homOfLE h)).hom y)) ∈
        IsLocalRing.maximalIdeal T
      have he : (colimit.ι D j).hom ((D.map (homOfLE h)).hom y) =
          (colimit.ι D i).hom y :=
        ConcreteCategory.congr_hom (colimit.w D (homOfLE h)) y
      rw [he]
      exact hy
    have hm := congrArg CommRingCat.Hom.hom (ιB.naturality (homOfLE h))
    obtain ⟨φ, hφ, hloc⟩ := exists_localized_pushout_tensor (F.obj i.1) (D.obj i)
      (F.obj j.1) (D.obj j) (B.obj i) (B.obj j) (σ i)
      (F.map (homOfLE h)).hom (D.map (homOfLE h)).hom (σ j) (hpush i j h)
      (ιB.app i).hom (ιB.app j).hom (B.map (homOfLE h)).hom hm.symm
      (q i).primeCompl (q j).primeCompl hn (hιBloc i) (hιBloc j)
    exact ⟨φ, hφ, hloc⟩
  · intro i
    have hn : (q i).primeCompl.map (colimit.ι D i).hom ≤ qL.primeCompl := by
      rintro x ⟨y, hy, rfl⟩
      exact hy
    have hb : g.comp (e.symm.toRingHom.comp aQ) = τ := by
      ext x
      change fQ (e (e.symm (aQ x))) = τ x
      rw [e.apply_symm_apply]
      exact DFunLike.congr_fun hfQ x
    obtain ⟨φ, hφ, hloc⟩ := exists_localized_pushout_tensor (F.obj i.1) (D.obj i)
      c.pt (colimit D) (B.obj i) T (σ i) (c.ι.app i.1).hom
      (colimit.ι D i).hom (e.symm.toRingHom.comp aQ) (hfinal i)
      (ιB.app i).hom g (β.app i).hom (hιBcomp i)
      (q i).primeCompl qL.primeCompl hn (hιBloc i) hqL
    refine ⟨φ, ?_, hloc⟩
    intro x y
    rw [hφ]
    exact congrArg ((β.app i).hom x * ·) (DFunLike.congr_fun hb y)
end RingHom
