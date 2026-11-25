/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Localized additive comparison
Source: Stacks Project, Algebra, Tag 02JO first paragraph and Tag 037D.
(blueprint: lem-pc-localized-module-colimit-comparison) -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Lift representatives after enlarging the additive-group universe. -/
private theorem additive_colimit_rep
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ AddCommGrpCat.{v}) (c : Cocone D) (hc : IsColimit c) (x : c.pt) :
    ∃ (i : Λ) (y : D.obj i), c.ι.app i y = x := by
  -- The lifted forgetful functor preserves colimits of this indexing size.
  let U := AddCommGrpCat.uliftFunctor.{u, v}
  let : IsFiltered Λ := inferInstance
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u v}) := preservesFilteredColimitsOfSize_shrink _
  have h := isColimitOfPreserves U hc
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep (D ⋙ U) h (ULift.up x)
  exact ⟨i, y.down, congrArg ULift.down hy⟩

/-- Detect zero at a stage, including diagrams larger than their group universe. -/
private theorem additive_colimit_zero
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ AddCommGrpCat.{v}) (c : Cocone D) (hc : IsColimit c)
    (i : Λ) (x : D.obj i) (hx : c.ι.app i x = 0) :
    ∃ (j : Λ) (f : i ⟶ j), D.map f x = 0 := by
  -- The lifted forgetful functor preserves colimits of this indexing size.
  let U := AddCommGrpCat.uliftFunctor.{u, v}
  let : IsFiltered Λ := inferInstance
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{max u v}) := preservesFilteredColimitsOfSize_shrink _
  have h := isColimitOfPreserves U hc
  have he : (U.mapCocone c).ι.app i (ULift.up x) =
      (U.mapCocone c).ι.app i (ULift.up (0 : D.obj i)) := by
    change ULift.up (c.ι.app i x) = ULift.up (c.ι.app i 0)
    exact congrArg ULift.up (hx.trans (map_zero (c.ι.app i).hom).symm)
  obtain ⟨j, f, g, hj⟩ :=
    Concrete.isColimit_exists_of_rep_eq (D ⋙ U) h (ULift.up x) (ULift.up 0) he
  refine ⟨j, f, ?_⟩
  have he' := congrArg ULift.down hj
  change (D.map f).hom x = (D.map g).hom 0 at he'
  exact he'.trans (map_zero _)

/-- Additive comparison for localization of a semilinear filtered diagram.
Source: Stacks Project, Algebra, Tag 02JO first paragraph and Tag 037D.
(blueprint: lem-pc-localized-module-colimit-comparison)
Proof: Lift the numerator of a fraction in M through D and its denominator through B,
then pass to a common upper bound. The denominator remains outside the contracted prime,
so the fraction lifts to N. For equality, lift a multiplier outside q witnessing the zero
cross difference and pass to a common stage. Semilinearity ensures that the cross difference
there maps to zero in M. The original additive colimit detects this zero at a later stage.
The multiplier remains outside the prime, so the localized fractions agree at that stage.
The stipulated transition and fraction formulas therefore give a bijective comparison
from the colimit of N. Addition is respected at common stages; the comparison is an
additive equivalence with the stated coprojection formula. -/
theorem exists_colimit_addEquiv_localizedModule
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] {M : Type v} [AddCommGroup M] [Module T M]
    (B : Λ ⥤ CommRingCat.{u}) (D : Λ ⥤ AddCommGrpCat.{v})
    (N : Λ ⥤ AddCommGrpCat.{max u v})
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i, Module (B.obj i) (D.obj i)]
    (hB : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (hD : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)))
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hν : ∀ i (b : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (b • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) b •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (q : PrimeSpectrum T)
    (eᵢ : ∀ i, N.obj i ≃+
      LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i)
      (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      ∃ t : (q.asIdeal.comap (κ.app j).hom).primeCompl,
        (t : B.obj j) = (B.map f).hom s ∧
        eᵢ j ((N.map f).hom ((eᵢ i).symm (LocalizedModule.mk x s))) =
          LocalizedModule.mk ((D.map f).hom x) t)
    (g : ∀ i, N.obj i →+ LocalizedModule q.asIdeal.primeCompl M)
    (hg : ∀ i (x : D.obj i) (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      g i ((eᵢ i).symm (LocalizedModule.mk x s)) =
        LocalizedModule.mk
          ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
          ⟨(@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) s, s.property⟩) :
    ∃ e : (colimit N : AddCommGrpCat.{max u v}) ≃+
      LocalizedModule q.asIdeal.primeCompl M,
      ∀ i (z : N.obj i), e ((colimit.ι N i).hom z) = g i z := by
  classical
  let νf (i : Λ) : D.obj i →+ M :=
    @AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)
  let κf (i : Λ) : B.obj i →+* T :=
    @CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)
  let : IsFiltered Λ := inferInstance
  let : PreservesFilteredColimitsOfSize.{u, u}
      (forget CommRingCat.{u}) := inferInstance
  have hκ (i j : Λ) (f : i ⟶ j) (b : B.obj i) :
      (κf j) ((B.map f).hom b) = (κf i) b :=
    ConcreteCategory.congr_hom (κ.naturality f) b
  have hνn (i j : Λ) (f : i ⟶ j) (x : D.obj i) :
      (νf j) ((D.map f).hom x) = (νf i) x :=
    ConcreteCategory.congr_hom (ν.naturality f) x
  -- The fraction formulas and cocone naturality make the localized maps compatible.
  have hgn (i j : Λ) (f : i ⟶ j) (z : N.obj i) :
      g j ((N.map f).hom z) = g i z := by
    obtain ⟨x, s, hz⟩ : ∃ x s, (eᵢ i).symm (LocalizedModule.mk x s) = z := by
      have hrep : ∀ w : LocalizedModule
          (q.asIdeal.comap (κf i)).primeCompl (D.obj i),
          ∃ x s, LocalizedModule.mk x s = w := by
        intro w
        induction w using LocalizedModule.induction_on with
        | h x s => exact ⟨x, s, rfl⟩
      obtain ⟨x, s, he⟩ := hrep (eᵢ i z)
      exact ⟨x, s, by rw [he]; exact (eᵢ i).symm_apply_apply z⟩
    rw [← hz]
    obtain ⟨t, ht, he⟩ := hm i j f x s
    have hmap : (N.map f).hom ((eᵢ i).symm (LocalizedModule.mk x s)) =
        (eᵢ j).symm (LocalizedModule.mk ((D.map f).hom x) t) := by
      exact (eᵢ j).injective (by simpa using he)
    rw [hmap, hg, hg]
    congr 1
    · exact hνn i j f x
    · apply Subtype.ext
      change (κf j) (t : B.obj j) = (κf i) (s : B.obj i)
      rw [ht]
      exact hκ i j f s
  let c : Cocone N := Cocone.mk
    (AddCommGrpCat.of (LocalizedModule q.asIdeal.primeCompl M))
    { app := fun i => AddCommGrpCat.ofHom (g i)
      naturality := by
        intro i j f
        ext z
        exact hgn i j f z }
  let d := (colimit.desc N c).hom
  have hd (i : Λ) (z : N.obj i) : d ((colimit.ι N i).hom z) = g i z :=
    ConcreteCategory.congr_hom (colimit.ι_desc c i) z
  -- Lift numerator and denominator separately, then move both to a common stage.
  have hsurj : Function.Surjective d := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h x s =>
      obtain ⟨i, y, hy⟩ := additive_colimit_rep D _ hD.some x
      obtain ⟨j, b, hb⟩ := Concrete.isColimit_exists_rep B hB.some (s : T)
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let f : i ⟶ k := homOfLE hik
      let f' : j ⟶ k := homOfLE hjk
      have hs' : (κf k) ((B.map f').hom b) = (s : T) := by
        exact (hκ j k f' b).trans hb
      let t : (q.asIdeal.comap (κf k)).primeCompl :=
        ⟨(B.map f').hom b, by change (κf k) _ ∉ q.asIdeal; rw [hs']; exact s.property⟩
      refine ⟨(colimit.ι N k).hom ((eᵢ k).symm
        (LocalizedModule.mk ((D.map f).hom y) t)), ?_⟩
      rw [hd, hg]
      congr 1
      · exact (hνn i k f y).trans hy
      · exact Subtype.ext hs'
  have hzero (i : Λ) (z : N.obj i) (hz : g i z = 0) :
      (colimit.ι N i).hom z = 0 := by
    have hrep : ∀ w : LocalizedModule
        (q.asIdeal.comap (κf i)).primeCompl (D.obj i),
        ∃ x s, LocalizedModule.mk x s = w := by
      intro w
      induction w using LocalizedModule.induction_on with
      | h x s => exact ⟨x, s, rfl⟩
    obtain ⟨x, s, he⟩ := hrep (eᵢ i z)
    have hzrep : (eᵢ i).symm (LocalizedModule.mk x s) = z := by
      rw [he]
      exact (eᵢ i).symm_apply_apply z
    rw [← hzrep, hg] at hz
    rw [← LocalizedModule.zero_mk (1 : q.asIdeal.primeCompl),
      LocalizedModule.mk_eq] at hz
    obtain ⟨a, ha⟩ := hz
    -- A zero fraction has a multiplier outside the prime annihilating its numerator.
    have ha' : (a : T) • ((νf i) x : M) = 0 := by
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, smul_zero] using ha
    obtain ⟨j, b, hb⟩ := Concrete.isColimit_exists_rep B hB.some (a : T)
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let f : i ⟶ k := homOfLE hik
    let f' : j ⟶ k := homOfLE hjk
    let b' : B.obj k := (B.map f').hom b
    let x' : D.obj k := (D.map f).hom x
    have hb' : (κf k) b' = (a : T) := (hκ j k f' b).trans hb
    have hx' : (νf k) (b' • x') = 0 := by
      calc
        (νf k) (b' • x') =
            (κf k) b' • ((νf k) x' : M) := hν k b' x'
        _ = (a : T) • ((νf i) x : M) :=
          congrArg₂ (fun (b : T) (y : M) => b • y) hb' (hνn i k f x)
        _ = 0 := ha'
    -- Descend the annihilation equation through the original additive colimit.
    obtain ⟨l, fl, hl⟩ := additive_colimit_zero D _ hD.some k (b' • x') hx'
    let fi : i ⟶ l := f ≫ fl
    obtain ⟨t, ht, hemap⟩ := hm i l fi x s
    let a' : (q.asIdeal.comap (κf l)).primeCompl :=
      ⟨(B.map fl).hom b', by
        change (κf l) ((B.map fl).hom b') ∉ q.asIdeal
        rw [hκ k l fl b', hb']
        exact a.property⟩
    have hzstage : eᵢ l ((N.map fi).hom z) = 0 := by
      rw [← hzrep, hemap]
      rw [← LocalizedModule.zero_mk
        (1 : (q.asIdeal.comap (κf l)).primeCompl), LocalizedModule.mk_eq]
      refine ⟨a', ?_⟩
      simp only [Submonoid.smul_def, one_smul, smul_zero]
      change (B.map fl).hom b' • (D.map fi).hom x = 0
      have hcomp : (D.map fi).hom x = (D.map fl).hom x' := by
        exact ConcreteCategory.congr_hom (D.map_comp f fl) x
      rw [hcomp, ← hs k l fl b' x']
      exact hl
    have hzstage' : (N.map fi).hom z = 0 :=
      (eᵢ l).injective (hzstage.trans (map_zero (eᵢ l)).symm)
    have hw := ConcreteCategory.congr_hom (colimit.w N fi) z
    change (colimit.ι N l).hom ((N.map fi).hom z) = (colimit.ι N i).hom z at hw
    rw [← hw, hzstage', map_zero]
  have hinj : Function.Injective d := by
    apply (injective_iff_map_eq_zero d).mpr
    intro z hz
    obtain ⟨i, y, hy⟩ := additive_colimit_rep N _ (colimit.isColimit N) z
    rw [← hy] at hz ⊢
    exact hzero i y ((hd i y).symm.trans hz)
  refine ⟨AddEquiv.ofBijective d ⟨hinj, hsurj⟩, ?_⟩
  exact hd

end Algebra
