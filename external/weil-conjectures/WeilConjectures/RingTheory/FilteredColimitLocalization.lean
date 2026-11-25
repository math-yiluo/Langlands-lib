/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Localization at a prime and normality along filtered colimits of rings

Let `R = colim_i R_i` be a filtered colimit of commutative rings with coprojections `ι_i`, and
let `p` be a prime of `R` with contractions `p_i = ι_i⁻¹(p)`. We show that the localizations
`(R_i)_{p_i}` form a diagram whose colimit is `R_p`, and that if all `(R_i)_{p_i}` are integrally
closed domains then so is `R_p`.

## Main definitions

- `CommRingCat.localizationAtPrimeDiagram c p`: the diagram `i ↦ (R_i)_{p_i}`.
- `CommRingCat.localizationAtPrimeCocone c p`: the cocone `(R_i)_{p_i} ⟶ R_p`.

## Main results

- `CommRingCat.isColimitLocalizationAtPrimeCocone`: `R_p = colim_i (R_i)_{p_i}`.
- `CommRingCat.isDomain_and_isIntegrallyClosed_of_isColimit`: a filtered colimit of integrally
  closed domains is an integrally closed domain.
- `CommRingCat.isDomain_and_isIntegrallyClosed_localization_of_isColimit`: Stacks 037D for the
  localization at a prime.

## References

- Stacks Project, Lemma 10.37.5, <https://stacks.math.columbia.edu/tag/037D>
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Polynomial

/-- A domain `R` is integrally closed if and only if `b ∣ a` whenever `b ≠ 0` and `a` is a root
of `P.scaleRoots b` for a monic polynomial `P`, i.e. whenever `a / b` is integral over `R`. -/
lemma isIntegrallyClosed_iff_dvd_of_eval_scaleRoots_eq_zero {R : Type*} [CommRing R]
    [IsDomain R] :
    IsIntegrallyClosed R ↔ ∀ a b : R, b ≠ 0 → ∀ P : R[X], P.Monic →
      (P.scaleRoots b).eval a = 0 → b ∣ a := by
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  rw [isIntegrallyClosed_iff K]
  constructor
  · intro h a b hb P hP he
    have hb' : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    set x : K := algebraMap R K a / algebraMap R K b
    have hx : algebraMap R K b * x = algebraMap R K a := mul_div_cancel₀ _ hb'
    have key := scaleRoots_eval₂_mul (p := P) (algebraMap R K) x b
    rw [hx, eval₂_at_apply, he, map_zero] at key
    have hPx : eval₂ (algebraMap R K) x P = 0 :=
      (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hb')
    obtain ⟨y, hy⟩ := h ⟨P, hP, hPx⟩
    refine ⟨y, hinj ?_⟩
    rw [map_mul, hy, ← hx, mul_comm]
  · intro h x ⟨P, hP, hPx⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
    have hx : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a :=
      mul_div_cancel₀ _ hb'
    have key := scaleRoots_eval₂_mul (p := P) (algebraMap R K)
      (algebraMap R K a / algebraMap R K b) b
    rw [hx, eval₂_at_apply, hPx, mul_zero, ← map_zero (algebraMap R K)] at key
    obtain ⟨y, rfl⟩ := h a b hb0 P hP (hinj key)
    exact ⟨y, by rw [map_mul, mul_div_cancel_left₀ _ hb']⟩

namespace CommRingCat

section Colimit

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}} {c : Cocone F}

omit [IsFiltered J] in
lemma ι_app_map_apply (c : Cocone F) {i j : J} (f : i ⟶ j) (x : F.obj i) :
    c.ι.app j (F.map f x) = c.ι.app i x := by
  rw [← c.w f]; rfl

include c in
lemma exists_eq_ι_app (hc : IsColimit c) (x : c.pt) : ∃ (j : J) (y : F.obj j), c.ι.app j y = x :=
  Concrete.isColimit_exists_rep F hc x

lemma exists_map_eq_zero (hc : IsColimit c) {i : J} (x : F.obj i) (hx : c.ι.app i x = 0) :
    ∃ (k : J) (f : i ⟶ k), F.map f x = 0 := by
  obtain ⟨k, f, g, h⟩ := Concrete.isColimit_exists_of_rep_eq F hc x 0 (by rw [hx, map_zero])
  exact ⟨k, f, by rw [h, map_zero]⟩

/-- A filtered colimit of nontrivial rings is nontrivial. -/
lemma nontrivial_of_isColimit (hc : IsColimit c) [∀ j, Nontrivial (F.obj j)] : Nontrivial c.pt := by
  let j : J := IsFiltered.nonempty.some
  refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
  obtain ⟨k, f, hf⟩ := exists_map_eq_zero hc (1 : F.obj j) (by rw [map_one, ← h])
  exact one_ne_zero (α := F.obj k) (by simp at hf)

/-- A filtered colimit of domains is a domain. -/
lemma isDomain_of_isColimit (hc : IsColimit c) [∀ j, IsDomain (F.obj j)] : IsDomain c.pt := by
  have := nontrivial_of_isColimit hc
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨i, a, rfl⟩ := exists_eq_ι_app hc a
  obtain ⟨j, b, rfl⟩ := exists_eq_ι_app hc b
  rw [← ι_app_map_apply c (IsFiltered.leftToMax i j),
    ← ι_app_map_apply c (IsFiltered.rightToMax i j),
    ← (ConcreteCategory.hom (c.ι.app (IsFiltered.max i j))).map_mul] at hab
  obtain ⟨k, f, hf⟩ := exists_map_eq_zero hc _ hab
  rw [map_mul] at hf
  rcases mul_eq_zero.mp hf with h | h
  · left
    rw [← ι_app_map_apply c (IsFiltered.leftToMax i j), ← ι_app_map_apply c f, h, map_zero]
  · right
    rw [← ι_app_map_apply c (IsFiltered.rightToMax i j), ← ι_app_map_apply c f, h, map_zero]

/-- **Filtered colimits of integrally closed domains.** A filtered colimit of integrally closed
domains is an integrally closed domain: a fraction `a / b` integral over the colimit is, after
lifting `a`, `b` and a monic equation to a common stage, integral over that stage, hence a
quotient there. -/
theorem isDomain_and_isIntegrallyClosed_of_isColimit (hc : IsColimit c)
    [∀ j, IsDomain (F.obj j)] [∀ j, IsIntegrallyClosed (F.obj j)] :
    IsDomain c.pt ∧ IsIntegrallyClosed c.pt := by
  classical
  have := isDomain_of_isColimit hc
  refine ⟨this, isIntegrallyClosed_iff_dvd_of_eval_scaleRoots_eq_zero.mpr
    fun a b hb P hP he ↦ ?_⟩
  obtain ⟨j, hj⟩ := exists_forall_mem_range_ι_app F c hc
    (insert a (insert b (P.support.image P.coeff)))
  obtain ⟨a', ha'⟩ := hj a (by simp)
  obtain ⟨b', hb'⟩ := hj b (by simp)
  have hlift : P ∈ lifts (c.ι.app j).hom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ P.support
    · exact hj _ (by simp [Finset.mem_image_of_mem P.coeff hn])
    · exact ⟨0, by rw [map_zero]; exact (notMem_support_iff.mp hn).symm⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hP
  have h1 : (c.ι.app j).hom Q.leadingCoeff ≠ 0 := by
    rw [hQm.leadingCoeff]
    exact fun h ↦ hb (by rw [← mul_one b, ← (c.ι.app j).hom.map_one, h, mul_zero])
  have hι : c.ι.app j ((Q.scaleRoots b').eval a') = 0 := by
    rw [← eval₂_at_apply, ← eval_map, map_scaleRoots _ _ _ h1, hQ, ha', hb']
    exact he
  obtain ⟨k, f, hf⟩ := exists_map_eq_zero hc _ hι
  have hm : (Q.map (F.map f).hom).Monic := hQm.map _
  have hb'' : F.map f b' ≠ 0 := fun h ↦ hb (by rw [← hb', ← ι_app_map_apply c f, h, map_zero])
  have he' : ((Q.map (F.map f).hom).scaleRoots (F.map f b')).eval (F.map f a') = 0 := by
    rw [← map_scaleRoots _ _ _ (by simp [hQm.leadingCoeff]), eval_map, eval₂_at_apply]
    exact hf
  obtain ⟨y, hy⟩ := isIntegrallyClosed_iff_dvd_of_eval_scaleRoots_eq_zero.mp inferInstance
    _ _ hb'' _ hm he'
  refine ⟨c.ι.app k y, ?_⟩
  rw [← ha', ← hb', ← ι_app_map_apply c f a', hy, map_mul, ι_app_map_apply]

end Colimit

section Localization

variable {J : Type u} [SmallCategory J] {F : J ⥤ CommRingCat.{u}} (c : Cocone F)
  (p : Ideal c.pt) [p.IsPrime]

omit [p.IsPrime] in
lemma comap_comap_ι_app {i j : J} (f : i ⟶ j) :
    (p.comap (c.ι.app j).hom).comap (F.map f).hom = p.comap (c.ι.app i).hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, c.w f]

/-- The diagram `i ↦ (R_i)_{p_i}` of localizations of the stages `R_i` of a cocone with point
`R` at the contractions `p_i = ι_i⁻¹(p)` of a prime `p` of `R`, with the transition maps
`x / s ↦ R(a)(x) / R(a)(s)`.

(blueprint: `lemma-quasi-finite-coordinates--1`) -/
noncomputable def localizationAtPrimeDiagram : J ⥤ CommRingCat.{u} where
  obj j := .of (Localization.AtPrime (p.comap (c.ι.app j).hom))
  map {i j} f := ofHom (Localization.localRingHom _ _ (F.map f).hom
    (comap_comap_ι_app c p f).symm)
  map_id j := by
    ext1
    refine IsLocalization.ringHom_ext (M := (p.comap (c.ι.app j).hom).primeCompl)
      (S := Localization.AtPrime (p.comap (c.ι.app j).hom)) ?_
    ext x
    simp
  map_comp {i j k} f g := by
    ext1
    refine IsLocalization.ringHom_ext (M := (p.comap (c.ι.app i).hom).primeCompl)
      (S := Localization.AtPrime (p.comap (c.ι.app i).hom)) ?_
    ext x
    simp [Localization.localRingHom_to_map]

/-- The cocone `κ_i : (R_i)_{p_i} → R_p`, `x / s ↦ ι_i(x) / ι_i(s)`.

(blueprint: `lemma-quasi-finite-coordinates--1`) -/
noncomputable def localizationAtPrimeCocone : Cocone (localizationAtPrimeDiagram c p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app j := ofHom (Localization.localRingHom _ p (c.ι.app j).hom rfl)
      naturality {i j} f := by
        ext1
        refine IsLocalization.ringHom_ext (M := (p.comap (c.ι.app i).hom).primeCompl)
          (S := Localization.AtPrime (p.comap (c.ι.app i).hom)) ?_
        ext x
        simpa [localizationAtPrimeDiagram, Localization.localRingHom_to_map] using
          congrArg (algebraMap c.pt (Localization.AtPrime p)) (ι_app_map_apply c f x) }

lemma localizationAtPrimeCocone_ι_app_mk' (j : J) (x : F.obj j)
    (s : (p.comap (c.ι.app j).hom).primeCompl) :
    (localizationAtPrimeCocone c p).ι.app j
        (IsLocalization.mk' (Localization.AtPrime (p.comap (c.ι.app j).hom)) x s) =
      IsLocalization.mk' (R := c.pt) (Localization.AtPrime p) (c.ι.app j x)
        (⟨c.ι.app j s, s.2⟩ : p.primeCompl) :=
  Localization.localRingHom_mk' _ _ _ rfl _ _

lemma localizationAtPrimeDiagram_map_mk' {i j : J} (f : i ⟶ j) (x : F.obj i)
    (s : (p.comap (c.ι.app i).hom).primeCompl) :
    (localizationAtPrimeDiagram c p).map f
        (IsLocalization.mk' (Localization.AtPrime (p.comap (c.ι.app i).hom)) x s) =
      IsLocalization.mk' (Localization.AtPrime (p.comap (c.ι.app j).hom)) (F.map f x)
        (⟨F.map f s, by
          change c.ι.app j _ ∉ p
          rw [ι_app_map_apply]
          exact s.2⟩ : (p.comap (c.ι.app j).hom).primeCompl) :=
  Localization.localRingHom_mk' _ _ _ (comap_comap_ι_app c p f).symm _ _

variable [IsFiltered J]

/-- **Localization at a prime commutes with filtered colimits of rings.** If `R = colim_i R_i`
is a filtered colimit of commutative rings and `p` is a prime of `R` with contractions
`p_i = ι_i⁻¹(p)`, then `R_p = colim_i (R_i)_{p_i}`.

(blueprint: `lemma-quasi-finite-coordinates--1`) -/
noncomputable def isColimitLocalizationAtPrimeCocone (hc : IsColimit c) :
    IsColimit (localizationAtPrimeCocone c p) := by
  have := reflectsColimitsOfShape_of_reflectsIsomorphisms (G := forget CommRingCat.{u}) (J := J)
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ (fun z ↦ ?_) (fun i w w' h ↦ ?_))
  · change Localization.AtPrime p at z
    obtain ⟨⟨r, σ⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    dsimp only
    obtain ⟨i, x, hx⟩ := exists_eq_ι_app hc r
    obtain ⟨j, s, hs⟩ := exists_eq_ι_app hc (σ : c.pt)
    let k := IsFiltered.max i j
    have hs' : F.map (IsFiltered.rightToMax i j) s ∈ (p.comap (c.ι.app k).hom).primeCompl := by
      change c.ι.app k _ ∉ p
      rw [ι_app_map_apply, hs]
      exact σ.2
    refine ⟨k, IsLocalization.mk' (Localization.AtPrime (p.comap (c.ι.app k).hom))
      (F.map (IsFiltered.leftToMax i j) x) ⟨_, hs'⟩, ?_⟩
    change _ = (localizationAtPrimeCocone c p).ι.app k _
    rw [localizationAtPrimeCocone_ι_app_mk']
    congr 1
    · rw [ι_app_map_apply, hx]
    · exact Subtype.ext (by rw [← hs]; exact (ι_app_map_apply c (IsFiltered.rightToMax i j) s).symm)
  · change Localization.AtPrime (p.comap (c.ι.app i).hom) at w w'
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (p.comap (c.ι.app i).hom).primeCompl w
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective (p.comap (c.ι.app i).hom).primeCompl w'
    dsimp only at h ⊢
    change (localizationAtPrimeCocone c p).ι.app i _ =
      (localizationAtPrimeCocone c p).ι.app i _ at h
    rw [localizationAtPrimeCocone_ι_app_mk', localizationAtPrimeCocone_ι_app_mk'] at h
    obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp h
    obtain ⟨l, v, rfl⟩ := exists_eq_ι_app hc u
    obtain ⟨n, f, hf⟩ := exists_map_eq_zero hc
      (F.map (IsFiltered.leftToMax i l) (t * x - s * y) * F.map (IsFiltered.rightToMax i l) v)
      (by
        simp only [map_mul, map_sub, ι_app_map_apply]
        dsimp only at hu'
        linear_combination hu')
    refine ⟨n, IsFiltered.leftToMax i l ≫ f, ?_⟩
    change (localizationAtPrimeDiagram c p).map _ _ = (localizationAtPrimeDiagram c p).map _ _
    rw [localizationAtPrimeDiagram_map_mk', localizationAtPrimeDiagram_map_mk']
    refine (IsLocalization.eq (S := Localization.AtPrime (p.comap (c.ι.app n).hom))).mpr ?_
    have hv : F.map (IsFiltered.rightToMax i l ≫ f) v ∈
        (p.comap (c.ι.app n).hom).primeCompl := by
      change c.ι.app n _ ∉ p
      rw [ι_app_map_apply]
      exact hu
    refine ⟨⟨_, hv⟩, ?_⟩
    simp only [F.map_comp, CommRingCat.comp_apply, map_mul, map_sub] at hf ⊢
    linear_combination hf

/-- **Localizations of filtered colimits of normal rings are integrally closed.** If
`R = colim_i R_i` is a filtered colimit of commutative rings and `p` is a prime of `R` such
that all localizations `(R_i)_{p_i}` at the contractions `p_i = ι_i⁻¹(p)` are integrally closed
domains, then `R_p` is an integrally closed domain.

(blueprint: `proposition-proper-direct-image-constructible-complexes`) -/
theorem isDomain_and_isIntegrallyClosed_localization_of_isColimit (hc : IsColimit c)
    (h : ∀ j, IsDomain (Localization.AtPrime (p.comap (c.ι.app j).hom)) ∧
      IsIntegrallyClosed (Localization.AtPrime (p.comap (c.ι.app j).hom))) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
  @isDomain_and_isIntegrallyClosed_of_isColimit _ _ _ _ _
    (isColimitLocalizationAtPrimeCocone c p hc) (fun j ↦ (h j).1) (fun j ↦ (h j).2)

end Localization

end CommRingCat
