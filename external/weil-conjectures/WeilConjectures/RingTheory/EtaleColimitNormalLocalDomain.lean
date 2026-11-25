/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.FilteredColimitNormalRing

/-!
# Local filtered colimits of etale algebras over normal domains

Source: Stacks Project, Tag 06DI, proof of normality of strict henselizations,
with Tags 033C, 037D, 00GV, 00U2 and 00D7
(blueprint: lem-weil-pbc-etale-colimit-normal-local-domain).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

-- Forgetting the algebra structure preserves this filtered colimit, even when
-- the base ring and the diagram rings live in different universes.
private noncomputable def ringColimit
    (A : Type u) [CommRing A] {I : Type v} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{v} A) [HasColimit B] :
    IsColimit ((forget₂ (CommAlgCat A) CommRingCat).mapCocone (colimit.cocone B)) := by
  classical
  let U := forget₂ (CommAlgCat.{v} A) CommRingCat.{v}
  let i : I := Classical.choice IsFiltered.nonempty
  have comm (s : Cocone (B ⋙ U)) (j : I) (a : A) :
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
  let liftCocone (s : Cocone (B ⋙ U)) : Cocone B :=
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
  let desc (s : Cocone (B ⋙ U)) := U.map (colimit.desc B (liftCocone s))
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    exact congrArg (fun f ↦ U.map f) (colimit.ι_desc (liftCocone s) j)
  · intro s m hm
    let : Algebra A s.pt :=
      ((s.ι.app i).hom.comp (algebraMap A (B.obj i))).toAlgebra
    let ma : colimit B ⟶ (liftCocone s).pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' := by
          intro a
          have h := ConcreteCategory.congr_hom (hm i) (algebraMap A (B.obj i) a)
          change m.hom ((colimit.ι B i).hom (algebraMap A (B.obj i) a)) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a) at h
          simp only [AlgHom.commutes] at h
          change m.hom (algebraMap A ↥(colimit B) a) =
            (s.ι.app i).hom (algebraMap A (B.obj i) a)
          exact h }
    have he : ma = colimit.desc B (liftCocone s) := by
      apply colimit.hom_ext
      intro j
      rw [colimit.ι_desc]
      ext x
      exact ConcreteCategory.congr_hom (hm j) x
    exact congrArg (fun f ↦ U.map f) he

-- Localizing a local ring at its maximal ideal only inverts units.
private theorem localNormalDomain (R : Type v) [CommRing R] [IsLocalRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsDomain R ∧ IsIntegrallyClosed R := by
  let p := IsLocalRing.maximalIdeal R
  obtain ⟨hd, hc⟩ := hR p
  let := hd
  let := hc
  have hu : p.primeCompl ≤ IsUnit.submonoid R := by
    intro x hx
    change ¬ ¬ IsUnit x at hx
    exact not_not.mp hx
  let e := (IsLocalization.atUnits R p.primeCompl (S := Localization.AtPrime p) hu).toRingEquiv
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩

/-- A local filtered colimit of etale algebras over a normal domain is an integrally
closed domain, and its structure map is injective. Source: Stacks Project, Tag 06DI,
normality implication, and Tags 00U2 and 00D7 for injectivity
(blueprint: lem-weil-pbc-etale-colimit-normal-local-domain).

Proof:
1. By `lem-weil-pbc-filtered-colimit-algebras-elementwise`, the algebra colimit is also
   the colimit of the underlying commutative rings, with the same coprojections.
2. Each diagram ring is normal by `lem-weil-pbc-etale-over-normal-ring-normal`:
   etale maps are smooth, and normality ascends along smooth maps (Tag 033C).
3. By `lem-weil-pbc-filtered-colimit-normal-ring`, the colimit ring is normal (Tag 037D).
4. A local normal ring is a normal domain: localization at its maximal ideal is
   isomorphic to the ring since every denominator outside that ideal is a unit.
   Thus the domain and integral-closedness properties of that localization transfer back
   (`def-weil-pbc-normal-ring`, Tag 00GV).
5. By `lem-weil-pbc-etale-algebra-flat` and `def-weil-pbc-flat-ring-map`, each diagram
   ring is flat over the domain A. Multiplication by any nonzero element of A is
   injective on A, hence on each diagram ring by tensoring with that flat algebra.
6. If a nonzero element of A dies in the colimit, choose an object of the nonempty
   filtered category. By `lem-weil-pbc-filtered-colimit-rings-zero`, its image dies
   at some later stage. Injectivity of multiplication forces that stage to be the zero
   ring, so its unital coprojection forces the colimit to be zero, contradicting locality.
   Hence the structure map is injective. -/
theorem isDomain_isIntegrallyClosed_injective_of_etale_colimit
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (B : I ⥤ CommAlgCat.{v} A) [HasColimit B]
    (hB : ∀ i : I, Algebra.Etale A (B.obj i)) [IsLocalRing ↥(colimit B)] :
    (IsDomain ↥(colimit B) ∧ IsIntegrallyClosed ↥(colimit B)) ∧
      Function.Injective (algebraMap A ↥(colimit B)) := by
  classical
  let U := forget₂ (CommAlgCat.{v} A) CommRingCat.{v}
  let F := B ⋙ U
  let hr := ringColimit A B
  let e : ↥(colimit B) ≃+* ↥(colimit F) :=
    (hr.coconePointUniqueUpToIso (colimit.isColimit F)).commRingCatIsoToRingEquiv
  let : IsLocalRing ↥(colimit F) := e.isLocalRing
  have hn : ∀ (p : Ideal ↥(colimit F)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    apply CommRingCat.isNormal_of_filtered_colimit F
    intro i
    have hnBi := RingHom.Etale.isNormalRing
      (f := algebraMap A (B.obj i)) (RingHom.etale_algebraMap.mpr (hB i)) hA
    exact hnBi
  obtain ⟨hd, hc⟩ := localNormalDomain ↥(colimit F) hn
  let := hd
  let := hc
  refine ⟨⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩, ?_⟩
  suffices hz : ∀ a : A, algebraMap A ↥(colimit B) a = 0 → a = 0 by
    intro a b hab
    exact sub_eq_zero.mp (hz (a - b) (by simp only [map_sub, hab, sub_self]))
  intro a ha
  by_contra hne
  let i : I := Classical.choice IsFiltered.nonempty
  have hi : (U.map (colimit.ι B i)) (algebraMap A (B.obj i) a) =
      (U.map (colimit.ι B i)) 0 := by
    change (colimit.ι B i).hom (algebraMap A (B.obj i) a) = (colimit.ι B i).hom 0
    simpa only [AlgHom.commutes, map_zero] using ha
  obtain ⟨k, f, g, he⟩ := Concrete.isColimit_exists_of_rep_eq F hr
    (algebraMap A (B.obj i) a) 0 hi
  have hk : algebraMap A (B.obj k) a = 0 := by
    change (B.map f).hom (algebraMap A (B.obj i) a) = (B.map g).hom 0 at he
    simpa only [AlgHom.commutes, map_zero] using he
  let : Algebra.Etale A (B.obj k) := hB k
  have regA : IsSMulRegular A a := fun x y h ↦ mul_left_cancel₀ hne h
  have reg : IsSMulRegular (B.obj k) (algebraMap A (B.obj k) a) := regA.of_flat
  have h10 : (1 : B.obj k) = 0 := by
    apply reg
    simp only [smul_eq_mul, hk, zero_mul]
  apply one_ne_zero (α := ↥(colimit B))
  simpa only [map_one, map_zero] using congrArg (colimit.ι B k).hom h10

end CommAlgCat
