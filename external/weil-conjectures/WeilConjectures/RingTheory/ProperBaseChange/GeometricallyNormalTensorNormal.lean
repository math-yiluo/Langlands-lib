/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Algebra.Field.ULift
import WeilConjectures.FieldTheory.SeparableSmoothColimit
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Tensor products of geometrically normal and normal algebras

Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem normal_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

private theorem normal_localization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.comap_isPrime (algebraMap R S) q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (Localization.AtPrime q)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_tensor_localization_right
    {k A B B' : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing B']
    [Algebra k A] [Algebra k B] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
    (M : Submonoid B) [IsLocalization M B']
    (h : ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (A ⊗[k] B')) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra (A ⊗[k] B) (A ⊗[k] B') :=
    (TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B B')).toAlgebra
  have : IsScalarTower A (A ⊗[k] B) (A ⊗[k] B') :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k A M B'
    (by ext; rfl)
  exact normal_localization (M.map (TensorProduct.includeRight (R := k) (A := A))) h

private theorem normal_tensor_localization_left
    {k A A' B : Type*} [CommRing k] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra k A] [Algebra k A'] [Algebra k B] [Algebra A A'] [IsScalarTower k A A']
    (M : Submonoid A) [IsLocalization M A']
    (h : ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (A' ⊗[k] B)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  have h' := normal_equiv (TensorProduct.comm k A B).toRingEquiv h
  exact normal_equiv (TensorProduct.comm k B A').toRingEquiv
    (normal_tensor_localization_right M h')

private theorem normal_atPrime_of_localization {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (p : Ideal R) [hp : p.IsPrime]
    (hdisj : Disjoint (M : Set R) (p : Set R))
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let q := p.map (algebraMap R S)
  let : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S p hp hdisj
  have hcontract : q.comap (algebraMap R S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M S hp hdisj
  obtain ⟨hd, hi⟩ := hS q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hcontract] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q)
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_tensor_of_normal_localizations_right
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (h : ∀ (q : Ideal B) [q.IsPrime],
      ∀ (r : Ideal (A ⊗[k] Localization.AtPrime q)) [r.IsPrime],
        IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
  intro r hr
  let q := r.comap (TensorProduct.includeRight (R := k) (A := A)).toRingHom
  let : q.IsPrime := Ideal.comap_isPrime _ r
  let B' := Localization.AtPrime q
  let : Algebra (A ⊗[k] B) (A ⊗[k] B') :=
    (TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B B')).toAlgebra
  have : IsScalarTower A (A ⊗[k] B) (A ⊗[k] B') :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k A q.primeCompl B'
    (by ext; rfl)
  apply normal_atPrime_of_localization
    (q.primeCompl.map (TensorProduct.includeRight (R := k) (A := A))) r _ (h q)
  rw [Set.disjoint_left]
  rintro x ⟨b, hb, rfl⟩ hx
  exact hb hx

private theorem normal_tensor_of_normal_localizations_left
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    (h : ∀ (p : Ideal A) [p.IsPrime],
      ∀ (r : Ideal (Localization.AtPrime p ⊗[k] B)) [r.IsPrime],
        IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
  apply normal_equiv (TensorProduct.comm k B A).toRingEquiv
  apply normal_tensor_of_normal_localizations_right
  intro p hp
  exact normal_equiv (TensorProduct.comm k (Localization.AtPrime p) B).toRingEquiv (h p)

private theorem normal_of_geometric
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (h : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let e := (TensorProduct.congr ((AlgEquiv.refl : A ≃ₐ[k] A))
    (ULift.algEquiv : ULift.{max v w} k ≃ₐ[k] k)).trans (TensorProduct.rid k k A)
  exact normal_equiv e.toRingEquiv (h (ULift.{max v w} k))

open CategoryTheory CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem normal_tensor_of_directed_cover_left
    {k : Type u} {R B : Type (max u v)} [CommRing k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra k B]
    (P : Set (Subalgebra k R)) (hne : P.Nonempty)
    (hdir : DirectedOn (· ≤ ·) P) (hcover : ∀ x : R, ∃ A ∈ P, x ∈ A)
    (hnormal : ∀ A ∈ P, ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (R ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  let I := {A : Subalgebra k R // A ∈ P}
  have : Nonempty I := hne.to_subtype
  have : IsDirectedOrder I := ⟨fun i j ↦ by
    obtain ⟨A, hA, hi, hj⟩ := hdir i.1 i.2 j.1 j.2
    exact ⟨⟨A, hA⟩, hi, hj⟩⟩
  let inc {i j : I} (h : i ≤ j) : i.1 →ₐ[k] j.1 := Subalgebra.inclusion h
  let val (i : I) : i.1 →ₐ[k] R := i.1.val
  let F : I ⥤ CommRingCat.{max u v} :=
    { obj i := CommRingCat.of (i.1 ⊗[k] B)
      map {i j} f := CommRingCat.ofHom
        (Algebra.TensorProduct.map (inc (leOfHom f)) (AlgHom.id k B)).toRingHom
      map_id i := by ext <;> rfl
      map_comp f g := by ext <;> rfl }
  let U : Cocone F :=
    { pt := CommRingCat.of (R ⊗[k] B)
      ι :=
        { app i := CommRingCat.ofHom
            (Algebra.TensorProduct.map (val i) (AlgHom.id k B)).toRingHom
          naturality {i j} f := by ext <;> rfl } }
  have hsup : ⨆ i : I, i.1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨A, hA, hx⟩ := hcover x
    exact Algebra.mem_iSup_of_mem ⟨A, hA⟩ hx
  have hU : IsColimit U := by
    apply IsColimit.ofExistsUnique
    intro c
    let left (i : I) : i.1 →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeLeftRingHom
    let right (i : I) : B →+* c.pt :=
      (c.ι.app i).hom.comp Algebra.TensorProduct.includeRight.toRingHom
    have hleft {i j : I} (h : i ≤ j) (x : i.1) :
        left j (inc h x) = left i x := by
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (x ⊗ₜ[k] 1)
      simpa [F, left] using hh
    have hright {i j : I} (h : i ≤ j) : right i = right j := by
      ext b
      have hh := ConcreteCategory.congr_hom (c.w (homOfLE h)) (1 ⊗ₜ[k] b)
      simpa [F, right] using hh.symm
    have hright_all (i j : I) : right i = right j := by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact (hright hik).trans (hright hjk).symm
    let i0 : I := Classical.arbitrary I
    let b : B →+* c.pt := right i0
    have hb (i : I) : b = right i := hright_all i0 i
    let : Algebra k c.pt := (b.comp (algebraMap k B)).toAlgebra
    let bAlg : B →ₐ[k] c.pt := { b with commutes' := fun _ ↦ rfl }
    let leftAlg (i : I) : i.1 →ₐ[k] c.pt :=
      { toRingHom := left i
        commutes' := by
          intro a
          change left i (algebraMap k i.1 a) = b (algebraMap k B a)
          rw [hb i]
          exact congrArg (c.ι.app i).hom
            (RingHom.congr_fun TensorProduct.includeLeftRingHom_comp_algebraMap a) }
    let rAlg : R →ₐ[k] c.pt :=
      (Subalgebra.iSupLift (fun i : I ↦ i.1) (Subtype.mono_coe _).directed_le
        leftAlg (fun i j hij ↦ AlgHom.ext (fun x ↦ (hleft hij x).symm))
        ⊤ hsup.ge).comp Subalgebra.topEquiv.symm.toAlgHom
    let r := rAlg.toRingHom
    have hr (i : I) (x : i.1) : r (x : R) = left i x := by
      have he : Subalgebra.topEquiv.symm.toAlgHom (i.1.val x) =
          Subalgebra.inclusion (le_top : i.1 ≤ ⊤) x := Subtype.ext rfl
      change (Subalgebra.iSupLift (fun i : I ↦ i.1) (Subtype.mono_coe _).directed_le
        leftAlg (fun i j hij ↦ AlgHom.ext (fun x ↦ (hleft hij x).symm)) ⊤ hsup.ge)
        (Subalgebra.topEquiv.symm.toAlgHom (i.1.val x)) = left i x
      rw [he, Subalgebra.iSupLift_inclusion]
      rfl
    let m : U.pt ⟶ c.pt := CommRingCat.ofHom
      (Algebra.TensorProduct.lift rAlg bAlg (fun _ _ ↦ Commute.all _ _)).toRingHom
    have hm (i : I) : U.ι.app i ≫ m = c.ι.app i := by
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext
      · ext x
        change r (val i x) * b 1 = (c.ι.app i).hom (x ⊗ₜ[k] 1)
        rw [map_one, mul_one]
        exact hr i x
      · ext x
        change r 1 * b x = (c.ι.app i).hom (1 ⊗ₜ[k] x)
        rw [map_one, one_mul, hb i]
        rfl
    refine ⟨m, hm, ?_⟩
    intro n hn
    apply CommRingCat.hom_ext
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      obtain ⟨A, hA, hx⟩ := hcover x
      let i : I := ⟨A, hA⟩
      have hh := ConcreteCategory.congr_hom ((hn i).trans (hm i).symm)
        ((⟨x, hx⟩ : i.1) ⊗ₜ[k] (1 : B))
      exact hh
    · ext x
      have hh := ConcreteCategory.congr_hom ((hn i0).trans (hm i0).symm)
        ((1 : i0.1) ⊗ₜ[k] x)
      exact hh
  let : HasColimit F := ⟨⟨U, hU⟩⟩
  let e := CategoryTheory.Iso.commRingCatIsoToRingEquiv
    (colimit.isoColimitCocone ⟨U, hU⟩)
  exact normal_equiv e
    (CommRingCat.isNormal_of_filtered_colimit F (fun i ↦ hnormal i.1 i.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem normal_subalgebra_extension
    {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsDomain R] [IsIntegrallyClosed R] (C : Subalgebra k R) (hC : C.FG) :
    ∃ A : Subalgebra k R, C ≤ A ∧ A.FG ∧ IsIntegrallyClosed A := by
  classical
  let K := FractionRing C
  let N := integralClosure C K
  have : Algebra.FiniteType k C := (Subalgebra.fg_iff_finiteType C).mp hC
  have : Module.Finite C N := Algebra.FiniteType.finite_integralClosure k K K
  have : Algebra.FiniteType k N :=
    Algebra.FiniteType.trans (R := k) (S := C) (A := N)
      (inferInstanceAs (Algebra.FiniteType k C))
      (inferInstanceAs (Algebra.FiniteType C N))
  have : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let L := FractionRing R
  let fC : C →ₐ[C] L := Algebra.ofId C L
  have hk : Function.Injective fC :=
    (IsFractionRing.injective R L).comp Subtype.val_injective
  let l : K →ₐ[C] L := IsFractionRing.liftAlgHom hk
  let j : N →ₐ[C] L := l.comp N.val
  let r : R →ₐ[k] L := IsScalarTower.toAlgHom k R L
  have hr : Function.Injective r := IsFractionRing.injective R L
  have hjmem : ∀ n : N, j n ∈ r.range := by
    intro n
    apply (AlgHom.mem_range r).mpr
    have hn : IsIntegral C (j n) := n.property.map l
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hn.tower_top (A := R))
  let q : N →ₐ[k] r.range := (j.restrictScalars k).codRestrict r.range hjmem
  let h : N →ₐ[k] R := (AlgEquiv.ofInjective r hr).symm.toAlgHom.comp q
  have hh : ∀ n : N, r (h n) = j n := by
    intro n
    change r ((AlgEquiv.ofInjective r hr).symm (q n)) = j n
    have he := (AlgEquiv.ofInjective r hr).apply_symm_apply (q n)
    exact congrArg Subtype.val he
  have hinj : Function.Injective h := by
    intro x y hxy
    apply Subtype.ext
    apply l.toRingHom.injective
    exact (hh x).symm.trans ((congrArg r hxy).trans (hh y))
  refine ⟨h.range, ?_, ?_, ?_⟩
  · intro x hx
    let c : C := ⟨x, hx⟩
    refine (AlgHom.mem_range h).mpr ⟨algebraMap C N c, ?_⟩
    apply hr
    rw [hh]
    rw [j.commutes]
    rfl
  · have : Algebra.FiniteType k h.range :=
      Algebra.FiniteType.of_surjective h.rangeRestrict h.rangeRestrict_surjective
    exact (Subalgebra.fg_iff_finiteType h.range).mpr inferInstance
  · exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective h hinj).toRingEquiv

private theorem normal_reduced {R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsReduced R := by
  apply isReduced_ofLocalizationMaximal
  intro p hp
  let : p.IsMaximal := hp
  let : IsDomain (Localization.AtPrime p) := (hR p).1
  infer_instance

private theorem separable_of_geometric_normal
    {k : Type u} {K : Type (max u v)} [Field k] [Field K] [Algebra k K]
    (hK : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
      ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsSeparableExtension k K := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hz
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    exact isSeparableExtension_of_forall_isReduced_tensorProduct k K (ringChar k)
      (fun E _ _ ↦ normal_reduced (hK E))
  · have : CharZero k := by
      let : CharP k 0 := hz ▸ inferInstance
      exact CharP.charP_to_charZero k
    intro F hF
    let : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
    exact ⟨(s : Set F), hs, hsep⟩

private theorem normal_tensor_of_separable_field
    {k : Type u} {K B : Type (max u v)} [Field k] [Field K] [CommRing B]
    [Algebra k K] [Algebra k B] (hsep : IsSeparableExtension k K)
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    (∀ (p : Ideal (K ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
        IsReduced (K ⊗[k] B) := by
  have hn : ∀ (p : Ideal (K ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    obtain ⟨hne, hdir, hcover, _⟩ :=
      FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
    apply normal_tensor_of_directed_cover_left
      {D : Subalgebra k K | Smooth k D ∧ D.FG}
    · obtain ⟨D⟩ := hne
      exact ⟨D.1, D.2⟩
    · intro D hD E hE
      obtain ⟨F, hDF, hEF⟩ := hdir ⟨D, hD⟩ ⟨E, hE⟩
      exact ⟨F.1, F.2, hDF, hEF⟩
    · intro x
      obtain ⟨D, hx⟩ := hcover x
      exact ⟨D.1, D.2, hx⟩
    · intro D hD
      let : Smooth k D := hD.1
      have hn := RingHom.Smooth.isNormalRing
        (RingHom.smooth_algebraMap.mpr (inferInstance : Smooth B (B ⊗[k] D))) hB
      exact normal_equiv (TensorProduct.comm k B D).toRingEquiv hn
  exact ⟨hn, normal_reduced (R := K ⊗[k] B) hn⟩

private theorem tensor_map_injective
    {k A A' B B' : Type*} [Field k] [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra k A] [Algebra k A']
    [Algebra k B] [Algebra k B'] (f : A →ₐ[k] A') (g : B →ₐ[k] B')
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  exact _root_.TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

private theorem finite_minimalPrimes_tensor
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [FiniteType k B] :
    (minimalPrimes (A ⊗[k] B)).Finite := by
  let K := FractionRing A
  let f : A ⊗[k] B →ₐ[k] K ⊗[k] B :=
    TensorProduct.map (IsScalarTower.toAlgHom k A K) (AlgHom.id k B)
  have hf : Function.Injective f := tensor_map_injective _ _
    (IsFractionRing.injective A K) Function.injective_id
  have : IsNoetherianRing (K ⊗[k] B) := FiniteType.isNoetherianRing K _
  have hs := (minimalPrimes.finite_of_isNoetherianRing (K ⊗[k] B)).image
    (Ideal.comap f.toRingHom)
  apply hs.subset
  intro p hp
  apply Ideal.minimalPrimes_comap_subset f.toRingHom (⊥ : Ideal (K ⊗[k] B))
  rw [Ideal.comap_bot_of_injective f.toRingHom hf]
  exact hp

private theorem normal_tensor_domain_of_finiteType
    {k : Type u} {A B : Type (max u v)} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain B] [IsIntegrallyClosed B]
    (hfinite : ∀ (D : Subalgebra k B), D.FG → IsIntegrallyClosed D →
      ∀ (p : Ideal (A ⊗[k] D)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  apply normal_equiv (TensorProduct.comm k B A).toRingEquiv
  apply normal_tensor_of_directed_cover_left {D : Subalgebra k B | D.FG ∧ IsIntegrallyClosed D}
  · obtain ⟨D, hD, hfg, hn⟩ :=
      normal_subalgebra_extension (⊥ : Subalgebra k B) Subalgebra.fg_bot
    exact ⟨D, hfg, hn⟩
  · intro D hD E hE
    obtain ⟨F, hF, hfg, hn⟩ := normal_subalgebra_extension (D ⊔ E) (hD.1.sup hE.1)
    exact ⟨F, ⟨hfg, hn⟩, le_sup_left.trans hF, le_sup_right.trans hF⟩
  · intro x
    have hxfg : (Algebra.adjoin k ({x} : Set B)).FG :=
      Subalgebra.fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩
    obtain ⟨D, hD, hfg, hn⟩ := normal_subalgebra_extension (Algebra.adjoin k {x}) hxfg
    exact ⟨D, ⟨hfg, hn⟩, hD (Algebra.subset_adjoin (Set.mem_singleton x))⟩
  · intro D hD
    exact normal_equiv (TensorProduct.comm k A D).toRingEquiv (hfinite D hD.1 hD.2)

private theorem integral_mem_normal_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R)
    (hn : ∀ (p : Ideal S) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (f : S →ₐ[R] FractionRing R) (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ y : S, f y = x := by
  let : Algebra S (FractionRing R) := f.toRingHom.toAlgebra
  have : IsScalarTower R S (FractionRing R) :=
    .of_algebraMap_eq <| fun r ↦ (f.commutes r).symm
  have : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization M S (FractionRing R) hM
  have : IsIntegrallyClosed S := (isIntegrallyClosed_iff (FractionRing S)).mpr
    (fun {y} hy ↦ integral_totalFraction_mem_range_of_normal S hn y hy)
  exact (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance (hx.tower_top (A := S))

private theorem tensor_intersection
    {k A A' B B' : Type*} [Field k] [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra k A] [Algebra k A']
    [Algebra k B] [Algebra k B'] (f : A →ₐ[k] A') (g : B →ₐ[k] B')
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : A' ⊗[k] B) (y : A ⊗[k] B')
    (h : TensorProduct.map (AlgHom.id k A') g x =
      TensorProduct.map f (AlgHom.id k B') y) :
    ∃ z : A ⊗[k] B,
      TensorProduct.map f (AlgHom.id k B) z = x ∧
        TensorProduct.map (AlgHom.id k A) g z = y := by
  let p := f.toLinearMap.leftInverse
  have hp : p.comp f.toLinearMap = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr hf)
  let z : A ⊗[k] B := _root_.TensorProduct.map p LinearMap.id x
  have hy : TensorProduct.map (AlgHom.id k A) g z = y := by
    have hh := congrArg (_root_.TensorProduct.map p (LinearMap.id : B' →ₗ[k] B')) h
    change _root_.TensorProduct.map p LinearMap.id
        (_root_.TensorProduct.map LinearMap.id g.toLinearMap x) =
      _root_.TensorProduct.map p LinearMap.id
        (_root_.TensorProduct.map f.toLinearMap LinearMap.id y) at hh
    change _root_.TensorProduct.map LinearMap.id g.toLinearMap
      (_root_.TensorProduct.map p LinearMap.id x) = y
    simpa only [_root_.TensorProduct.map_map, LinearMap.id_comp,
      LinearMap.comp_id, hp, _root_.TensorProduct.map_id, LinearMap.id_apply] using hh
  refine ⟨z, ?_, hy⟩
  apply tensor_map_injective (AlgHom.id k A') g Function.injective_id hg
  rw [h, ← hy]
  change _root_.TensorProduct.map LinearMap.id g.toLinearMap
      (_root_.TensorProduct.map f.toLinearMap LinearMap.id z) =
    _root_.TensorProduct.map f.toLinearMap LinearMap.id
      (_root_.TensorProduct.map LinearMap.id g.toLinearMap z)
  simp only [_root_.TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

private theorem localization_regular_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (h : Function.Injective (algebraMap R S)) : M ≤ nonZeroDivisors R := by
  intro x hx
  exact mem_nonZeroDivisors_of_injective h
    (IsLocalization.map_units S (⟨x, hx⟩ : M)).mem_nonZeroDivisors

private theorem localization_totalFraction_embedding
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    ∃ f : S →ₐ[R] FractionRing R, Function.Injective f := by
  let hu : ∀ s : M, IsUnit (algebraMap R (FractionRing R) s) :=
    fun s ↦ IsLocalization.map_units (FractionRing R) (⟨(s : R), hM s.2⟩ : nonZeroDivisors R)
  refine ⟨IsLocalization.liftAlgHom (f := Algebra.ofId R (FractionRing R)) hu, ?_⟩
  change Function.Injective (IsLocalization.lift hu : S →+* FractionRing R)
  apply (IsLocalization.lift_injective_iff hu).mpr
  intro x y
  exact ⟨fun h ↦ congrArg (algebraMap R (FractionRing R))
      (IsLocalization.injective S hM h),
    fun h ↦ congrArg (algebraMap R S) (IsFractionRing.injective R (FractionRing R) h)⟩

private theorem integral_tensor_mem_range
    {k A B K L : Type*} [Field k] [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k L]
    [Algebra A K] [Algebra B L] [IsScalarTower k A K] [IsScalarTower k B L]
    [IsDomain A] [IsDomain B] [IsFractionRing A K] [IsFractionRing B L]
    (hKA : ∀ (p : Ideal (K ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hBL : ∀ (p : Ideal (A ⊗[k] L)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (x : FractionRing (A ⊗[k] B)) (hx : IsIntegral (A ⊗[k] B) x) :
    ∃ z : A ⊗[k] B, algebraMap (A ⊗[k] B) (FractionRing (A ⊗[k] B)) z = x := by
  let C := A ⊗[k] B
  let S := K ⊗[k] B
  let U := A ⊗[k] L
  let T := K ⊗[k] L
  let Q := FractionRing C
  let f : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  let g : B →ₐ[k] L := IsScalarTower.toAlgHom k B L
  let i : C →ₐ[k] S := TensorProduct.map f (AlgHom.id k B)
  let j : C →ₐ[k] U := TensorProduct.map (AlgHom.id k A) g
  let m : S →ₐ[k] T := TensorProduct.map (AlgHom.id k K) g
  let n : U →ₐ[k] T := TensorProduct.map f (AlgHom.id k L)
  have hf : Function.Injective f := IsFractionRing.injective A K
  have hg : Function.Injective g := IsFractionRing.injective B L
  have hi := tensor_map_injective f (AlgHom.id k B) hf Function.injective_id
  have hj := tensor_map_injective (AlgHom.id k A) g Function.injective_id hg
  have hm := tensor_map_injective (AlgHom.id k K) g Function.injective_id hg
  let : Algebra C S := i.toAlgebra
  let : Algebra C U := j.toAlgebra
  let : Algebra S T := m.toAlgebra
  have : IsScalarTower A C S := .of_algebraMap_eq <| by
    intro a
    change algebraMap A K a ⊗ₜ[k] (1 : B) = i (a ⊗ₜ[k] (1 : B))
    change f a ⊗ₜ[k] (1 : B) = f a ⊗ₜ[k] (AlgHom.id k B) 1
    rw [AlgHom.id_apply]
  have : IsScalarTower A C U := .of_algebraMap_eq <| by
    intro a
    change a ⊗ₜ[k] (1 : L) = j (a ⊗ₜ[k] (1 : B))
    change a ⊗ₜ[k] (1 : L) = a ⊗ₜ[k] g 1
    rw [map_one]
  have : IsScalarTower K S T := .of_algebraMap_eq <| by
    intro a
    change a ⊗ₜ[k] (1 : L) = m (a ⊗ₜ[k] (1 : B))
    change a ⊗ₜ[k] (1 : L) = a ⊗ₜ[k] g 1
    rw [map_one]
  let MA := Algebra.algebraMapSubmonoid C (nonZeroDivisors A)
  let MB := (nonZeroDivisors B).map (TensorProduct.includeRight (R := k) (A := A))
  let MT := (nonZeroDivisors B).map (TensorProduct.includeRight (R := k) (A := K))
  have : IsLocalization MA S :=
    IsLocalization.tensorProduct_tensorProduct k B (nonZeroDivisors A) K (by
      apply RingHom.ext
      intro b
      change i (1 ⊗ₜ[k] b) = 1 ⊗ₜ[k] b
      change f 1 ⊗ₜ[k] b = 1 ⊗ₜ[k] b
      rw [map_one])
  have : IsLocalization MB U :=
    IsLocalization.tensorProduct_tensorProduct_right k A (nonZeroDivisors B) L
      (by ext; rfl)
  have : IsLocalization MT T :=
    IsLocalization.tensorProduct_tensorProduct_right k K (nonZeroDivisors B) L
      (by ext; rfl)
  have hMA : MA ≤ nonZeroDivisors C := localization_regular_of_injective MA hi
  have hMB : MB ≤ nonZeroDivisors C := localization_regular_of_injective MB hj
  obtain ⟨eA, heA⟩ := localization_totalFraction_embedding (S := S) MA hMA
  obtain ⟨eB, _⟩ := localization_totalFraction_embedding (S := U) MB hMB
  have hu : ∀ d : MT, IsUnit (eA d) := by
    rintro ⟨d, hd⟩
    obtain ⟨b, hb, rfl⟩ := hd
    change IsUnit (eA (1 ⊗ₜ[k] b))
    have he : i (1 ⊗ₜ[k] b) = (1 ⊗ₜ[k] b : S) := by
      change f 1 ⊗ₜ[k] b = 1 ⊗ₜ[k] b
      rw [map_one]
    rw [← he]
    change IsUnit (eA (algebraMap C S (1 ⊗ₜ[k] b)))
    rw [eA.commutes]
    exact IsLocalization.map_units Q (⟨1 ⊗ₜ[k] b, hMB ⟨b, hb, rfl⟩⟩ : nonZeroDivisors C)
  let eT : T →+* Q := IsLocalization.lift hu
  have heT (s : S) : eT (m s) = eA s := IsLocalization.lift_eq hu s
  have heTi : Function.Injective eT := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq MT eT).mpr
    intro a b
    change m a = m b ↔ eT (m a) = eT (m b)
    rw [heT, heT]
    exact hm.eq_iff.trans heA.eq_iff.symm
  have hcomm : m.comp i = n.comp j := by ext <;> rfl
  have heTU : eT.comp n.toRingHom = eB.toRingHom := by
    apply IsLocalization.ringHom_ext MB
    apply RingHom.ext
    intro c
    change eT (n (j c)) = eB (j c)
    have hc : m (i c) = n (j c) := AlgHom.congr_fun hcomm c
    rw [← hc, heT]
    exact (eA.commutes c).trans (eB.commutes c).symm
  obtain ⟨a, ha⟩ := integral_mem_normal_localization MA hMA hKA eA x hx
  obtain ⟨b, hb⟩ := integral_mem_normal_localization MB hMB hBL eB x hx
  have hab : m a = n b := by
    apply heTi
    exact (heT a).trans (ha.trans (hb.symm.trans (RingHom.congr_fun heTU b).symm))
  obtain ⟨z, hz, _⟩ := tensor_intersection f g hf hg a b hab
  exact ⟨z, (eA.commutes z).symm.trans ((congrArg eA hz).trans ha)⟩

-- Prove the total-fraction criterion with abstract algebras, before specializing to subalgebras.
private theorem integrallyClosed_tensor_of_normal_localizations
    {k A B K L : Type*} [Field k] [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra k A] [Algebra k B] [Algebra k K] [Algebra k L]
    [Algebra A K] [Algebra B L] [IsScalarTower k A K] [IsScalarTower k B L]
    [IsDomain A] [IsDomain B] [IsFractionRing A K] [IsFractionRing B L]
    (hKA : ∀ (p : Ideal (K ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hBL : ∀ (p : Ideal (A ⊗[k] L)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed (A ⊗[k] B) := by
  apply (isIntegrallyClosed_iff (FractionRing (A ⊗[k] B))).mpr
  intro x hx
  exact integral_tensor_mem_range (k := k) (A := A) (B := B)
    (K := K) (L := L) hKA hBL x hx

private theorem normal_domain_case_common
    {k : Type u} {A B : Type (max u v)} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain B] [IsIntegrallyClosed B]
    (hA : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (_hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  refine normal_tensor_domain_of_finiteType.{u, v} (k := k) (A := A) (B := B) ?_
  intro D hfg hn
  let : FiniteType k D := (Subalgebra.fg_iff_finiteType D).mp hfg
  let : IsIntegrallyClosed D := hn
  let K := FractionRing A
  -- Preserve the existing localization ring structure when installing its field structure.
  let : Field K := IsFractionRing.toField A
  have hK : ∀ (E : Type (max u v)) [Field E] [Algebra k E],
      ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    intro E _ _
    exact normal_tensor_localization_left (nonZeroDivisors A) (hA E)
  have hsep := separable_of_geometric_normal.{u, v} (k := k) (K := K) hK
  obtain ⟨hKD, hredKD⟩ := normal_tensor_of_separable_field.{u, v}
    (k := k) (K := K) (B := D) hsep (fun p _ ↦ by
      exact ⟨inferInstance,
        isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
          p.primeCompl_le_nonZeroDivisors⟩)
  let L := FractionRing D
  let : Field L := IsFractionRing.toField D
  have hAL := hA L
  have hfinite := finite_minimalPrimes_tensor (k := k) (A := A) (B := D)
  let : IsReduced (K ⊗[k] D) := hredKD
  let f : A ⊗[k] D →ₐ[k] K ⊗[k] D :=
    TensorProduct.map (IsScalarTower.toAlgHom k A K) (AlgHom.id k D)
  let : IsReduced (A ⊗[k] D) := isReduced_of_injective f
    (tensor_map_injective _ _ (IsFractionRing.injective A K) Function.injective_id)
  apply (reduced_normal_iff_integrallyClosed_totalFractions (A ⊗[k] D) hfinite).1.mpr
  exact integrallyClosed_tensor_of_normal_localizations (K := K) (L := L) hKD hAL

/-- The normal-domain case of tensor normality, allowing different universes for the
base field and both algebras. The test extensions live in their common universe.

Source: Stacks Project, Algebra, Tag 06DF, the normal-domain reduction.
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal-domain-case)

Lift the two algebras to the common universe and transport back at the end. Every finite-type
subalgebra of `B` lies in a finite-type normal subalgebra: its integral closure in its fraction
field is finite by Noether's finiteness theorem, and embeds in `B` by integral closedness.
These normal subalgebras form a directed cover, so filtered-colimit normality reduces to
finite-type `B`. Put `K = Frac(A)` and `L = Frac(B)`. Geometric normality makes `K/k`
separable. Express `K` as a directed union of smooth finite-type subalgebras; smooth base
change and filtered-colimit normality show `K ⊗ B` is normal. Also `A ⊗ L` is normal by
hypothesis. The injection into the Noetherian ring `K ⊗ B` gives finitely many minimal
primes for `C = A ⊗ B`; it also gives reducedness. Both partial localizations embed in the
total fraction ring of `C`. An integral total fraction belongs to both by their normality.
Their intersection is `C`: split the vector-space inclusion `A → K` by a linear retraction
and tensor this retraction with the identity. The equality of the two images in `K ⊗ L`
then yields the common preimage in `A ⊗ B`. Thus `C` is integrally closed in its total
fractions, and the reduced finite-minimal-prime criterion proves its normality.
-/
theorem normal_domain_case
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain B] [IsIntegrallyClosed B]
    (hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (A ⊗[k] B)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let A' := ULift.{max u w} A
  let B' := ULift.{max u v} B
  let eA : A' ≃ₐ[k] A := ULift.algEquiv
  let eB : B' ≃ₐ[k] B := ULift.algEquiv
  let : IsDomain A' := eA.injective.isDomain eA
  let : IsDomain B' := eB.injective.isDomain eB
  let : IsIntegrallyClosed A' := IsIntegrallyClosed.of_equiv eA.symm.toRingEquiv
  let : IsIntegrallyClosed B' := IsIntegrallyClosed.of_equiv eB.symm.toRingEquiv
  apply normal_equiv (TensorProduct.congr eA eB).toRingEquiv
  apply normal_domain_case_common.{u, max v w}
  · intro E _ _
    exact normal_equiv (TensorProduct.congr eA (AlgEquiv.refl : E ≃ₐ[k] E)).symm.toRingEquiv
      (hA E)
  · exact normal_equiv eB.symm.toRingEquiv hB

/-- If `A` is geometrically normal over a field `k` and `B` is normal, then
`A ⊗[k] B` is normal, with normality expressed at every prime localization.
Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).

At a prime of the tensor product, contract to primes of `A` and `B`. Localizing each
factor there gives normal domains. The first remains geometrically normal because
localization commutes with scalar extension. Apply `normal_domain_case` to these domains,
then descend normality through the two localizations to the original prime. The normality
of `A` itself follows by testing geometric normality on a universe lift of `k`.
-/
theorem isNormal_tensorProduct_of_geometricallyNormal
    (k : Type u) (A : Type v) (B : Type w)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r)    := by
  apply normal_tensor_of_normal_localizations_left
  intro p hp
  let A' := Localization.AtPrime p
  let : IsDomain A' := (normal_of_geometric hA p).1
  let : IsIntegrallyClosed A' := (normal_of_geometric hA p).2
  apply normal_tensor_of_normal_localizations_right
  intro q hq
  let B' := Localization.AtPrime q
  let : IsDomain B' := (hB q).1
  let : IsIntegrallyClosed B' := (hB q).2
  apply normal_domain_case
  · intro E _ _ r hr
    exact normal_tensor_localization_left (k := k) (A := A)
      (A' := Localization.AtPrime p) (B := E) p.primeCompl (hA E) r
  · exact normal_localization q.primeCompl hB

end Algebra
