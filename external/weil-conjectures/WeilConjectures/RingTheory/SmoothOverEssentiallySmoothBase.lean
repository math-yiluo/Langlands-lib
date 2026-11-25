/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations
import WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink

@[expose] public section

universe u v w t

namespace Algebra

/-- Descent in one universe, using the diagram of 00CR and smooth descent of 0CAQ. -/
private theorem smooth_principal_localization_descent_sameUniverse
    (C A Q : Type u) [CommRing C] [CommRing A] [CommRing Q]
    [Algebra C A] [Algebra A Q] (S : Submonoid C) [IsLocalization S A]
    (hQ : Smooth A Q) :
    ∃ (s : S) (hCA : Algebra (Localization.Away (s : C)) A),
      letI := hCA
      IsScalarTower C (Localization.Away (s : C)) A ∧
      ∃ (P : Type u) (hP : CommRing P),
        letI := hP
        ∃ (hCP : Algebra (Localization.Away (s : C)) P),
          letI := hCP
          Smooth (Localization.Away (s : C)) P ∧
            Nonempty (Q ≃ₐ[A] (TensorProduct (Localization.Away (s : C)) A P)) := by
  classical
  obtain ⟨p, hp, hprod, hdir, hfil, rho, kappa, hrho, hid, hcomp, hkappa,
    hcompat, hbase, F, ei, eL, hF, hι⟩ :=
    CommRingCat.localization_colimit_principalLocalizations C S
  let := p
  let := hfil
  let eLA : LocalizedModule S C ≃ₐ[C] A := IsLocalization.algEquiv S _ _
  let e : (CategoryTheory.Limits.colimit F : CommRingCat) ≃+* A :=
    eL.commRingCatIsoToRingEquiv.trans eLA.toRingEquiv
  let f : CategoryTheory.Limits.colimit F ⟶ CommRingCat.of Q :=
    CommRingCat.ofHom ((algebraMap A Q).comp e.toRingHom)
  have hf : letI := f.hom.toAlgebra; Smooth (CategoryTheory.Limits.colimit F : CommRingCat) Q := by
    let L := (CategoryTheory.Limits.colimit F : CommRingCat)
    let : Algebra L A := e.toRingHom.toAlgebra
    let : Algebra L Q := f.hom.toAlgebra
    have : IsScalarTower L A Q := IsScalarTower.of_algebraMap_eq' rfl
    have : Smooth L L := by constructor <;> infer_instance
    let ee : L ≃ₐ[L] A := { e with commutes' := fun _ ↦ rfl }
    have : Smooth L A := Smooth.of_equiv ee
    let := hQ
    exact Smooth.comp L A Q
  obtain ⟨i, P, hP, g, hPsmooth, ⟨eQ⟩⟩ :=
    exists_smooth_algebra_of_filteredColimit F Q f hf
  let := hP
  let L := (CategoryTheory.Limits.colimit F : CommRingCat)
  let E := F.obj i
  let D := Localization.Away (i : C)
  let : Algebra E P := g.hom.toAlgebra
  let : Algebra E L := (CategoryTheory.Limits.colimit.ι F i).hom.toAlgebra
  let : Algebra L Q := f.hom.toAlgebra
  let : Algebra L A := e.toRingHom.toAlgebra
  let : Algebra E A := ((algebraMap L A).comp (algebraMap E L)).toAlgebra
  have : IsScalarTower E L A := IsScalarTower.of_algebraMap_eq' rfl
  let d : E ≃+* D := (ei i).commRingCatIsoToRingEquiv
  let : Algebra D E := d.symm.toRingHom.toAlgebra
  let : Algebra E D := d.toRingHom.toAlgebra
  let : Algebra D A := ((algebraMap E A).comp d.symm.toRingHom).toAlgebra
  let : Algebra D P := ((algebraMap E P).comp d.symm.toRingHom).toAlgebra
  have : IsScalarTower D E A := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower D E P := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower E D A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap E A x = algebraMap E A (d.symm (d x))
    rw [d.symm_apply_apply])
  have : IsScalarTower E D P := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap E P x = algebraMap E P (d.symm (d x))
    rw [d.symm_apply_apply])
  have : Smooth D D := by constructor <;> infer_instance
  let de : D ≃ₐ[D] E := { d.symm with commutes' := fun _ ↦ rfl }
  have : Smooth D E := Smooth.of_equiv de
  let := hPsmooth
  have : Smooth D P := Smooth.comp D E P
  have hCDA : IsScalarTower C D A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap C A x =
      eLA (eL.hom.hom ((CategoryTheory.Limits.colimit.ι F i).hom
        ((ei i).inv.hom (algebraMap C D x))))
    have hi := CategoryTheory.ConcreteCategory.congr_hom (hι i) (algebraMap C D x)
    change eL.hom.hom ((CategoryTheory.Limits.colimit.ι F i).hom
      ((ei i).inv.hom (algebraMap C D x))) =
      kappa i (algebraMap C D x) at hi
    have hb := RingHom.congr_fun (hbase i) x
    change kappa i (algebraMap C D x) = algebraMap C (LocalizedModule S C) x at hb
    rw [hi, hb]
    exact (eLA.commutes x).symm)
  have : _root_.TensorProduct.CompatibleSMul E D A P :=
    _root_.TensorProduct.CompatibleSMul.of_algebraMap_surjective A P d.surjective
  have : _root_.TensorProduct.CompatibleSMul D E A P :=
    _root_.TensorProduct.CompatibleSMul.of_algebraMap_surjective A P d.symm.surjective
  let ee : L ≃ₐ[L] A := { e with commutes' := fun _ ↦ rfl }
  let ec : (TensorProduct E L P) ≃ₐ[L] (TensorProduct E A P) :=
    TensorProduct.congr ee (AlgEquiv.refl)
  let eqA : Q ≃ₐ[A] (TensorProduct E A P) :=
    { (eQ.toRingEquiv.trans ec.toRingEquiv) with
      commutes' := by
        intro a
        obtain ⟨l, rfl⟩ := e.surjective a
        change ec (eQ (algebraMap A Q (e l))) = algebraMap A (TensorProduct E A P) (e l)
        change ec (eQ (algebraMap L Q l)) = algebraMap A (TensorProduct E A P) (e l)
        rw [eQ.commutes, ec.commutes]
        rfl }
  let et : (TensorProduct E A P) ≃ₐ[A] (TensorProduct D A P) :=
    TensorProduct.equivOfCompatibleSMul D E A A P
  exact ⟨i, inferInstance, hCDA, P, inferInstance, inferInstance, inferInstance,
    ⟨eqA.trans et⟩⟩

/-- Shrink the localized base and its finite-type algebra, then transport descent back. -/
private theorem smooth_principal_localization_descent
    (C : Type u) (A : Type v) (Q : Type w)
    [CommRing C] [CommRing A] [CommRing Q]
    [Algebra C A] [Algebra A Q] (S : Submonoid C) [IsLocalization S A]
    (hQ : Smooth A Q) :
    ∃ (s : S) (hCA : Algebra (Localization.Away (s : C)) A),
      letI := hCA
      IsScalarTower C (Localization.Away (s : C)) A ∧
      ∃ (P : Type (max u v w)) (hP : CommRing P),
        letI := hP
        ∃ (hCP : Algebra (Localization.Away (s : C)) P),
          letI := hCP
          Smooth (Localization.Away (s : C)) P ∧
            Nonempty (Q ≃ₐ[A] (TensorProduct (Localization.Away (s : C)) A P)) := by
  classical
  have : Small.{u} A :=
    small_of_surjective (IsLocalization.algEquiv S (Localization S) A).surjective
  let := hQ
  have : Small.{u} Q := FiniteType.small (R := A) (S := Q)
  let A₀ := Shrink.{u} A
  let Q₀ := Shrink.{u} Q
  let ea : A₀ ≃ₐ[C] A := Shrink.algEquiv C A
  let eq : Q₀ ≃ₐ[A] Q := Shrink.algEquiv A Q
  let : Algebra A₀ A := ea.toRingHom.toAlgebra
  let : Algebra A₀ Q := ((algebraMap A Q).comp ea.toRingHom).toAlgebra
  have : IsScalarTower A₀ A Q := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A₀ A Q₀ :=
    IsScalarTower.of_algebraMap_eq' (R := A₀) (S := A) (A := Q₀) (by
      ext x
      rfl)
  have : Smooth A₀ A₀ := by constructor <;> infer_instance
  let ea' : A₀ ≃ₐ[A₀] A := { ea.toRingEquiv with commutes' := fun _ ↦ rfl }
  have : Smooth A₀ A := Smooth.of_equiv ea'
  have : Smooth A₀ Q := Smooth.comp A₀ A Q
  have : Smooth A₀ Q₀ := Smooth.of_equiv (eq.restrictScalars A₀).symm
  have : IsLocalization S A₀ := IsLocalization.isLocalization_of_algEquiv S ea.symm
  obtain ⟨s, hDA, hCDA, P₀, hP, hDP, hPsmooth, ⟨e₀⟩⟩ :=
    smooth_principal_localization_descent_sameUniverse C A₀ Q₀ S inferInstance
  let D := Localization.Away (s : C)
  let : SMul D A₀ := hDA.toSMul
  let : Module D A₀ := @Algebra.toModule D A₀ _ _ hDA
  let := hDA
  let := hCDA
  let := hP
  let := hDP
  let := hPsmooth
  let : Algebra D A := (ea.toRingHom.comp (algebraMap D A₀)).toAlgebra
  have : IsScalarTower D A₀ A :=
    IsScalarTower.of_algebraMap_eq' (R := D) (S := A₀) (A := A) rfl
  have hCDA' : IsScalarTower C D A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap C A x = ea (algebraMap D A₀ (algebraMap C D x))
    rw [← IsScalarTower.algebraMap_apply C D A₀, ea.commutes])
  let ea₀ : A₀ ≃ₐ[A₀] A := { ea.toRingEquiv with commutes' := fun _ ↦ rfl }
  let ec : (TensorProduct D A₀ P₀) ≃ₐ[A₀] (TensorProduct D A P₀) :=
    TensorProduct.congr ea₀ AlgEquiv.refl
  let e₁ : Q ≃ₐ[A₀] (TensorProduct D A P₀) := ((eq.restrictScalars A₀).symm.trans e₀).trans ec
  let e₂ : Q ≃ₐ[A] (TensorProduct D A P₀) :=
    { e₁.toRingEquiv with
      commutes' := by
        intro a
        obtain ⟨a₀, rfl⟩ := ea.surjective a
        change e₁ (algebraMap A₀ Q a₀) = algebraMap A (TensorProduct D A P₀) (ea a₀)
        rw [e₁.commutes]
        rfl }
  let P := ULift.{max v w} P₀
  let ep : P ≃ₐ[D] P₀ := ULift.algEquiv
  have : Smooth D P := Smooth.of_equiv ep.symm
  let ec' : (TensorProduct D A P₀) ≃ₐ[A] (TensorProduct D A P) :=
    TensorProduct.congr AlgEquiv.refl ep.symm
  exact ⟨s, inferInstance, hCDA', P, inferInstance, inferInstance, inferInstance,
    ⟨e₂.trans ec'⟩⟩


/-- A smooth algebra over an essentially smooth base is a localization of a smooth
algebra over the original ring. Source: Stacks Project, Algebra, Tags 00CR and 0CAQ;
explicit reduction using Tags 00T3, 00TD, and 00DK.
(blueprint: lem-weil-pbc-smooth-over-essentially-smooth-base).

Proof: Write A as the localization of a smooth R-algebra C at S, using hA. Transport
Q and its A-algebra structure across this presentation. By 00CR, A is the filtered
colimit of C localized at s, for s in S. By 0CAQ, the smooth A-algebra Q descends
at some stage to a smooth C_s-algebra P, with Q isomorphic as an A-algebra to
A tensor over C_s with P. The map R to C_s is smooth (00T3), so P is smooth
over R by composition (00TD). The map C_s to A localizes at the image of S.
Base change (00DK) identifies P to Q with localization at the image of S in P.
The tensor balancing relation makes this map compatible with the R-structures.
Finally P is of finite type over R, hence small in universe u: a surjection from
polynomials in finitely many variables over R proves this. Transport P, its
submonoid, and its map to Q along a small model and lift to universe max u t.
These transports preserve smoothness, the localization property, and the scalar
tower. No localization of Q and no composition with a second localization is
asserted here. -/
theorem exists_smooth_localization_model
    (R : Type u) (A : Type v) (Q : Type w)
    [CommRing R] [CommRing A] [CommRing Q]
    [Algebra R A] [Algebra A Q] [Algebra R Q] [IsScalarTower R A Q]
    (hA : EssentiallySmooth R A) (hQ : Smooth A Q) :
    ∃ (P : Type (max u t)) (hP : CommRing P),
      letI : CommRing P := hP
      ∃ (hRP : Algebra R P),
        letI : Algebra R P := hRP
        ∃ (hPQ : Algebra P Q),
          letI : Algebra P Q := hPQ
          IsScalarTower R P Q ∧ Smooth R P ∧
            ∃ (S : Submonoid P), IsLocalization S Q := by
  classical
  obtain ⟨C, hC, hRC, hCsmooth, S, ⟨eA⟩⟩ := hA
  let := hC
  let := hRC
  let := hCsmooth
  let : Algebra C A :=
    (eA.symm.toRingHom.comp (algebraMap C (Localization S))).toAlgebra
  let eCA : Localization S ≃ₐ[C] A :=
    { eA.symm.toRingEquiv with commutes' := fun _ ↦ rfl }
  let : IsLocalization S A := IsLocalization.isLocalization_of_algEquiv S eCA
  have : IsScalarTower R C A := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (eA.symm.commutes r).symm)
  obtain ⟨s, hDA, hCDA, P, hP, hDP, hPsmooth, ⟨eQ⟩⟩ :=
    smooth_principal_localization_descent C A Q S hQ
  let D := Localization.Away (s : C)
  let := hDA
  let := hCDA
  let := hP
  let := hDP
  let := hPsmooth
  have : IsScalarTower R D A := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R A r = algebraMap D A (algebraMap R D r)
    rw [IsScalarTower.algebraMap_apply R C A,
      IsScalarTower.algebraMap_apply C D A, IsScalarTower.algebraMap_apply R C D])
  let : Algebra R P := ((algebraMap D P).comp (algebraMap R D)).toAlgebra
  have : IsScalarTower R D P := IsScalarTower.of_algebraMap_eq' rfl
  have : Smooth C D := Smooth.of_isLocalization_Away (s : C)
  have : Smooth R D := Smooth.comp R C D
  have : Smooth R P := Smooth.comp R D P
  have : IsLocalization (S.map (algebraMap C D)) A :=
    IsLocalization.isLocalization_of_submonoid_le D A (Submonoid.powers (s : C)) S
      (Submonoid.powers_le.mpr s.property)
  let T := TensorProduct D A P
  let : Algebra P T := TensorProduct.rightAlgebra
  let : Algebra P Q :=
    (eQ.symm.toRingHom.comp (algebraMap P T)).toAlgebra
  let ePQ : T ≃ₐ[P] Q :=
    { eQ.symm.toRingEquiv with commutes' := fun _ ↦ rfl }
  have : IsLocalization ((S.map (algebraMap C D)).map (algebraMap D P)) T :=
    IsLocalization.tensorRight A (S.map (algebraMap C D))
  have : IsLocalization ((S.map (algebraMap C D)).map (algebraMap D P)) Q :=
    IsLocalization.isLocalization_of_algEquiv _ ePQ
  have : IsScalarTower R P Q := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R Q r = eQ.symm (algebraMap P T (algebraMap R P r))
    rw [IsScalarTower.algebraMap_apply R D P]
    change algebraMap R Q r =
      eQ.symm (TensorProduct.includeRight (algebraMap D P (algebraMap R D r)))
    rw [TensorProduct.includeRight.commutes, IsScalarTower.algebraMap_apply D A T,
      ← IsScalarTower.algebraMap_apply R D A, eQ.symm.commutes,
      ← IsScalarTower.algebraMap_apply R A Q])
  have : Small.{max u t} P := FiniteType.small (R := R) (S := P)
  let P' := Shrink.{max u t} P
  let eP : P' ≃ₐ[R] P := Shrink.algEquiv R P
  let : Algebra P' Q := ((algebraMap P Q).comp eP.toRingHom).toAlgebra
  have : IsScalarTower R P' Q := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R Q r = algebraMap P Q (eP (algebraMap R P' r))
    rw [eP.commutes]
    exact IsScalarTower.algebraMap_apply R P Q r)
  have : Smooth R P' := Smooth.of_equiv eP.symm
  refine ⟨P', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ((S.map (algebraMap C D)).map (algebraMap D P)).map eP.symm.toRingHom, ?_⟩
  exact IsLocalization.isLocalization_of_base_ringEquiv _ Q eP.symm.toRingEquiv

end Algebra
