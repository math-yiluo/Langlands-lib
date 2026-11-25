/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Smooth.IntegralClosure
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-!
# Integral closure and ind-etale base change

Source: Stacks Project, Algebra, Tag 0CBF
(blueprint: lem-dl-a1-integral-closure-strict-etale-base-change).
-/

@[expose] public section
set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RingHom

open CategoryTheory CategoryTheory.Limits

-- Transfer the elementwise tensor-colimit API to the specified colimit cocone.
private theorem tensor_rep
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (P : ColimitPresentation I (CommAlgCat.of R S))
    (N : Type w) [AddCommGroup N] [Module R N] (x : S ⊗[R] N) :
    ∃ (i : I) (y : P.diag.obj i ⊗[R] N),
      LinearMap.rTensor N (P.ι.app i).hom.toLinearMap y = x := by
  classical
  let : HasColimit P.diag := P.hasColimit
  let e : (colimit P.diag : CommAlgCat R) ≃ₐ[R] S := CommAlgCat.algEquivOfIso
    ((colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit)
  let et := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R N)
  obtain ⟨i, y, hy⟩ := (CommAlgCat.filteredColimit_tensorProduct_elementwise R P.diag N).1
    (et.symm x)
  refine ⟨i, y, ?_⟩
  have he (i : I) : e.toAlgHom.comp (colimit.ι P.diag i).hom = (P.ι.app i).hom := by
    exact congrArg CommAlgCat.Hom.hom ((colimit.isColimit P.diag).comp_coconePointUniqueUpToIso_hom
      P.isColimit i)
  have hcomp : et.toLinearMap.comp
      (LinearMap.rTensor N (colimit.ι P.diag i).hom.toLinearMap) =
      LinearMap.rTensor N (P.ι.app i).hom.toLinearMap := by
    ext a n
    exact congrArg (fun z ↦ z ⊗ₜ[R] n) (DFunLike.congr_fun (he i) a)
  calc
    _ = et (LinearMap.rTensor N (colimit.ι P.diag i).hom.toLinearMap y) :=
      (DFunLike.congr_fun hcomp y).symm
    _ = x := by rw [hy, et.apply_symm_apply]

private theorem tensor_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (P : ColimitPresentation I (CommAlgCat.of R S))
    (N : Type w) [AddCommGroup N] [Module R N] (i : I)
    (y : P.diag.obj i ⊗[R] N)
    (hy : LinearMap.rTensor N (P.ι.app i).hom.toLinearMap y = 0) :
    ∃ (j : I) (f : i ⟶ j), LinearMap.rTensor N (P.diag.map f).hom.toLinearMap y = 0 := by
  classical
  let : HasColimit P.diag := P.hasColimit
  let e : (colimit P.diag : CommAlgCat R) ≃ₐ[R] S := CommAlgCat.algEquivOfIso
    ((colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit)
  let et := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R N)
  apply (CommAlgCat.filteredColimit_tensorProduct_elementwise R P.diag N).2 i y
  apply et.injective
  rw [map_zero]
  have he : e.toAlgHom.comp (colimit.ι P.diag i).hom = (P.ι.app i).hom := by
    exact congrArg CommAlgCat.Hom.hom ((colimit.isColimit P.diag).comp_coconePointUniqueUpToIso_hom
      P.isColimit i)
  have hcomp : et.toLinearMap.comp
      (LinearMap.rTensor N (colimit.ι P.diag i).hom.toLinearMap) =
      LinearMap.rTensor N (P.ι.app i).hom.toLinearMap := by
    ext a n
    exact congrArg (fun z ↦ z ⊗ₜ[R] n) (DFunLike.congr_fun he a)
  exact (DFunLike.congr_fun hcomp y).trans hy

-- The finite support of a polynomial fits in one stage; its monic lift stays monic.
private theorem polynomial_rep
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (P : ColimitPresentation I (CommAlgCat.of R S))
    (p : Polynomial S) (hp : p.Monic) :
    ∃ (i : I) (q : Polynomial (P.diag.obj i)),
      q.map (P.ι.app i).hom.toRingHom = p ∧ q.Monic := by
  classical
  have hc := isColimitOfPreserves (forget (CommAlgCat R)) P.isColimit
  choose i a ha using fun n : p.support ↦
    Types.jointly_surjective_of_isColimit hc (p.coeff n)
  let co := IsFiltered.cocone (Discrete.functor i)
  have hcoeff (n : ℕ) : p.coeff n ∈ (P.ι.app co.pt).hom.toRingHom.range := by
    by_cases hn : n ∈ p.support
    · refine ⟨(P.diag.map (co.ι.app ⟨⟨n, hn⟩⟩)).hom (a ⟨n, hn⟩), ?_⟩
      have hw := ConcreteCategory.congr_hom (P.w (co.ι.app ⟨⟨n, hn⟩⟩)) (a ⟨n, hn⟩)
      exact hw.trans (ha ⟨n, hn⟩)
    · exact ⟨0, by
      rw [Polynomial.notMem_support_iff.mp hn]; exact map_zero (P.ι.app co.pt).hom.toRingHom⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (p.lifts_iff_coeff_lifts.mpr hcoeff) hp
  exact ⟨co.pt, q, hq, hqm⟩

private theorem rTensor_apply
    {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D]
    (f : A →ₐ[R] B) (x : A ⊗[R] D) :
    Algebra.TensorProduct.rTensor D f x = LinearMap.rTensor D f.toLinearMap x := by
  have h : (Algebra.TensorProduct.rTensor D f).toLinearMap =
      LinearMap.rTensor D f.toLinearMap := by
    ext a d
    rfl
  exact DFunLike.congr_fun h x

private theorem eval_tensor_map
    {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D]
    (f : A →ₐ[R] B) (x : A ⊗[R] D) (p : Polynomial A) :
    Algebra.TensorProduct.rTensor D f (Polynomial.aeval x p) =
      Polynomial.aeval (Algebra.TensorProduct.rTensor D f x) (p.map f.toRingHom) := by
  change (Algebra.TensorProduct.rTensor D f).toRingHom
    (p.eval₂ (algebraMap A _) x) =
      (p.map f.toRingHom).eval₂ (algebraMap B _) _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1

private theorem of_presentation
    {R S : Type u} {D : Type w} [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (P : ColimitPresentation I (CommAlgCat.of R S))
    (hP : ∀ i, Algebra.Etale R (P.diag.obj i)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S D) := by
  classical
  let α (i : I) : P.diag.obj i →ₐ[R] S := (P.ι.app i).hom
  have : Module.Flat R S := by
    rw [Module.Flat.iff_ind_flat]
    refine ⟨I, inferInstance, inferInstance, P, fun i ↦ ?_⟩
    rw [CommAlgCat.flat_iff]
    have := hP i
    infer_instance
  refine ⟨TensorProduct.toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨i, pi, hpi, hpim⟩ := polynomial_rep P p hp
  obtain ⟨j, xj, hxj⟩ := tensor_rep P D x
  change pi.map (α i).toRingHom = p at hpi
  change LinearMap.rTensor D (α j).toLinearMap xj = x at hxj
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  let xk := Algebra.TensorProduct.rTensor D (P.diag.map g).hom xj
  let pk := pi.map (P.diag.map f).hom.toRingHom
  have hleg {a b : I} (h : a ⟶ b) :
      (α b).comp (P.diag.map h).hom = (α a) := by
    exact congrArg CommAlgCat.Hom.hom (P.w h)
  have htx : Algebra.TensorProduct.rTensor D (α k) xk = x := by
    change (Algebra.TensorProduct.rTensor D (α k)).comp
      (Algebra.TensorProduct.rTensor D (P.diag.map g).hom) xj = x
    simpa only [Algebra.TensorProduct.rTensor, ← Algebra.TensorProduct.map_comp,
      AlgHom.comp_id, hleg, rTensor_apply] using hxj
  have htp : pk.map (α k).toRingHom = p := by
    dsimp only [pk]
    rw [Polynomial.map_map]
    change pi.map ((α k).comp (P.diag.map f).hom).toRingHom = p
    rw [hleg, hpi]
  have hz : LinearMap.rTensor D (α k).toLinearMap
      (Polynomial.aeval xk pk) = 0 := by
    change Algebra.TensorProduct.rTensor D (α k) _ = 0
    rw [eval_tensor_map, htx, htp]
    exact hpx
  obtain ⟨l, h, hh⟩ := tensor_zero P D k (Polynomial.aeval xk pk) hz
  let xl := Algebra.TensorProduct.rTensor D (P.diag.map h).hom xk
  have hxl : _root_.IsIntegral (P.diag.obj l) xl := by
    refine ⟨pk.map (P.diag.map h).hom.toRingHom, (hpim.map _).map _, ?_⟩
    change Polynomial.aeval xl _ = 0
    rw [← eval_tensor_map]
    simpa only [rTensor_apply] using hh
  have := hP l
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := P.diag.obj l) (B := D)).2 ⟨xl, hxl⟩
  refine ⟨Algebra.TensorProduct.rTensor (integralClosure R D) (α l) y, ?_⟩
  apply Subtype.ext
  have hnat :
      (((integralClosure S (S ⊗[R] D)).val.restrictScalars R).comp
        ((TensorProduct.toIntegralClosure R S D).restrictScalars R)).comp
          (Algebra.TensorProduct.rTensor (integralClosure R D) (α l)) =
      (Algebra.TensorProduct.rTensor D (α l)).comp
        (((integralClosure (P.diag.obj l) (P.diag.obj l ⊗[R] D)).val.restrictScalars R).comp
          ((TensorProduct.toIntegralClosure R (P.diag.obj l) D).restrictScalars R)) := by
    ext a <;> simp [TensorProduct.toIntegralClosure]
  have hy' := congrArg Subtype.val hy
  have hxlx : Algebra.TensorProduct.rTensor D (α l) xl = x := by
    change (Algebra.TensorProduct.rTensor D (α l)).comp
      (Algebra.TensorProduct.rTensor D (P.diag.map h).hom) xk = x
    simpa only [Algebra.TensorProduct.rTensor, ← Algebra.TensorProduct.map_comp,
      AlgHom.comp_id, hleg] using htx
  exact (DFunLike.congr_fun hnat y).trans ((congrArg
    (Algebra.TensorProduct.rTensor D (α l)) hy').trans hxlx)

-- Transport the comparison along an algebra equivalence without changing its map.
private theorem of_algEquiv
    {R S T D : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing D]
    [Algebra R S] [Algebra R T] [Algebra R D] (e : S ≃ₐ[R] T)
    (H : Function.Bijective (TensorProduct.toIntegralClosure R T D)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S D) := by
  let ed := Algebra.TensorProduct.congr e (AlgEquiv.refl (R := R) (A₁ := D))
  let eb := Algebra.TensorProduct.congr e
    (AlgEquiv.refl (R := R) (A₁ := integralClosure R D))
  have hsquare :
      ed.toAlgHom.comp (((integralClosure S (S ⊗[R] D)).val.restrictScalars R).comp
        ((TensorProduct.toIntegralClosure R S D).restrictScalars R)) =
      (((integralClosure T (T ⊗[R] D)).val.restrictScalars R).comp
        ((TensorProduct.toIntegralClosure R T D).restrictScalars R)).comp eb.toAlgHom := by
    ext a <;> simp [TensorProduct.toIntegralClosure, ed, eb]
  constructor
  · intro a b hab
    apply eb.injective
    apply H.1
    apply Subtype.ext
    exact (DFunLike.congr_fun hsquare a).symm.trans
      ((congrArg ed (congrArg Subtype.val hab)).trans (DFunLike.congr_fun hsquare b))
  · rintro ⟨x, hx⟩
    have hcomm : (algebraMap T (T ⊗[R] D)).comp e.toRingHom =
        ed.toRingHom.comp (algebraMap S (S ⊗[R] D)) := by
      ext s
      simp [ed]
    have hint := IsIntegral.map_of_comp_eq e.toRingHom ed.toRingHom hcomm hx
    obtain ⟨y, hy⟩ := H.2 ⟨ed x, hint⟩
    refine ⟨eb.symm y, Subtype.ext (ed.injective ?_)⟩
    have ht := DFunLike.congr_fun hsquare (eb.symm y)
    change ed ((TensorProduct.toIntegralClosure R S D (eb.symm y)).val) =
      (TensorProduct.toIntegralClosure R T D (eb (eb.symm y))).val at ht
    rw [eb.apply_symm_apply] at ht
    exact ht.trans (congrArg Subtype.val hy)

/-- Integral closure commutes with base change by an ind-etale algebra.

Source: Stacks Project, Algebra, Tag 0CBF
(blueprint: lem-dl-a1-integral-closure-strict-etale-base-change).
The canonical map `s ⊗ b ↦ s ⊗ b` is `TensorProduct.toIntegralClosure R S D`;
its bijectivity is the asserted `S`-algebra isomorphism.

Proof (Stacks 0CBF, with etale stages by Stacks 03GE):
1. Lift to one universe: put `A = ULift R`, `T = ULift S`. By
   definition-ind-etale-pro-etale-weakly, `T` has a small filtered presentation
   `P : T = colim T_i` by etale (hence smooth) `A`-algebras.
2. Same-universe case (`of_presentation`), for any `A`-algebra `D'`. Transport
   lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise from the chosen
   colimit to `P` along the unique cocone isomorphism (`tensor_rep`,
   `tensor_zero`): every tensor has a stage representative, and one mapping
   to zero vanishes after a transition.
3. Injectivity: each etale stage is flat, so `T` is flat over `A`
   (lem-weil-pbc-flat-ring-map-iff-ind-flat, `Module.Flat.iff_ind_flat`), and
   `TensorProduct.toIntegralClosure_injective_of_flat` applies.
4. Surjectivity: for `x` integral over `T` by a monic `p`, lift `p` to a monic
   polynomial at a stage (`polynomial_rep`, via
   `Polynomial.lifts_and_natDegree_eq_and_monic`) and `x` to a stage; at a
   common stage `k` the value maps to zero (evaluation commutes with tensor
   maps), so it vanishes at some `l`. Then `x_l` is integral over `T_l`, and
   the etale stage (lem-dl-a1-integral-closure-etale-base-change,
   `TensorProduct.toIntegralClosure_bijective_of_smooth`) lifts it; by
   naturality of the comparison on pure tensors its image in `T ⊗ B` maps to `x`.
5. Apply step 2 to `A → T` with `D' = A ⊗[R] D`; since `R → A` is a ring
   isomorphism, hence smooth, `TensorProduct.toIntegralClosure_bijective_of_tower`
   gives the result for `R → T`. Transport along `ULift.algEquiv : T ≃ₐ[R] S`
   (`of_algEquiv`), which commutes with the comparison and maps monic equations.
A bijective algebra map is an algebra isomorphism.
No injectivity, normality, domain, Noetherian or finiteness hypothesis is used.
-/
theorem integralClosure_bijective_of_indEtale
    {R : Type u} {S : Type v} {D : Type w}
    [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D]
    (hS : RingHom.IndEtaleAcrossUniverses (algebraMap R S)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S D) := by
  let A := ULift.{v} R
  let T := ULift.{u} S
  let : Algebra A T := ULift.algebra' R T
  have hi : (algebraMap A T).IndEtale := hS
  have : Algebra.IndEtale A T := (RingHom.IndEtale.algebraMap_iff A T).mp hi
  obtain ⟨I, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := T)
  have hAT := of_presentation (D := A ⊗[R] D) P hP
  have : IsScalarTower R A T := inferInstance
  have : Algebra.Smooth R A := by
    apply (RingHom.smooth_algebraMap).mp
    exact RingHom.Smooth.of_bijective (ULift.ringEquiv.symm : R ≃+* A).bijective
  have hRT : Function.Bijective (TensorProduct.toIntegralClosure R T D) :=
    TensorProduct.toIntegralClosure_bijective_of_tower
      TensorProduct.toIntegralClosure_bijective_of_smooth hAT
  exact of_algEquiv (ULift.algEquiv : T ≃ₐ[R] S).symm hRT

end RingHom
