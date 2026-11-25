/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section
universe u
open CategoryTheory
open scoped TensorProduct
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the constructed boundary at the tensor of the kernel.

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ; Homology, Tag 0111.

Proof: Put K = ker(q). Let P be the chosen projective resolution of N, with
augmentation epsilon and differential d : P1 -> P0. Its augmentation lift
e : P0 -> F defines D : P1 -> K with i D = e d, where i is the kernel inclusion.
The map s : K × P0 -> F, s(k,p) = i(k) + e(p), is surjective: lift q(f) through
epsilon to p and use (f - e(p), p). The relation map j(z) = (D(z), -d(z)) has
image ker(s), by exactness of d followed by epsilon.

Tensor right exactness now lifts (x,0), for any x in K tensor M killed by i tensor 1,
to z in P1 tensor M with (D tensor 1)(z) = x and (d tensor 1)(z) = 0. Thus z is a
cycle. The cokernel formula defining torKernelHomologyBoundary sends its homology
class to x; transport through the resolution isomorphism gives a Tor class with
boundary x. Conversely i D = e d shows that the boundary of every cycle is killed
by i tensor 1. Since the homology projection is epic, the same holds for the
homology boundary and hence torKernelBoundary. No projectivity of F is required.
(blueprint: lem-sc-p1-tor-kernel-boundary-construction-exact-right) -/
theorem tor_kernel_boundary_construction_exact_right
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Exact (torKernelBoundary M F N q hq)
      ((LinearMap.ker q).subtype.rTensor M) := by
  let P := projectiveResolution N
  let C := torKernelComplex M N
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let d := (P.complex.d 1 0).hom
  let e := (torKernelLift q hq).hom
  let ε := (P.π.f 0).hom
  let D := torKernelDifferential q hq
  let i := (LinearMap.ker q).subtype
  have he (p : P.complex.X 0) : q (e p) = ε p :=
    congrArg (fun f ↦ f.hom p) (torKernelLift_comp q hq)
  have hD (p : P.complex.X 1) : (D p : F) = e (d p) := rfl
  have hε : Function.Surjective ε :=
    (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance
  have hdε : Function.Exact d ε :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀
  -- The lift presents F as a quotient of ker(q) × P₀.
  let s : (LinearMap.ker q × P.complex.X 0) →ₗ[R] F :=
    i.comp (LinearMap.fst R _ _) + e.comp (LinearMap.snd R _ _)
  let j : P.complex.X 1 →ₗ[R] (LinearMap.ker q × P.complex.X 0) := D.prod (-d)
  have hs : Function.Surjective s := by
    intro f
    obtain ⟨p, hp⟩ := hε (q f)
    have hk : f - e p ∈ LinearMap.ker q := by
      simp only [LinearMap.mem_ker, map_sub, he, hp, sub_self]
    refine ⟨(⟨f - e p, hk⟩, p), ?_⟩
    change f - e p + e p = f
    simp
  have hjs : Function.Exact j s := by
    intro x
    constructor
    · intro hx
      have hx' : (x.1 : F) + e x.2 = 0 := hx
      have hp : ε x.2 = 0 := by
        have hh := congrArg q hx'
        simpa only [map_add, LinearMap.mem_ker.mp x.1.property, zero_add,
          he, map_zero] using hh
      obtain ⟨z, hz⟩ := (hdε x.2).mp hp
      refine ⟨-z, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change (D (-z) : F) = (x.1 : F)
        rw [map_neg, Submodule.coe_neg, hD, hz]
        exact eq_neg_of_add_eq_zero_left hx' |>.symm
      · change (-d) (-z) = x.2
        simp [hz]
    · rintro ⟨z, rfl⟩
      change (D z : F) + e (-d z) = 0
      rw [hD, map_neg, add_neg_cancel]
  -- The cokernel descent agrees with the lifted differential on cycles.
  have hp : C.homologyπ 1 ≫ torKernelHomologyBoundary M q hq =
      C.iCycles 1 ≫ ModuleCat.ofHom (D.rTensor M) :=
    (C.homologyIsCokernel 2 1
      ((ComplexShape.down ℕ).prev_eq' (by simp))).fac _ Limits.WalkingParallelPair.one
  have hDi : ModuleCat.ofHom D ≫ ModuleCat.ofHom i =
      P.complex.d 1 0 ≫ torKernelLift q hq := by
    ext z
    rfl
  -- Every cycle boundary is killed by the kernel inclusion after tensoring.
  have hb : torKernelHomologyBoundary M q hq ≫ ModuleCat.ofHom (i.rTensor M) = 0 := by
    rw [← cancel_epi (C.homologyπ 1), ← Category.assoc, hp, Category.assoc]
    change C.iCycles 1 ≫ (T.map (ModuleCat.ofHom D) ≫ T.map (ModuleCat.ofHom i)) = _
    rw [← T.map_comp, hDi, T.map_comp, ← Category.assoc]
    have hz : C.iCycles 1 ≫ T.map (P.complex.d 1 0) = 0 := C.iCycles_d 1 0
    rw [hz, Limits.zero_comp, Limits.comp_zero]
  intro x
  constructor
  · intro hx
    let a : LinearMap.ker q →ₗ[R] (LinearMap.ker q × P.complex.X 0) :=
      LinearMap.inl R _ _
    have hsa : s.comp a = i := by
      ext k
      change (k : F) + e 0 = (k : F)
      simp
    have hax : s.rTensor M (a.rTensor M x) = 0 := by
      rw [← LinearMap.rTensor_comp_apply, hsa]
      exact hx
    -- Lift (x, 0) through the tensored relation map; its second coordinate is zero.
    obtain ⟨z, hz⟩ := (rTensor_exact M hjs hs _).mp hax
    have hf : (LinearMap.fst R (LinearMap.ker q) (P.complex.X 0)).comp j = D := by
      ext p; rfl
    have hfa : (LinearMap.fst R (LinearMap.ker q) (P.complex.X 0)).comp a =
        LinearMap.id := by ext k; rfl
    have hDz : D.rTensor M z = x := by
      have hh := congrArg
        ((LinearMap.fst R (LinearMap.ker q) (P.complex.X 0)).rTensor M) hz
      simpa only [← LinearMap.rTensor_comp_apply, hf, hfa,
        LinearMap.rTensor_id_apply] using hh
    have hg : (LinearMap.snd R (LinearMap.ker q) (P.complex.X 0)).comp j = -d := by
      ext p; rfl
    have hga : (LinearMap.snd R (LinearMap.ker q) (P.complex.X 0)).comp a = 0 := by
      ext k; rfl
    have hdz : d.rTensor M z = 0 := by
      have hh := congrArg
        ((LinearMap.snd R (LinearMap.ker q) (P.complex.X 0)).rTensor M) hz
      simpa only [← LinearMap.rTensor_comp_apply, hg, hga, LinearMap.rTensor_neg,
        LinearMap.neg_apply, LinearMap.rTensor_zero, LinearMap.zero_apply,
        neg_eq_zero] using hh
    have hcycles : Function.Exact (C.iCycles 1).hom (C.d 1 0).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (ShortComplex.exact_of_f_is_kernel
          (ShortComplex.mk _ _ (C.iCycles_d 1 0)) (C.cyclesIsKernel 1 0 (by simp)))
    -- Pass the resulting cycle to homology and then back through the Tor isomorphism.
    obtain ⟨w, hw⟩ := (hcycles z).mp hdz
    let iso := P.isoLeftDerivedObj T 1
    refine ⟨iso.inv.hom ((C.homologyπ 1).hom w), ?_⟩
    change (iso.inv ≫ iso.hom ≫ torKernelHomologyBoundary M q hq).hom
      ((C.homologyπ 1).hom w) = x
    rw [Iso.inv_hom_id_assoc]
    change (C.homologyπ 1 ≫ torKernelHomologyBoundary M q hq).hom w = x
    rw [hp]
    change D.rTensor M ((C.iCycles 1).hom w) = x
    rw [hw, hDz]
  · rintro ⟨t, rfl⟩
    change (((P.isoLeftDerivedObj T 1).hom ≫ torKernelHomologyBoundary M q hq) ≫
      ModuleCat.ofHom (i.rTensor M)).hom t = 0
    rw [Category.assoc, hb, Limits.comp_zero]
    rfl

end CategoryTheory
