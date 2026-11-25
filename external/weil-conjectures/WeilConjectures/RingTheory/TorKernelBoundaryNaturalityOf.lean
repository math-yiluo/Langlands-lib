/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction

/-!
# Naturality of the constructed Tor kernel boundary

Source: Stacks Project, Algebra, Tags 00LZ and 00M0.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_cycles_naturality
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    {F N F' N' : ModuleCat.{u} R} (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (a : F →ₗ[R] F') (b : N →ₗ[R] N')
    (c : LinearMap.ker q →ₗ[R] LinearMap.ker q')
    (hab : q'.comp a = b.comp q)
    (hc : ∀ x : LinearMap.ker q, (c x : F') = a (x : F)) :
    let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
    let φ := ProjectiveResolution.lift (ModuleCat.ofHom b)
      (projectiveResolution N) (projectiveResolution N')
    (torKernelComplex M N).iCycles 1 ≫
        T.map (φ.f 1) ≫ ModuleCat.ofHom ((torKernelDifferential q' hq').rTensor M) =
      (torKernelComplex M N).iCycles 1 ≫
        ModuleCat.ofHom ((torKernelDifferential q hq).rTensor M) ≫
          ModuleCat.ofHom (c.rTensor M) := by
  dsimp only
  let P := projectiveResolution N
  let P' := projectiveResolution N'
  let φ := ProjectiveResolution.lift (ModuleCat.ofHom b) P P'
  let e := torKernelLift q hq
  let e' := torKernelLift q' hq'
  let k₀ : P.complex.X 0 →ₗ[R] F' := (e ≫ ModuleCat.ofHom a - φ.f 0 ≫ e').hom
  have hk₀ (x : P.complex.X 0) : k₀ x ∈ LinearMap.ker q' := by
    change ((e ≫ ModuleCat.ofHom a - φ.f 0 ≫ e') ≫ ModuleCat.ofHom q').hom x = 0
    have ha : ModuleCat.ofHom a ≫ ModuleCat.ofHom q' =
        ModuleCat.ofHom q ≫ ModuleCat.ofHom b := ModuleCat.hom_ext hab
    rw [Preadditive.sub_comp, Category.assoc, ha, ← Category.assoc e,
      torKernelLift_comp, Category.assoc, torKernelLift_comp,
      ProjectiveResolution.lift_commutes_zero, sub_self]
    rfl
  let k := k₀.codRestrict (LinearMap.ker q') hk₀
  have hd : ModuleCat.ofHom (torKernelDifferential q hq) ≫ ModuleCat.ofHom c -
      φ.f 1 ≫ ModuleCat.ofHom (torKernelDifferential q' hq') =
        P.complex.d 1 0 ≫ ModuleCat.ofHom k := by
    ext x
    change (c (torKernelDifferential q hq x) : F') -
      (torKernelDifferential q' hq' (φ.f 1 x) : F') = k₀ (P.complex.d 1 0 x)
    rw [hc]
    change ((P.complex.d 1 0 ≫ e ≫ ModuleCat.ofHom a) -
      (φ.f 1 ≫ P'.complex.d 1 0 ≫ e')).hom x =
      (P.complex.d 1 0 ≫ (e ≫ ModuleCat.ofHom a - φ.f 0 ≫ e')).hom x
    rw [Preadditive.comp_sub, ← Category.assoc (φ.f 1), φ.comm]
    simp only [Category.assoc]
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  have ht := congrArg (fun f => (torKernelComplex M N).iCycles 1 ≫ T.map f) hd
  simp only [T.map_sub, T.map_comp, Preadditive.comp_sub, ← Category.assoc] at ht
  have hz : (torKernelComplex M N).iCycles 1 ≫ T.map (P.complex.d 1 0) = 0 :=
    (torKernelComplex M N).iCycles_d 1 0
  rw [hz, zero_comp] at ht
  exact (sub_eq_zero.mp ht).symm

set_option backward.isDefEq.respectTransparency false in
/-- The constructed boundary is natural; exactness alone is not a naturality hypothesis.

Source: Stacks Project, Algebra, Tags 00LZ and 00M0.
Proof: lift b between the projective resolutions. The difference between the two
augmentation lifts factors through ker(q'). Its contribution to the boundary
factors through the differential and hence vanishes on tensor cycles. The cycle
maps thus commute, so their descents to homology commute. Resolution comparison
identifies the induced homology map with Tor₁(b,M).
(blueprint: lem-sc-p1-tor-kernel-boundary-naturality-of) -/
theorem tor_kernel_boundary_naturality_of
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
        (hq : Function.Surjective q) (hq' : Function.Surjective q')
        (a : F →ₗ[R] F') (b : N →ₗ[R] N')
        (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
      q'.comp a = b.comp q →
      (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
      ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
        torKernelBoundary M F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom b)).app M).hom t) =
        c.rTensor M (torKernelBoundary M F N q hq t) := by
  intro F N F' N' q q' hq hq' a b c hab hc t
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let P := projectiveResolution N
  let P' := projectiveResolution N'
  let φ := ProjectiveResolution.lift (ModuleCat.ofHom b) P P'
  have hh : HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map φ) 1 ≫
      torKernelHomologyBoundary M q' hq' =
        torKernelHomologyBoundary M q hq ≫ ModuleCat.ofHom (c.rTensor M) := by
    rw [← cancel_epi ((torKernelComplex M N).homologyπ 1)]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    have hp (X Y : ModuleCat.{u} R) (f : X →ₗ[R] Y) (hf : Function.Surjective f) :
        (torKernelComplex M Y).homologyπ 1 ≫ torKernelHomologyBoundary M f hf =
          (torKernelComplex M Y).iCycles 1 ≫
            ModuleCat.ofHom ((torKernelDifferential f hf).rTensor M) := by
      exact ((torKernelComplex M Y).homologyIsCokernel 2 1
        ((ComplexShape.down ℕ).prev_eq' (by simp))).fac _ WalkingParallelPair.one
    change HomologicalComplex.cyclesMap ((T.mapHomologicalComplex _).map φ) 1 ≫
      ((torKernelComplex M N').homologyπ 1 ≫ torKernelHomologyBoundary M q' hq') = _
    rw [hp, ← Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, hp]
    exact boundary_cycles_naturality M q q' hq hq' a b c hab hc
  have hi := P.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom b) P' φ
    (ProjectiveResolution.lift_commutes_zero _ _ _) T 1
  have h : ((Tor' (ModuleCat R) 1).map (ModuleCat.ofHom b)).app M ≫
      ModuleCat.ofHom (torKernelBoundary M F' N' q' hq') =
        ModuleCat.ofHom (torKernelBoundary M F N q hq) ≫ ModuleCat.ofHom (c.rTensor M) := by
    change (T.leftDerived 1).map (ModuleCat.ofHom b) ≫
      ((P'.isoLeftDerivedObj T 1).hom ≫ torKernelHomologyBoundary M q' hq') =
        ((P.isoLeftDerivedObj T 1).hom ≫ torKernelHomologyBoundary M q hq) ≫ _
    rw [← Category.assoc, hi, Category.assoc]
    change (P.isoLeftDerivedObj T 1).hom ≫
      (HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map φ) 1 ≫ _) = _
    rw [hh]
    simp only [Category.assoc]
  exact congrArg (fun f => f.hom t) h

end CategoryTheory
