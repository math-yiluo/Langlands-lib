/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.TorKernelBoundaryConstruction
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Comparing the horseshoe connecting map with the constructed Tor boundary

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ; Homology, Tag 0111.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The connecting map of any augmentation-compatible split resolution sequence,
transported to Tor and the tensor of the kernel, is the negative of the explicit boundary.

Source: Stacks Project, Algebra, Tags 00M0 and 00LZ; Homology, Tag 0111.

Proof: Let P be the chosen projective resolution of N. Lift its augmentation to a
comparison c : P -> C. Use the degreewise sections of b to lift c in degrees zero
and one to maps l0 : P0 -> B0 and l1 : P1 -> B1. The chain identity for c shows
that dB l1 - l0 dP lies in ker b0, hence factors uniquely through a0, say as a0 t.
The augmentation identities imply i epsilonA t = -epsilonB l0 dP. Therefore
 epsilonA t is the negative kernel restriction of the differential lifted using
 e0 = epsilonB l0. The chosen lift e used by torKernelBoundary differs from e0
by a map k : P0 -> ker q. Thus on a tensor cycle z the two explicit boundaries
agree, since their difference is (k tensor 1)(dP tensor 1)(z) = 0.

The tensor of l1 lifts (c1 tensor 1)(z). Its differential equals (a0 tensor 1)
(t tensor 1)(z), so the homology snake formula sends the class of that cycle to
[(t tensor 1)(z)]. Applying the augmentation of A gives the negative explicit
boundary. In degree zero, homology inclusion followed by fromLeftDerivedZero'
is exactly the map induced by that augmentation. Resolution comparison in degree
one identifies the induced map of c with the Tor-to-homology isomorphism for C.
Every homology class has a cycle representative, and the explicit map kills
boundaries by torKernelTensor_boundary. Consequently this cycle equality descends
to the displayed equality of maps. This argument uses no projectivity of F.
(blueprint: lem-sc-p1-tor-kernel-boundary-horseshoe-comparison) -/
theorem tor_kernel_boundary_horseshoe_comparison
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q)
    (A : ProjectiveResolution (ModuleCat.of R (LinearMap.ker q)))
    (B : ProjectiveResolution F) (C : ProjectiveResolution N)
    (a : A.complex ⟶ B.complex) (b : B.complex ⟶ C.complex) (w : a ≫ b = 0)
    (ha : a.f 0 ≫ B.π.f 0 = A.π.f 0 ≫ ModuleCat.ofHom (LinearMap.ker q).subtype)
    (hb : b.f 0 ≫ C.π.f 0 = B.π.f 0 ≫ ModuleCat.ofHom q)
    (hs : ∀ n, Nonempty ((ShortComplex.mk a b w).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).Splitting)
    (hS : ((ShortComplex.mk a b w).map
      (((MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ))).ShortExact) :
    (C.isoLeftDerivedObj ((MonoidalCategory.tensoringRight (ModuleCat R)).obj M) 1).hom ≫
      hS.δ 1 0 (by simp) ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫
      A.fromLeftDerivedZero' ((MonoidalCategory.tensoringRight (ModuleCat R)).obj M) =
        -ModuleCat.ofHom (torKernelBoundary M F N q hq) := by
  classical
  let P := projectiveResolution N
  let T := (MonoidalCategory.tensoringRight (ModuleCat R)).obj M
  let PC := torKernelComplex M N
  let AC := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj A.complex
  let BC := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj B.complex
  let CC := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj C.complex
  let c := ProjectiveResolution.lift (𝟙 N) P C
  let s₀ : C.complex.X 0 ⟶ B.complex.X 0 := (hs 0).some.s
  let s₁ : C.complex.X 1 ⟶ B.complex.X 1 := (hs 1).some.s
  let r₀ : B.complex.X 0 ⟶ A.complex.X 0 := (hs 0).some.r
  let l₀ : P.complex.X 0 ⟶ B.complex.X 0 := c.f 0 ≫ s₀
  let l₁ : P.complex.X 1 ⟶ B.complex.X 1 := c.f 1 ≫ s₁
  have hl₀ : l₀ ≫ b.f 0 = c.f 0 := by
    have hh : s₀ ≫ b.f 0 = 𝟙 _ := (hs 0).some.s_g
    dsimp only [l₀]
    rw [Category.assoc, hh, Category.comp_id]
  have hl₁ : l₁ ≫ b.f 1 = c.f 1 := by
    have hh : s₁ ≫ b.f 1 = 𝟙 _ := (hs 1).some.s_g
    dsimp only [l₁]
    rw [Category.assoc, hh, Category.comp_id]
  let v : P.complex.X 1 ⟶ B.complex.X 0 :=
    l₁ ≫ B.complex.d 1 0 - P.complex.d 1 0 ≫ l₀
  have hv : v ≫ b.f 0 = 0 := by
    dsimp only [v]
    rw [Preadditive.sub_comp, Category.assoc, ← b.comm, ← Category.assoc,
      hl₁, Category.assoc, hl₀, c.comm, sub_self]
  let t : P.complex.X 1 ⟶ A.complex.X 0 := v ≫ r₀
  have ht : t ≫ a.f 0 = v := by
    have hid : r₀ ≫ a.f 0 + b.f 0 ≫ s₀ = 𝟙 (B.complex.X 0) := (hs 0).some.id
    have hh := congrArg (fun f ↦ v ≫ f) hid
    rw [Preadditive.comp_add, ← Category.assoc v (b.f 0), hv,
      zero_comp, add_zero, Category.comp_id] at hh
    exact hh
  let e₀ : P.complex.X 0 ⟶ F := l₀ ≫ B.π.f 0
  have he₀ : e₀ ≫ ModuleCat.ofHom q = P.π.f 0 := by
    dsimp only [e₀]
    rw [Category.assoc, ← hb, ← Category.assoc, hl₀,
      ProjectiveResolution.lift_commutes_zero]
    exact Category.comp_id (P.π.f 0 : P.complex.X 0 ⟶ N)
  let k₀ := (torKernelLift q hq - e₀).hom
  have hk₀ (x : P.complex.X 0) : k₀ x ∈ LinearMap.ker q := by
    change ((torKernelLift q hq - e₀) ≫ ModuleCat.ofHom q).hom x = 0
    rw [Preadditive.sub_comp, torKernelLift_comp, he₀, sub_self]
    rfl
  let k := k₀.codRestrict (LinearMap.ker q) hk₀
  have htε : t ≫ A.π.f 0 ≫ ModuleCat.ofHom (LinearMap.ker q).subtype =
      -(P.complex.d 1 0 ≫ e₀) := by
    rw [← ha, ← Category.assoc t, ht]
    dsimp only [v, e₀]
    rw [Preadditive.sub_comp, Category.assoc l₁,
      B.complex_d_comp_π_f_zero, comp_zero, zero_sub]
    simp only [Category.assoc]
  let D : P.complex.X 1 ⟶ ModuleCat.of R (LinearMap.ker q) :=
    ModuleCat.ofHom (torKernelDifferential q hq)
  let εA : A.complex.X 0 ⟶ ModuleCat.of R (LinearMap.ker q) := A.π.f 0
  have hD : D + t ≫ εA =
      P.complex.d 1 0 ≫ ModuleCat.ofHom k := by
    ext x
    change (torKernelDifferential q hq x : F) + ((t ≫ εA).hom x : F) =
      k₀ (P.complex.d 1 0 x)
    have hh := congrArg (fun f ↦ f.hom x) htε
    change ((t ≫ εA).hom x : F) = -(P.complex.d 1 0 ≫ e₀).hom x at hh
    rw [hh]
    change (torKernelLift q hq).hom (P.complex.d 1 0 x) +
      -e₀.hom (P.complex.d 1 0 x) =
        (torKernelLift q hq).hom (P.complex.d 1 0 x) - e₀.hom (P.complex.d 1 0 x)
    exact (sub_eq_add_neg _ _).symm
  have hcycle : PC.iCycles 1 ≫ T.map t ≫ T.map (A.π.f 0) =
      -(PC.iCycles 1 ≫ ModuleCat.ofHom ((torKernelDifferential q hq).rTensor M)) := by
    have hh := congrArg (fun f ↦ PC.iCycles 1 ≫ T.map f) hD
    simp only [T.map_add, T.map_comp, Preadditive.comp_add, ← Category.assoc] at hh
    have hz : PC.iCycles 1 ≫ T.map (P.complex.d 1 0) = 0 := PC.iCycles_d 1 0
    rw [hz, zero_comp] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hnat := P.isoLeftDerivedObj_hom_naturality (𝟙 N) C c
    (ProjectiveResolution.lift_commutes_zero _ _ _) T 1
  simp only [Functor.map_id, Category.id_comp] at hnat
  change (C.isoLeftDerivedObj T 1).hom ≫ hS.δ 1 0 (by simp) ≫
    (ChainComplex.isoHomologyι₀ AC).hom ≫ A.fromLeftDerivedZero' T =
      -((P.isoLeftDerivedObj T 1).hom ≫ torKernelHomologyBoundary M q hq)
  rw [hnat, ← Preadditive.comp_neg]
  simp only [Category.assoc]
  apply congrArg (fun f ↦ (P.isoLeftDerivedObj T 1).hom ≫ f)
  change HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map c) 1 ≫
    hS.δ 1 0 (by simp) ≫ (ChainComplex.isoHomologyι₀ AC).hom ≫
      A.fromLeftDerivedZero' T = -torKernelHomologyBoundary M q hq
  rw [← cancel_epi (PC.homologyπ 1), HomologicalComplex.homologyπ_naturality_assoc]
  have hp : PC.homologyπ 1 ≫ torKernelHomologyBoundary M q hq =
      PC.iCycles 1 ≫ ModuleCat.ofHom ((torKernelDifferential q hq).rTensor M) :=
    (PC.homologyIsCokernel 2 1
      ((ComplexShape.down ℕ).prev_eq' (by simp))).fac _ WalkingParallelPair.one
  rw [Preadditive.comp_neg, hp]
  rw [← hcycle]
  ext z
  let z₀ := (PC.iCycles 1).hom z
  let x₃ := (T.map (c.f 1)).hom z₀
  let x₂ := (T.map l₁).hom z₀
  let x₁ := (T.map t).hom z₀
  have hz : PC.iCycles 1 ≫ T.map (P.complex.d 1 0) = 0 := PC.iCycles_d 1 0
  have hcz : PC.iCycles 1 ≫ T.map (c.f 1) ≫ CC.d 1 0 = 0 := by
    change PC.iCycles 1 ≫ T.map (c.f 1) ≫ T.map (C.complex.d 1 0) = 0
    rw [← T.map_comp, c.comm, T.map_comp, ← Category.assoc,
      hz, zero_comp]
  have hx₃ : (CC.d 1 0).hom x₃ = 0 :=
    congrArg (fun f ↦ f.hom z) hcz
  have hx₂ : (T.map (b.f 1)).hom x₂ = x₃ := by
    change (T.map l₁ ≫ T.map (b.f 1)).hom z₀ = _
    rw [← T.map_comp, hl₁]
  have htz : PC.iCycles 1 ≫ T.map t ≫ T.map (a.f 0) =
      PC.iCycles 1 ≫ T.map l₁ ≫ BC.d 1 0 := by
    rw [← T.map_comp, ht]
    dsimp only [v]
    simp only [T.map_sub, T.map_comp, Preadditive.comp_sub, ← Category.assoc]
    rw [hz, zero_comp, sub_zero]
    rfl
  have hx₁ : (T.map (a.f 0)).hom x₁ = (BC.d 1 0).hom x₂ :=
    congrArg (fun f ↦ f.hom z) htz
  have hd := hS.δ_apply 1 0 (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁ 0 (by simp)
  let cz := HomologicalComplex.cyclesMap ((T.mapHomologicalComplex _).map c) 1
  have hcz' : CC.cyclesMk x₃ 0 (by simp) hx₃ = cz.hom z := by
    apply (ModuleCat.mono_iff_injective (CC.iCycles 1)).mp inferInstance
    have hh := congrArg (fun f ↦ f.hom z)
      (HomologicalComplex.cyclesMap_i ((T.mapHomologicalComplex _).map c) 1)
    have hi : (CC.iCycles 1).hom (CC.cyclesMk x₃ 0 (by simp) hx₃) = x₃ :=
      HomologicalComplex.i_cyclesMk CC x₃ 0 (by simp) hx₃
    change (CC.iCycles 1).hom (CC.cyclesMk x₃ 0 (by simp) hx₃) =
      (CC.iCycles 1).hom (cz.hom z)
    rw [hi]
    exact hh.symm
  change (A.fromLeftDerivedZero' T).hom
    ((ChainComplex.isoHomologyι₀ AC).hom.hom
      ((hS.δ 1 0 (by simp)).hom ((CC.homologyπ 1).hom (cz.hom z)))) = _
  rw [← hcz']
  have hx₀ : (AC.d 0 0).hom x₁ = 0 := by
    rw [AC.shape 0 0 (by simp)]
    rfl
  change (hS.δ 1 0 (by simp)).hom
    ((CC.homologyπ 1).hom (CC.cyclesMk x₃ 0 (by simp) hx₃)) =
      (AC.homologyπ 0).hom (AC.cyclesMk x₁ 0 (by simp) hx₀) at hd
  rw [hd]
  have haug : AC.homologyπ 0 ≫ (ChainComplex.isoHomologyι₀ AC).hom ≫
      A.fromLeftDerivedZero' T = AC.iCycles 0 ≫ T.map εA := by
    change AC.homologyπ 0 ≫ AC.homologyι 0 ≫ A.fromLeftDerivedZero' T = _
    rw [← Category.assoc, HomologicalComplex.homology_π_ι, Category.assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  change (AC.homologyπ 0 ≫ (ChainComplex.isoHomologyι₀ AC).hom ≫
    A.fromLeftDerivedZero' T).hom _ = _
  rw [haug]
  have hi : (AC.iCycles 0).hom (AC.cyclesMk x₁ 0 (by simp) hx₀) = x₁ :=
    HomologicalComplex.i_cyclesMk AC x₁ 0 (by simp) hx₀
  change (T.map εA).hom ((AC.iCycles 0).hom (AC.cyclesMk x₁ 0 (by simp) hx₀)) = _
  rw [hi]
  rfl

end CategoryTheory
