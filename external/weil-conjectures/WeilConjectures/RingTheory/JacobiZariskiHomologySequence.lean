/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
import WeilConjectures.RingTheory.TwoTermKernelBaseChange

/-!
# The full Jacobi–Zariski homology sequence

Source: Stacks Project, Algebra, Tag 00S2, `lemma-exact-sequence-NL`
(blueprint: lem-weil-pbc-jacobi-zariski-homology-sequence).
-/

@[expose] public section

universe u v w

open TensorProduct KaehlerDifferential CategoryTheory CategoryTheory.Limits

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
-- Transporting five module universes involves several tensor and quotient equivalences.
private theorem lifted_kernel.{b, c, n₁, n₀, h}
    (B : Type b) (C : Type c) (N₁ : Type n₁) (N₀ : Type n₀) (H₀ : Type h)
    [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₀] [Module B N₀]
    [AddCommGroup H₀] [Module B H₀] [Module.Free B N₀]
    (d : N₁ →ₗ[B] N₀) (p : N₀ →ₗ[B] H₀)
    (hp : Function.Surjective p) (hdp : Function.Exact d p)
    (h₁ : IsZero (((Tor' (ModuleCat (ULift.{max b c n₁ n₀ h} B)) 1).obj
      (ModuleCat.of (ULift.{max b c n₁ n₀ h} B) (ULift.{max b c n₁ n₀ h} H₀))).obj
      (ModuleCat.of (ULift.{max b c n₁ n₀ h} B) (ULift.{max b c n₁ n₀ h} C))))
    (h₂ : IsZero (((Tor' (ModuleCat (ULift.{max b c n₁ n₀ h} B)) 2).obj
      (ModuleCat.of (ULift.{max b c n₁ n₀ h} B) (ULift.{max b c n₁ n₀ h} H₀))).obj
      (ModuleCat.of (ULift.{max b c n₁ n₀ h} B) (ULift.{max b c n₁ n₀ h} C)))) :
    Function.Bijective (d.tensorKer C C) := by
  let B' := ULift.{max b c n₁ n₀ h} B
  let C' := ULift.{max b c n₁ n₀ h} C
  let N₁' := ULift.{max b c n₁ n₀ h} N₁
  let N₀' := ULift.{max b c n₁ n₀ h} N₀
  let H₀' := ULift.{max b c n₁ n₀ h} H₀
  let : Algebra B' B := ULift.algebra' B B
  let : Algebra B' C := ULift.algebra' B C
  let d' : N₁' →ₗ[B'] N₀' :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ d.restrictScalars B' ∘ₗ
      ULift.moduleEquiv.toLinearMap
  let p' : N₀' →ₗ[B'] H₀' :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ p.restrictScalars B' ∘ₗ
      ULift.moduleEquiv.toLinearMap
  have hp' : Function.Surjective p' := by
    intro x
    obtain ⟨y, hy⟩ := hp x.down
    exact ⟨⟨y⟩, congrArg ULift.up hy⟩
  have hdp' : Function.Exact d' p' := by
    intro x
    change ULift.up (p x.down) = 0 ↔ ∃ y : N₁', ULift.up (d y.down) = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (hdp x.down).mp (congrArg ULift.down hx)
      exact ⟨⟨y⟩, congrArg ULift.up hy⟩
    · rintro ⟨y, hy⟩
      apply ULift.ext
      exact (hdp x.down).mpr ⟨y.down, congrArg ULift.down hy⟩
  let : Module.Free B' N₀ :=
    Module.Free.of_basis ((Module.Free.chooseBasis B N₀).mapCoeffs
      ULift.ringEquiv.symm (fun _ _ ↦ rfl))
  let : Module.Free B' N₀' := inferInstance
  let e₀ : (N₀' ⧸ d'.range) ≃ₗ[B'] H₀' :=
    (Submodule.quotEquivOfEq _ _ hdp'.linearMap_ker_eq.symm).trans
      (p'.quotKerEquivOfSurjective hp')
  let i₀ : ModuleCat.of B' (N₀' ⧸ d'.range) ≅ ModuleCat.of B' H₀' :=
    e₀.toModuleIso
  have ht₁ : IsZero (((Tor' (ModuleCat B') 1).obj
      (ModuleCat.of B' (N₀' ⧸ d'.range))).obj (ModuleCat.of B' C')) :=
    h₁.of_iso (((Tor' (ModuleCat B') 1).mapIso i₀).app (ModuleCat.of B' C'))
  have ht₂ : IsZero (((Tor' (ModuleCat B') 2).obj
      (ModuleCat.of B' (N₀' ⧸ d'.range))).obj (ModuleCat.of B' C')) :=
    h₂.of_iso (((Tor' (ModuleCat B') 2).mapIso i₀).app (ModuleCat.of B' C'))
  have ht := LinearMap.bijective_twoTermKernelBaseChange_algebra
    B' C' N₁' N₀' d' ht₁ ht₂
  let k : ULift.{max b c n₁ n₀ h} d.ker ≃ₗ[B'] d'.ker :=
    { toFun := fun x ↦ ⟨⟨x.down.val⟩, congrArg ULift.up x.down.property⟩
      invFun := fun x ↦ ⟨⟨x.val.down, congrArg ULift.down x.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let e₁ : C ⊗[B] N₁ ≃ₗ[B] C' ⊗[B'] N₁' :=
    (ULift.moduleEquiv : ULift.{0} (C ⊗[B] N₁) ≃ₗ[B] _).symm.trans
      (AlgebraTensorModule.uliftEquiv B B C N₁)
  let e₂ : C ⊗[B] N₀ ≃ₗ[B] C' ⊗[B'] N₀' :=
    (ULift.moduleEquiv : ULift.{0} (C ⊗[B] N₀) ≃ₗ[B] _).symm.trans
      (AlgebraTensorModule.uliftEquiv B B C N₀)
  let eK : C ⊗[B] d.ker ≃ₗ[B] C' ⊗[B'] d'.ker :=
    ((ULift.moduleEquiv : ULift.{0} (C ⊗[B] d.ker) ≃ₗ[B] _).symm.trans
      (AlgebraTensorModule.uliftEquiv B B C d.ker)).trans
      ((_root_.TensorProduct.congr (LinearEquiv.refl B' C') k).restrictScalars B)
  have hd (x : C ⊗[B] N₁) :
      d'.baseChange C' (e₁ x) = e₂ (d.baseChange C x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c n => rfl
    | add x y hx hy => simp [hx, hy]
  let eT : (d.baseChange C).ker ≃ₗ[B] (d'.baseChange C').ker :=
    { toFun := fun x ↦ ⟨e₁ x.val, by
        rw [LinearMap.mem_ker, hd, x.property, map_zero]⟩
      invFun := fun x ↦ ⟨e₁.symm x.val, by
        apply e₂.injective
        rw [map_zero, ← hd, e₁.apply_symm_apply]
        exact x.property⟩
      left_inv := fun x ↦ Subtype.ext (e₁.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e₁.apply_symm_apply x.val)
      map_add' := fun _ _ ↦ Subtype.ext (map_add e₁ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul e₁ _ _) }
  have hc (x : C ⊗[B] d.ker) : eT (d.tensorKer C C x) = d'.tensorKer C' C' (eK x) := by
    apply Subtype.ext
    change e₁ _ = _
    induction x using TensorProduct.inductionOn with
    | tmul c n => rfl
    | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  constructor
  · intro x y hxy
    apply eK.injective
    apply ht.injective
    rw [← hc, ← hc, hxy]
  · intro y
    obtain ⟨x, hx⟩ := ht.surjective (eT y)
    refine ⟨eK.symm x, eT.injective ?_⟩
    rw [hc, eK.apply_symm_apply, hx]

set_option backward.isDefEq.respectTransparency false in
private theorem liftBaseChange_eq_on_cotangent_kernel
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {P : Extension A B} {W : Extension A C}
    (a b : P.Hom W) (x : (P.cotangentComplex.baseChange C).ker) :
    (Extension.Cotangent.map a).liftBaseChange C x.val =
      (Extension.Cotangent.map b).liftBaseChange C x.val := by
  have H : (Extension.Cotangent.map a).liftBaseChange C -
      (Extension.Cotangent.map b).liftBaseChange C =
      (a.sub b).liftBaseChange C ∘ₗ P.cotangentComplex.baseChange C := by
    ext y
    simpa using congrArg Extension.Cotangent.val
      (DFunLike.congr_fun (Extension.Cotangent.map_sub_map a b) y)
  have Hx := DFunLike.congr_fun H x.val
  rw [LinearMap.sub_apply, LinearMap.comp_apply, x.property, map_zero] at Hx
  exact sub_eq_zero.mp Hx

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Algebra, Tag 00S2, `lemma-exact-sequence-NL`
(blueprint: lem-weil-pbc-jacobi-zariski-homology-sequence).

The presentations are the canonical polynomial presentations. Tensor products are written
with `C` on the left, using the symmetry over `B`. The equations for `u` and `t` specify their
ambient conormal maps and hence their well-defined restrictions to the kernels. The maps
`v`, `w`, `z`, and the snake connecting map are Mathlib's canonical maps. The coefficient
formula specifies the connecting map on every polynomial representative. ULift only puts
both Tor arguments in a common module universe.

Proof (the node's ten steps). (1) Use the polynomial differential basis to identify the
canonical cotangent complexes with the presentation complexes. (2) Include A[B] into
A[B,C] and map A[B,C] to B[C]; these commute with the differentials and have zero composite
on conormals. (3) The row of free differential modules is split exact by its B- and C-bases.
(4) The conormal row is right exact: the coefficient map has kernel I A[B,C], whose image
modulo K squared is exactly the image of C tensor I/I squared.
(5) Apply the module snake lemma to obtain the six-term kernel/cokernel sequence.
(6) Identify its cokernels with Kahler differentials by the conormal exact sequence and
right exactness of tensor product. (7) Compare A[B,C] with A[C] in both directions;
presentation independence of H1 identifies their kernels and the specified maps u and v.
(8) Transport snake exactness across this isomorphism. (9) Apply the two-term complex
kernel base-change lemma: the degree-zero term is free, and Tor in degrees one and two
vanishes, so the natural kernel tensor map is bijective. (10) Lift each coefficient b of
a polynomial in B[C] to the variable [b] in A[B,C]. Its differential in the B-directions
is the coefficient-derivative sum displayed below, and its C-directions vanish because
the representative is a cycle. This computes the snake connecting map.
Dependency nodes by step: (1), (3), (10)
`lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`; (1), (2), (7)
`lem-weil-pbc-nl-presentation-h1-functoriality`; (4)
`lem-weil-pbc-polynomial-coefficient-map-kernel`; (5), (10)
`lem-weil-pbc-snake-lemma-modules`; (6), (9)
`lem-weil-pbc-jacobi-zariski-differential-maps`; (6)
`lem-weil-pbc-tensor-right-exact`; (9)
`lem-weil-pbc-two-term-complex-kernel-base-change` and `def-weil-pbc-tor-modules`.
Step (8) is elementary transport of images and kernels through an isomorphism. -/
theorem jacobiZariski_homology_sequence
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    let P := (Generators.self A B).toExtension
    let Q := (Generators.self B C).toExtension
    let E := (Generators.self A C).toExtension
    let K := (P.cotangentComplex.baseChange C).ker
    let f := Extension.Cotangent.map
      (Generators.defaultHom (Generators.self A B) (Generators.self A C)).toExtensionHom
    let v := H1Cotangent.map A B C C
    let w := KaehlerDifferential.mapBaseChange A B C
    let z := KaehlerDifferential.map A B C C
    let δ := H1Cotangent.δ A B C
    ∃ (u : K →ₗ[C] H1Cotangent A C)
      (t : C ⊗[B] H1Cotangent A B →ₗ[C] K),
      (∀ x : K, E.h1Cotangentι (u x) = f.liftBaseChange C x.val) ∧
      (∀ (c : C) (h : H1Cotangent A B),
        (t (c ⊗ₜ[B] h)).val = c ⊗ₜ[B] P.h1Cotangentι h) ∧
      (∀ (g : Q.ker) (h : H1Cotangent B C),
        Q.h1Cotangentι h = Extension.Cotangent.mk g →
        δ h = ∑ α ∈ g.val.support,
          (α.prod (fun c n ↦ c ^ n)) ⊗ₜ[B] D A B (AddMonoidAlgebra.coeff g.val α)) ∧
      Function.Exact u v ∧ Function.Exact v δ ∧ Function.Exact δ w ∧
      Function.Exact w z ∧ Function.Surjective z ∧
      ((IsZero (((Tor' (ModuleCat (ULift.{max u v w} B)) 1).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} Ω[B⁄A]))).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} C))) ∧
        IsZero (((Tor' (ModuleCat (ULift.{max u v w} B)) 2).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} Ω[B⁄A]))).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} C)))) → Function.Bijective t) := by
  classical
  dsimp only
  let P := Generators.self A B
  let Q := Generators.self B C
  let E := Generators.self A C
  let f := (Generators.defaultHom P E).toExtensionHom
  let K := (P.toExtension.cotangentComplex.baseChange C).ker
  have comm :
      (Extension.CotangentSpace.map f).liftBaseChange C ∘ₗ
        P.toExtension.cotangentComplex.baseChange C =
      E.toExtension.cotangentComplex ∘ₗ (Extension.Cotangent.map f).liftBaseChange C := by
    ext c
    simp [Extension.CotangentSpace.map_cotangentComplex]
  let u : K →ₗ[C] H1Cotangent A C :=
    ((Extension.Cotangent.map f).liftBaseChange C).restrict
      (p := K) (q := E.toExtension.cotangentComplex.ker) (fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hx, map_zero])
  let t : C ⊗[B] H1Cotangent A B →ₗ[C] K :=
    P.toExtension.cotangentComplex.tensorKer C C
  refine ⟨u, t, ?_, ?_, ?_, ?_, H1Cotangent.exact_map_δ A B C,
    H1Cotangent.exact_δ_mapBaseChange A B C,
    KaehlerDifferential.exact_mapBaseChange_map A B C,
    KaehlerDifferential.map_surjective A B C, ?_⟩
  · intro x
    rfl
  · intro c h
    exact LinearMap.tensorKer_tmul C C P.toExtension.cotangentComplex c h
  · intro g h hh
    have he : h = ⟨Extension.Cotangent.mk g, by
        rw [← hh]; exact h.property⟩ := Subtype.ext hh
    rw [he]
    change Generators.H1Cotangent.δ Q P _ = _
    rw [Generators.H1Cotangent.δ_eq_δAux]
    change Generators.H1Cotangent.δAux A Q g.val = _
    conv_lhs => rw [MvPolynomial.as_sum g.val, map_sum]
    simp only [Generators.H1Cotangent.δAux_monomial]
    rfl
  · let F := Q.comp P
    let e := Generators.H1Cotangent.equiv E F
    let i := (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C
    let j := Extension.Cotangent.map (Q.ofComp P).toExtensionHom
    have ve (y : H1Cotangent A C) :
        H1Cotangent.map A B C C y =
        Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom (e y) := by
      change Extension.H1Cotangent.map (Generators.defaultHom E Q).toExtensionHom y = _
      change _ = Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom
        (Extension.H1Cotangent.map (Generators.defaultHom E F).toExtensionHom y)
      rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]
    intro y
    constructor
    · intro hy
      have hj : j (e y).val = 0 := by
        have h := ve y
        rw [hy] at h
        exact (congrArg Subtype.val h).symm
      obtain ⟨x, hx⟩ := (Generators.Cotangent.exact Q P (e y).val).mp hj
      have hk : P.toExtension.cotangentComplex.baseChange C x = 0 := by
        apply Generators.CotangentSpace.map_toComp_injective Q P
        rw [map_zero]
        have H := DFunLike.congr_fun
          (Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P) x
        simp only [LinearMap.comp_apply, hx] at H
        exact H.trans (e y).property
      refine ⟨⟨x, hk⟩, ?_⟩
      apply Subtype.ext
      change (Extension.Cotangent.map f).liftBaseChange C x = y.val
      rw [liftBaseChange_eq_on_cotangent_kernel f ((Generators.defaultHom F E).toExtensionHom.comp
        (Q.toComp P).toExtensionHom) ⟨x, hk⟩]
      rw [Extension.Cotangent.map_comp, ← LinearMap.liftBaseChange_comp,
        LinearMap.comp_apply, hx]
      exact congrArg Subtype.val (e.symm_apply_apply y)
    · rintro ⟨x, rfl⟩
      rw [ve]
      apply Subtype.ext
      change j (Extension.Cotangent.map (Generators.defaultHom E F).toExtensionHom
        ((Extension.Cotangent.map f).liftBaseChange C x.val)) = 0
      have H : Extension.Cotangent.map (Generators.defaultHom E F).toExtensionHom
          ((Extension.Cotangent.map f).liftBaseChange C x.val) = i x.val := by
        change (Extension.Cotangent.map (Generators.defaultHom E F).toExtensionHom ∘ₗ
          (Extension.Cotangent.map f).liftBaseChange C) x.val = _
        rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp]
        exact liftBaseChange_eq_on_cotangent_kernel _ (Q.toComp P).toExtensionHom x
      rw [H]
      exact (Generators.Cotangent.exact Q P).apply_apply_eq_zero x.val
  · intro hTor
    exact lifted_kernel B C P.toExtension.Cotangent P.toExtension.CotangentSpace Ω[B⁄A]
      P.toExtension.cotangentComplex P.toExtension.toKaehler
      P.toExtension.toKaehler_surjective P.toExtension.exact_cotangentComplex_toKaehler
      hTor.1 hTor.2

end Algebra
