/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Kaehler.JacobiZariski
import WeilConjectures.RingTheory.ConormalIntersectionRegularQuotient
import WeilConjectures.RingTheory.ComposedConormalInjectiveOfIntersection

/-!
# Left injectivity in Jacobi–Zariski for a regular-sequence presentation

Source: Stacks Project, More on Algebra, Tag 07D4, the “in particular” clause,
using Tags 062F and 07CX, and Algebra, Tags 00S1 and 00S2
(blueprint: lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective).
-/

@[expose] public section

universe u v w

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_of_surjective_regular
    {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (hq : Function.Surjective q) (J : Ideal R)
    (hIJ : RingHom.ker q ≤ J) (fs : List S)
    (hreg : RingTheory.Sequence.IsRegular S fs) (hgen : Ideal.ofList fs = J.map q) :
    RingHom.ker q ⊓ J ^ 2 = RingHom.ker q * J := by
  classical
  let lift : S → R := fun s ↦ (hq s).choose
  have hlift (s : S) : q (lift s) = s := (hq s).choose_spec
  let e := q.quotientKerEquivOfSurjective hq
  have hm : Ideal.Quotient.mk (RingHom.ker q) = e.symm.toRingHom.comp q :=
    (RingHom.quotientKerEquivOfSurjective_symm_comp hq).symm
  apply Ideal.inf_sq_eq_mul_of_regular_quotient _ J hIJ
  refine ⟨fs.map lift, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
    have hs' : s ∈ J.map q := hgen ▸ Ideal.subset_span hs
    rw [Ideal.mem_map_iff_of_surjective q hq] at hs'
    obtain ⟨r, hr, he⟩ := hs'
    have hd : lift s - r ∈ RingHom.ker q := by
      simp only [RingHom.mem_ker, map_sub, hlift, he, sub_self]
    simpa using J.add_mem (hIJ hd) hr
  · have he : (fs.map lift).map (Ideal.Quotient.mk (RingHom.ker q)) =
        fs.map e.symm := by
      simp only [List.map_map]
      congr 1
      funext s
      rw [hm]
      exact congrArg e.symm (hlift s)
    rw [he]
    apply (AddEquiv.isRegular_congr (e := e.symm.toAddEquiv) ?_).mp hreg
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro s _ x
    exact e.symm.map_mul s x
  · rw [hm, ← Ideal.map_map, ← hgen, Ideal.map_ofList]
    congr 1
    simp only [List.map_map]
    congr 1
    funext s
    exact congrArg e.symm (hlift s)

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 07D4, with a regular-sequence presentation (Tag 062F).
(blueprint: lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective)
The canonical conormal map carries the kernel of the base-changed differential into
`H1Cotangent A C`; its restriction is injective. Tensor factors are reversed by symmetry.

Proof:
1. Take `P = Generators.self A B` and `Q = Generators.ofAlgHom β hβ`.
The composed presentation `T = Q.comp P` maps surjectively to `Q.Ring` by its
coefficient map `q`. Its kernel is the extension of `P.ker` and is contained in `T.ker`.
The image of `T.ker` under `q` is `Q.ker = Ideal.ofList fs`.
2. Lift the given sequence through `q`. The quotient isomorphism `T.Ring/ker q ≃ Q.Ring`
transports regularity of `fs` to regularity of the lifted sequence modulo `ker q`.
Apply lem-weil-pbc-conormal-intersection-regular-quotient to obtain
`ker q ∩ T.ker² = ker q * T.ker`. The proved private helper
`intersection_of_surjective_regular` performs this transport.
3. Apply lem-weil-pbc-composed-conormal-injective-of-intersection. This identifies
`C ⊗[B] P.Cotangent` with the coefficient ideal modulo its product with `T.ker`,
and injects it into `T.Cotangent`. The commutative differential square restricts
this injection to `r : ker (P.cotangentComplex.baseChange C) → T.H1Cotangent`.
4. Mathlib's presentation equivalence compares `T.H1Cotangent` with `H1Cotangent A C`.
Compose it with `r`. The composite presentation homomorphism and the canonical
homomorphism need not agree on the whole conormal module; `Cotangent.map_sub_map`
expresses their difference through the differential. After base change their difference
vanishes on its kernel, proving the required ambient formula. Injectivity follows from
the presentation equivalence, the conormal injection, and `Subtype.ext`.
Presentation functoriality and the polynomial differential square are Mathlib's
interfaces for lem-weil-pbc-nl-presentation-h1-functoriality and
lem-weil-pbc-polynomial-ring-kahler-basis-any-variables. -/
theorem jacobiZariski_left_injective_of_regularSequence
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (m : ℕ) (fs : List (MvPolynomial (Fin m) B))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) B) fs)
    (β : MvPolynomial (Fin m) B →ₐ[B] C)
    (hβ : Function.Surjective β) (hker : RingHom.ker β.toRingHom = Ideal.ofList fs) :
    let P := (Generators.self A B).toExtension
    let Q := (Generators.self A C).toExtension
    let F := (Generators.defaultHom (Generators.self A B) (Generators.self A C)).toExtensionHom
    let d := P.cotangentComplex.baseChange C
    let g := (Extension.Cotangent.map F).liftBaseChange C
    ∃ u : LinearMap.ker d →ₗ[C] H1Cotangent A C,
      (∀ x : LinearMap.ker d, Q.h1Cotangentι (u x) = g x.1) ∧ Function.Injective u := by
  classical
  dsimp only
  let P := Generators.self A B
  let E := Generators.self A C
  let Q := Generators.ofAlgHom β hβ
  let T := Q.comp P
  let f := (Generators.defaultHom P E).toExtensionHom
  let i := (Q.toComp P).toExtensionHom
  let j := (Generators.defaultHom T E).toExtensionHom
  let q := (Q.ofComp P).toAlgHom.toRingHom
  have hQ : Q.ker = Ideal.ofList fs := by
    rw [Generators.ker_eq_ker_aeval_val]
    have he : MvPolynomial.aeval Q.val = β := by
      ext x
      simp [Q, Generators.ofAlgHom, Generators.ofSurjective]
    rw [he]
    exact hker
  have hIJ : RingHom.ker q ≤ T.ker := by
    intro x hx
    change algebraMap T.toExtension.Ring C x = 0
    have H := (Q.ofComp P).toExtensionHom.algebraMap_toRingHom x
    have hx' : q x = 0 := hx
    rw [show (Q.ofComp P).toExtensionHom.toRingHom x = 0 from hx', map_zero] at H
    simpa only [algebraMap_self, RingHom.id_apply] using H.symm
  have hgen : Ideal.ofList fs = T.ker.map q := by
    rw [← hQ]
    exact (Generators.map_ofComp_ker Q P).symm
  have hinter := intersection_of_surjective_regular q
    (Generators.toAlgHom_ofComp_surjective Q P) T.ker hIJ fs hreg hgen
  have hinj := Generators.Cotangent.toComp_injective_of_intersection Q P hinter
  have comm := Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P
  let r : (P.toExtension.cotangentComplex.baseChange C).ker →ₗ[C]
      T.toExtension.H1Cotangent :=
    ((Extension.Cotangent.map i).liftBaseChange C).restrict
      (p := (P.toExtension.cotangentComplex.baseChange C).ker)
      (q := T.toExtension.cotangentComplex.ker) (fun x hx ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hx, map_zero])
  let e := Generators.H1Cotangent.equiv T E
  refine ⟨e.toLinearMap ∘ₗ r, ?_, ?_⟩
  · intro x
    change Extension.Cotangent.map j
      ((Extension.Cotangent.map i).liftBaseChange C x.val) =
        (Extension.Cotangent.map f).liftBaseChange C x.val
    rw [← LinearMap.comp_apply, LinearMap.liftBaseChange_comp,
      ← Extension.Cotangent.map_comp]
    have H : (Extension.Cotangent.map (j.comp i)).liftBaseChange C -
        (Extension.Cotangent.map f).liftBaseChange C =
        ((j.comp i).sub f).liftBaseChange C ∘ₗ P.toExtension.cotangentComplex.baseChange C := by
      ext y
      simpa using congrArg Extension.Cotangent.val
        (DFunLike.congr_fun (Extension.Cotangent.map_sub_map (j.comp i) f) y)
    have Hx := DFunLike.congr_fun H x.val
    rw [LinearMap.sub_apply, LinearMap.comp_apply, x.property, map_zero] at Hx
    exact sub_eq_zero.mp Hx
  · intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val (e.injective hxy)

end Algebra
