/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Smooth.Flat

@[expose] public section

set_option autoImplicit false
universe u v z

open scoped TensorProduct

namespace Algebra

/-- Flatness of the map in the finite étale Artinian lifting construction.
Source: Stacks Project, proof of Tag 07FI, flatness of the last map; the proof below
uses étale base change, étale cancellation and smooth flatness instead of Tag 00MP.
(blueprint: lem-weil-pbc-artinian-separable-residue-lift-flat).

Proof: Regard g' as a D-algebra map using the factorization equality. It induces the
S-algebra section sigma : S ⊗[D] D' → S, sending s ⊗ d to s g'(d). The inclusion
D' → S ⊗[D] D' is flat by base change of the flat map D → S (and tensor commutativity).
The tensor algebra is étale over S by base change of D → D'. Since the identity
S → S is étale and factors through sigma, étale cancellation makes sigma étale.
Étale maps are smooth and hence flat. The composite of the inclusion with sigma is
g', so composition of flat maps proves the conclusion. This also proves the claim
without the Artinian, local or module-finiteness hypotheses. -/
theorem flat_of_finiteEtale_artinian_residue_lift_core
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat)
    (D' : Type (max u v z)) [CommRing D'] [Algebra D D']
    (g' : D' →+* S) [IsLocalRing D'] [IsArtinianRing D']
    [IsLocalHom (algebraMap D D')] [IsLocalHom g']
    [Etale D D'] [Module.Finite D D']
    (hcomp : g'.comp (algebraMap D D') = algebraMap D S) : g'.Flat := by
  let g : D' →ₐ[D] S := ⟨g', fun r => congrArg (fun f : D →+* S => f r) hcomp⟩
  let σ : S ⊗[D] D' →ₐ[S] S :=
    TensorProduct.lift (AlgHom.id S S) g (fun _ _ => Commute.all _ _)
  have : Module.Flat D S := RingHom.flat_algebraMap_iff.mp hflat
  have hright : (TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom.Flat := by
    have hleft : (algebraMap D' (D' ⊗[D] S)).Flat :=
      RingHom.flat_algebraMap_iff.mpr inferInstance
    have heq : (TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom =
        (TensorProduct.comm D D' S).toRingHom.comp (algebraMap D' (D' ⊗[D] S)) := by
      ext x
      simp
    rw [heq]
    exact hleft.comp (.of_bijective (TensorProduct.comm D D' S).bijective)
  have hσ : σ.toRingHom.Flat := by
    let := σ.toRingHom.toAlgebra
    have : IsScalarTower S (S ⊗[D] D') S :=
      IsScalarTower.of_algebraMap_eq (fun x => (σ.commutes x).symm)
    have : Etale (S ⊗[D] D') S := Etale.of_restrictScalars S _ _
    exact Smooth.flat (S ⊗[D] D') S
  have heq : σ.toRingHom.comp
      (TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom = g' := by
    ext x
    simp [σ, g]
  rw [← heq]
  exact hright.comp hσ

end Algebra
