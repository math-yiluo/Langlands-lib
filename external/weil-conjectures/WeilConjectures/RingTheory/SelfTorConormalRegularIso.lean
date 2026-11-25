/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulNormalizedProjectiveResolution
import WeilConjectures.RingTheory.KoszulQuotientTensorHomologyBasis

/-! # The canonical self-Tor comparison for a regular quotient

Source: Stacks Project, Tags 062I, 0BQY and 09PQ.
(blueprint: new-r4-self-tor-conormal-regular-iso). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The normalized comparison is invertible for a Koszul-regular quotient.

Source: Stacks Project, Tags 062I, 0BQY and 09PQ.
(blueprint: new-r4-self-tor-conormal-regular-iso).

Proof: Let f be the r Koszul-regular generators. Their Koszul complex is a finite
free resolution of A/I. Use this resolution to compute Tor. After tensoring with A/I,
every differential coefficient is zero, and nth homology is its nth term, the nth
exterior power of (A/I)^r. The conormal basis theorem identifies I/I² with (A/I)^r,
sending the class of f_j to its standard basis vector. The normalization of the
canonical comparison identifies its value on each increasing wedge of these classes
with precisely the corresponding Koszul homology basis vector. It is consequently an
isomorphism. Equivalently apply the nth exterior power to the conormal basis equivalence
and compose with the zero-differential homology and resolution Tor equivalences; equality
with the canonical map follows by exterior generation and its normalization. For n=0
this sends the empty wedge to 1; for n>r both modules are zero. The same equivalences
cover r=0, A/I=0, and the zero ring. -/
theorem selfTorConormalComparison_isIso (A : Type u) [CommRing A]
    (I : Ideal A) (n r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    IsIso (selfTorConormalComparison A I n) := by
  classical
  obtain ⟨b, hb⟩ := ExteriorAlgebra.exists_koszul_conormal_basis A I r f hreg hf
  obtain ⟨P, a, ha⟩ :=
    ExteriorAlgebra.exists_koszul_normalized_projective_resolution A I r f hreg hf
  obtain ⟨e, he⟩ := exists_koszul_quotient_tensor_homology_basis A I n r f hf b
  let F := tensorRight (ModuleCat.of A (A ⧸ I))
  let T := F.mapHomologicalComplex (.down ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n
  let d := P.isoLeftDerivedObj F n
  let k := (T ⋙ H).mapIso a
  have hgen (s : Set.powersetCard (Fin r) n) :
      d.hom (selfTorConormalComparison A I n (b.exteriorPower n s)) =
        k.hom (e.hom (b.exteriorPower n s)) := by
    obtain ⟨z, hz, hez⟩ := he s
    let g : Fin r → I :=
      fun j ↦ ⟨f j, hf ▸ Ideal.subset_span (Set.mem_range_self j)⟩
    let v : Fin n → (Fin r →₀ A) :=
      fun j ↦ Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1
    have hv : exteriorPower.ιMulti (A ⧸ I) n
        (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))) =
          b.exteriorPower n s := by
      rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
      congr 1
      funext j
      change I.toCotangent (Finsupp.linearCombination A g (v j)) =
        b (Set.powersetCard.ofFinEmbEquiv.symm s j)
      rw [hb]
      simp [v, g, ExteriorAlgebra.koszulConormalVector]
    have hg : (fun j => (g j : A)) = f := by
      funext j
      rfl
    have hspec := selfTorConormalComparison_spec A I n r g P a.hom ha v z hz
    rw [hv] at hspec
    rw [← hez] at hspec
    simpa [d, k, F, T, H, hg] using hspec
  have hcomp : selfTorConormalComparison A I n ≫ d.hom = e.hom ≫ k.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [← (b.exteriorPower n).sum_repr x]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((b.exteriorPower n).repr x s)
    rw [← hc]
    change d.hom (selfTorConormalComparison A I n (c • (b.exteriorPower n s))) =
      k.hom (e.hom (c • (b.exteriorPower n s)))
    simp only [map_smul, hgen]
  have hc : selfTorConormalComparison A I n = (e ≪≫ k ≪≫ d.symm).hom := by
    apply (cancel_mono d.hom).mp
    simpa using hcomp
  rw [hc]
  infer_instance

end AlgebraicGeometry
