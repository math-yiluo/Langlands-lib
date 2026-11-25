/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Uniqueness of the normalized self-Tor comparison. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Every tuple of ideal elements supplies a normalized resolution lift and a cycle
representing the standard top wedge after reduction modulo the ideal.
Source: Stacks Project, Tag 00LS (lifting free complexes to resolutions) and
Tag 0623 (Koszul differentials).
(blueprint: new-r4-self-tor-conormal-comparison-unique).

Proof: The terms of the Koszul complex are exterior powers of a finite free module,
hence projective. Lift the quotient augmentation in degree zero through the
surjective resolution augmentation. Its composite with the first Koszul
boundary is zero, since each tuple entry belongs to I. Exactness and projectivity
lift degree one through the first resolution differential. Inductively, the
square-zero identity and the previous commutative square put the next composite
in the kernel of the resolution differential; exactness and projectivity lift
it through the next differential. These components define the required chain map.
After tensoring with A/I, the contraction formula for a wedge has coefficients
in I, so every differential vanishes. The standard top wedge tensored with one
therefore lies in the kernel, and the cycles inclusion identifies cycles with
that kernel, giving z. For n=0 the outgoing differential is zero by the complex
shape and the empty wedge gives the unit. If I=A the tensor is zero; if I=0 all
tuple entries and all Koszul differentials are zero. No regularity is required. -/
private theorem exists_koszul_conormal_test_data (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (g : Fin n → I)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))) :
    ∃ a : ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A)) ⟶ P.complex,
      a.f 0 ≫ P.π.f 0 =
        ModuleCat.ofHom (I.mkQ.comp
          (exteriorPower.zeroEquiv A (Fin n →₀ A)).toLinearMap) ∧
      ∃ z : (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
          (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A)))).cycles n,
        (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)).obj
          (ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A)))).iCycles n z =
          (exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[A]
            (1 : A ⧸ I) := by
  classical
  let K := ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A))
  have hproj (k : ℕ) : Projective (K.X k) :=
    ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne : Module.Basis (Fin n) A (Fin n →₀ A)).exteriorPower k)
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) :=
    ModuleCat.ofHom (I.mkQ.comp
      (exteriorPower.zeroEquiv A (Fin n →₀ A)).toLinearMap)
  have hmem (v : Fin n →₀ A) :
      Finsupp.linearCombination A (fun j ↦ (g j : A)) v ∈ I := by
    have he : Finsupp.linearCombination A (fun j ↦ (g j : A)) =
        I.subtype.comp (Finsupp.linearCombination A g) := by
      ext j
      simp
    rw [he]
    exact (Finsupp.linearCombination A g v).property
  have hq : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    ext v
    change I.mkQ (exteriorPower.zeroEquiv A (Fin n →₀ A)
      (ExteriorAlgebra.koszulBoundary A n (fun j ↦ (g j : A)) 0
        (exteriorPower.ιMulti A 1 v))) = 0
    rw [ExteriorAlgebra.boundary_wedge]
    rw [Fin.sum_univ_succ]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero,
      zero_add, neg_one_sq, one_mul]
    rw [map_smul]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    exact I.mul_mem_right _ (hmem (v 0))
  let a₀ : K.X 0 ⟶ P.complex.X 0 := Projective.factorThru q (P.π.f 0)
  have ha₀ : a₀ ≫ P.π.f 0 = q := Projective.factorThru_comp _ _
  have h₁ : (K.d 1 0 ≫ a₀) ≫ P.π.f 0 = 0 := by
    rw [Category.assoc, ha₀, hq]
  let a₁ : K.X 1 ⟶ P.complex.X 1 := P.exact₀.liftFromProjective _ h₁
  have ha₁ : a₁ ≫ P.complex.d 1 0 = K.d 1 0 ≫ a₀ :=
    P.exact₀.liftFromProjective_comp _ _
  let a : K ⟶ P.complex := ChainComplex.mkHom K P.complex a₀ a₁ ha₁ (by
    intro k t
    refine ⟨(P.exact_succ k).liftFromProjective (K.d (k + 2) (k + 1) ≫ t.2.1)
      (by rw [Category.assoc, t.2.2, ← Category.assoc, K.d_comp_d, zero_comp]),
      (P.exact_succ k).liftFromProjective_comp _ _⟩)
  refine ⟨a, ha₀, ?_⟩
  let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let L := T.obj K
  have hd (i j : ℕ) : L.d i j = 0 := by
    by_cases hij : i = j + 1
    · subst i
      change ((tensorRight (ModuleCat.of A (A ⧸ I))).map (K.d (j + 1) j)) = 0
      simp only [K, ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change ExteriorAlgebra.koszulBoundary A n (fun j ↦ (g j : A)) j x ⊗ₜ[A] y = 0
      have hx : x ∈ Submodule.span A
          (Set.range (exteriorPower.ιMulti A (j + 1) (M := Fin n →₀ A))) := by
        rw [exteriorPower.ιMulti_span]
        exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [ExteriorAlgebra.boundary_wedge, TensorProduct.sum_tmul]
        apply Finset.sum_eq_zero
        intro k hk
        rw [TensorProduct.smul_tmul]
        have hz : (((-1 : A) ^ (k.val + 2) *
            Finsupp.linearCombination A (fun j ↦ (g j : A)) (v k)) • y : A ⧸ I) = 0 := by
          change Ideal.Quotient.mk I _ * y = 0
          rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hmem (v k)), mul_zero, zero_mul]
        rw [hz, TensorProduct.tmul_zero]
      | zero => simp
      | add x x' hx hx' h h' => simp only [map_add, TensorProduct.add_tmul, h, h', add_zero]
      | smul b x hx h => rw [map_smul, ← TensorProduct.smul_tmul', h, smul_zero]
    · have hK : K.d i j = 0 := K.shape i j (by simpa [eq_comm] using hij)
      change (tensorRight (ModuleCat.of A (A ⧸ I))).map (K.d i j) = 0
      rw [hK, Functor.map_zero]
  let e := L.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl (hd _ _)
  refine ⟨e.inv ((exteriorPower.ιMulti A n (fun j ↦ Finsupp.single j 1)) ⊗ₜ[A]
      (1 : A ⧸ I)), ?_⟩
  exact congrArg (fun f ↦ f ((exteriorPower.ιMulti A n
    (fun j ↦ Finsupp.single j 1)) ⊗ₜ[A] (1 : A ⧸ I))) e.inv_hom_id

/-- The Koszul normalization determines a comparison uniquely.
Source: Stacks Project, Tag 00LS (comparison of free complexes with resolutions),
with the normalization of Tag 09PQ used in the parent theorem.
(blueprint: new-r4-self-tor-conormal-comparison-unique).

Proof: Lift the n entries of any pure conormal wedge to ideal elements g,
using the surjection I -> I/I². Use the Koszul complex on that tuple and its
standard basis vectors. Its terms are free. The quotient augmentation kills
its first differential, so lift it inductively to any projective resolution
of A/I: lift degree zero against the surjective augmentation, degree one
against its kernel, and successive degrees against the exact differentials.
After tensoring with A/I all Koszul differentials vanish, since every g lies
in I. Thus the standard top wedge tensored with one has a cycle preimage z.
The two normalization hypotheses identify c and d on the conormal wedge
with the same homology class, after the same resolution isomorphism; cancel
that isomorphism. Pure wedges span over A/I. Since A -> A/I is surjective,
A-linearity also propagates equality to every A/I-multiple of a pure wedge,
and then to their sums. This proves equality of the morphisms. For n=0
use the empty tuple: the empty wedge is the unit and generates A/I. For
I=A the source is zero; for I=0 its positive exterior degrees are zero.
No regularity hypothesis is used. -/
theorem selfTorConormalComparison_unique (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ)
    (c d : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)))
    (hc : IsSelfTorConormalComparison A I n c)
    (hd : IsSelfTorConormalComparison A I n d) : c = d := by
  classical
  let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
  let e := P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n
  have hw (v : Fin n → I.Cotangent) :
      c (exteriorPower.ιMulti (A ⧸ I) n v) =
        d (exteriorPower.ιMulti (A ⧸ I) n v) := by
    choose g hg using fun j ↦ I.toCotangent_surjective (v j)
    obtain ⟨a, ha, z, hz⟩ := exists_koszul_conormal_test_data A I n g P
    have hv : (fun j ↦ I.toCotangent
        (Finsupp.linearCombination A g (Finsupp.single j 1))) = v := by
      funext j
      simpa using hg j
    have hc' := hc n g P a ha (fun j ↦ Finsupp.single j 1) z hz
    have hd' := hd n g P a ha (fun j ↦ Finsupp.single j 1) z hz
    rw [hv] at hc' hd'
    exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance (hc'.trans hd'.symm)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span (A ⧸ I)
      (Set.range (exteriorPower.ιMulti (A ⧸ I) n (M := I.Cotangent))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact hw v
  | zero => simp
  | add x y hx hy hcx hcy => simp only [map_add, hcx, hcy]
  | smul b x hx hcx =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change c (a • x) = d (a • x)
    simp only [map_smul, hcx]

end AlgebraicGeometry

