/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalCyclePresentation
import WeilConjectures.RingTheory.KoszulIdealAlternatingProducts
import WeilConjectures.RingTheory.KoszulAugmentationLiftHomotopy

/-! # Conormal relations vanish in Koszul-to-resolution homology

Source: Stacks Project, Tags 09PQ and 00LS.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Evaluate formal wedge-cycle generators in the homology of one resolution,
using a specified family of chain maps. This is an actual finite linear combination. 
(blueprint: new-e1-koszul-conormal-cycle-relations)
-/
noncomputable def koszulConormalCycleEvaluation (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex) :
    (KoszulConormalWedgeCycle A I n →₀ A) →ₗ[A]
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        P.complex).homology n :=
  Finsupp.linearCombination A fun s ↦
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
        (a s.r s.g)))
      ((((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        (ExteriorAlgebra.koszulComplex A s.r (fun j ↦ (s.g j : A)))).homologyπ n s.z)

/-- Multilinearity into a quotient module already kills I² in each ideal slot. -/
private theorem ideal_alternating_descends (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (N : Type u) [AddCommGroup N] [Module A N]
    [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N]
    (F : I [⋀^Fin n]→ₗ[A] N) :
    ∃ G : I.Cotangent [⋀^Fin n]→ₗ[A ⧸ I] N,
      ∀ w : Fin n → I, G (fun j ↦ I.toCotangent (w j)) = F w := by
  classical
  have hzero (w : Fin n → I) (i : Fin n) (x : I)
      (hx : x ∈ (I • ⊤ : Submodule A I)) : F (Function.update w i x) = 0 := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rw [F.map_update_smul]
      rw [← IsScalarTower.algebraMap_smul (A ⧸ I) r]
      change Ideal.Quotient.mk I r • _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
    · intro x y hx hy
      rw [F.map_update_add, hx, hy, add_zero]
  have hupdate (w : Fin n → I) (i : Fin n) (x y : I)
      (h : I.toCotangent x = I.toCotangent y) :
      F (Function.update w i x) = F (Function.update w i y) := by
    apply sub_eq_zero.mp
    rw [← F.map_update_sub]
    exact hzero w i (x - y) ((Submodule.Quotient.eq _).mp h)
  have hcongr (w v : Fin n → I)
      (h : ∀ j, I.toCotangent (w j) = I.toCotangent (v j)) : F w = F v := by
    have hs (s : Finset (Fin n)) : F (s.piecewise w v) = F v := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.piecewise_insert]
        have he := hupdate (s.piecewise w v) i (w i) (v i) (h i)
        have hv : Function.update (s.piecewise w v) i (v i) = s.piecewise w v := by
          apply Function.update_eq_self_iff.mpr
          exact (Finset.piecewise_eq_of_notMem s w v hi).symm
        rw [hv] at he
        exact he.trans ih
    simpa using hs Finset.univ
  choose lift hlift using I.toCotangent_surjective
  let f : (Fin n → I.Cotangent) → N := fun w ↦ F (fun j ↦ lift (w j))
  have hf (w : Fin n → I) : f (fun j ↦ I.toCotangent (w j)) = F w := by
    exact hcongr _ _ (fun j ↦ hlift (I.toCotangent (w j)))
  have hrep (w : Fin n → I.Cotangent) :
      (fun j ↦ I.toCotangent (lift (w j))) = w := funext fun j ↦ hlift (w j)
  have hquot_update (w : Fin n → I) (i : Fin n) (x : I) :
      (fun j ↦ I.toCotangent (Function.update w i x j)) =
        Function.update (fun j ↦ I.toCotangent (w j)) i (I.toCotangent x) := by
    ext j
    by_cases h : j = i <;> simp [h]
  have hu (w : Fin n → I.Cotangent) (i : Fin n) (x : I) :
      f (Function.update w i (I.toCotangent x)) =
        F (Function.update (fun j ↦ lift (w j)) i x) := by
    have he := hf (Function.update (fun j ↦ lift (w j)) i x)
    rw [hquot_update, hrep] at he
    exact he
  refine ⟨{ toFun := f
            map_update_add' := ?_
            map_update_smul' := ?_
            map_eq_zero_of_eq' := ?_ }, hf⟩
  · intro inst w i x y
    cases Subsingleton.elim inst (instDecidableEqFin n)
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective y
    rw [← map_add]
    simp only [hu, F.map_update_add]
  · intro inst w i c x
    cases Subsingleton.elim inst (instDecidableEqFin n)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective x
    change f (Function.update w i (algebraMap A (A ⧸ I) a • I.toCotangent b)) =
      algebraMap A (A ⧸ I) a • f (Function.update w i (I.toCotangent b))
    simp only [IsScalarTower.algebraMap_smul]
    rw [← map_smul]
    simp only [hu, F.map_update_smul]
  · intro w i j hij hne
    exact F.map_eq_zero_of_eq _ (congrArg lift hij) hne

/-- Every exterior-conormal relation among Koszul wedge cycles evaluates to zero
in resolution homology. There is no comparison map or derived-functor object in
this assertion: it is a kernel inclusion for two explicitly constructed linear maps.
Source: Stacks Project, Tag 09PQ (strict Tor product), Tag 00LS (comparison homotopies).
(blueprint: new-e1-koszul-conormal-cycle-relations).

Proof: Compute the homology using a free strictly commutative Tate resolution Q.
An element x of I lifts to degree one with differential x; its homology class
after tensoring with A/I depends only on x modulo I². Additivity and the A/I
scalar rule follow by adding and scaling lifts; changing a lift changes its
class by a boundary, by exactness before tensoring. Products of these degree-one
classes are alternating, including in characteristic two, since the Tate algebra
is strictly commutative. Therefore they satisfy the additive, balanced, and
alternating relations defining the exterior power of I/I² over A/I. Choose
Koszul-to-Q dg algebra maps by lifting the tuple elements in degree one; on a
wedge they give exactly these products. A comparison Q -> P induces an
isomorphism after tensoring and passing to homology. Its composite with each
Koszul map is homotopic to the specified a by Tag 00LS, because Koszul terms
are free and both maps preserve augmentation. Tensoring preserves the homotopy,
so their homology maps agree. Thus the specified evaluation also respects all
the relations, proving the kernel inclusion by linearity. Cycle representatives
with the same image under iCycles agree because iCycles is monic. In degree
zero the empty product is the quotient unit and is killed by I; for I=A all
quotient tensor complexes vanish; for I=0 all positive conormal wedges vanish. -/
theorem koszulConormalCycleEvaluation_ker (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ∀ (r : ℕ) (g : Fin r → I),
      ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
    (ha : ∀ (r : ℕ) (g : Fin r → I), (a r g).f 0 ≫ P.π.f 0 =
      ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) :
    LinearMap.ker (koszulConormalCyclePresentation A I n) ≤
      LinearMap.ker (koszulConormalCycleEvaluation A I n P a) := by
  classical
  obtain ⟨b, F, hb, hF⟩ := koszul_ideal_alternating_products A I n P
  obtain ⟨G, hG⟩ := ideal_alternating_descends A I n _ F
  let d : conormalExteriorModule A I n →ₗ[A]
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
        P.complex).homology n :=
    (Submodule.torsionBySet A _ (I : Set A)).subtype.comp
      ((exteriorPower.alternatingMapLinearEquiv G).restrictScalars A)
  have hd (s : KoszulConormalWedgeCycle A I n) :
      d (koszulConormalCyclePresentation A I n (Finsupp.single s 1)) =
        koszulConormalCycleEvaluation A I n P a (Finsupp.single s 1) := by
    simp only [koszulConormalCyclePresentation, koszulConormalCycleEvaluation,
      Finsupp.linearCombination_single, one_smul]
    change (exteriorPower.alternatingMapLinearEquiv G
      (exteriorPower.ιMulti (A ⧸ I) n
        (fun j ↦ I.toCotangent (Finsupp.linearCombination A s.g (s.v j))))).val = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hG, hF]
    obtain ⟨h⟩ := koszul_augmentation_lifts_homotopic A I s.r s.g P
      (b s.r s.g) (a s.r s.g) ((hb s.r s.g).trans (ha s.r s.g).symm)
    have heq := ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomotopy h).homologyMap_eq n
    change (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
      (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
        (b s.r s.g)) =
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
        (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).map
          (a s.r s.g)) at heq
    rw [heq]
  have heq : d.comp (koszulConormalCyclePresentation A I n) =
      koszulConormalCycleEvaluation A I n P a := by
    apply Finsupp.lhom_ext
    intro s c
    have hc : Finsupp.single s c = c • Finsupp.single s (1 : A) := by simp
    rw [hc, map_smul, map_smul]
    exact congrArg (fun y ↦ c • y) (hd s)
  intro x hx
  change koszulConormalCycleEvaluation A I n P a x = 0
  rw [← heq, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

end AlgebraicGeometry
