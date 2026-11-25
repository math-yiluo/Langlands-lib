/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import WeilConjectures.RingTheory.KoszulDerivedTopEvaluation
import WeilConjectures.RingTheory.KoszulConormalBasis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Koszul roofs and normalized comparisons

Source: Stacks Project, Tags 0BQZ and 0BQY, local finite free Koszul computation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem pairingDual_injective_of_basis
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (b : Module.Basis (Fin r) R M) (n : ℕ) :
    Function.Injective (exteriorPower.pairingDual R M n) := by
  classical
  let bd := b.dualBasis.exteriorPower n
  have hc (s : Set.powersetCard (Fin r) n) :
      bd.coord s = (exteriorPower.pairingDual R M n).flip
        ((b.exteriorPower n) s) := by
    apply bd.ext
    intro t
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, LinearMap.flip_apply]
    simp only [bd, exteriorPower.basis_apply]
    change (if t = s then 1 else 0) =
      exteriorPower.pairingDual R M n
        (exteriorPower.ιMulti_family R n b.dualBasis t)
        (exteriorPower.ιMulti_family R n b s)
    by_cases h : t = s
    · subst t
      simpa [exteriorPower.ιMultiDual, Module.Basis.dualBasis_apply] using
        (exteriorPower.ιMultiDual_apply_diag R n b s).symm
    · simpa [h, exteriorPower.ιMultiDual, Module.Basis.dualBasis_apply] using
        (exteriorPower.ιMultiDual_apply_nondiag R n b t s h).symm
  intro w w' h
  apply bd.repr.injective
  ext s
  change bd.coord s w = bd.coord s w'
  rw [hc]
  exact DFunLike.congr_fun h _

private theorem conormalVector_comp
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f) :
    (koszulConormalVector A I r g hg).comp t = koszulConormalVector A I r f hf := by
  have heval (k : Fin r → A) (hk : Ideal.span (Set.range k) = I)
      (v : Fin r →₀ A) :
      I.cotangentToQuotientSquare (koszulConormalVector A I r k hk v) =
        (I ^ 2).mkQ (Finsupp.linearCombination A k v) := by
    simp only [koszulConormalVector, Finsupp.linearCombination_apply,
      map_finsuppSum, map_smul, Ideal.toCotangent_to_quotient_square,
      Submodule.mkQ_apply]
  apply LinearMap.ext
  intro v
  apply I.cotangentToQuotientSquare_injective
  simp only [LinearMap.comp_apply]
  rw [heval, heval]
  exact congrArg ((I ^ 2).mkQ) (LinearMap.congr_fun ht v)

private theorem conormalVector_surjective
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    Function.Surjective (koszulConormalVector A I r f hf) := by
  have hspan : Submodule.span A
      (Set.range (fun i ↦ I.toCotangent
        ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩)) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
    have hx : (x : A) ∈ Ideal.span (Set.range f) := hf.symm ▸ x.property
    refine Submodule.span_induction
      (p := fun z hz ↦ I.toCotangent ⟨z, hf ▸ hz⟩ ∈ _)
      ?_ ?_ ?_ ?_ hx
    · rintro z ⟨j, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self j)
    · change I.toCotangent 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy hxx hyy
      change I.toCotangent (⟨x, hf ▸ hx⟩ + ⟨y, hf ▸ hy⟩) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hxx hyy
    · intro a x hx hxx
      change I.toCotangent (a • ⟨x, hf ▸ hx⟩) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a hxx
  apply LinearMap.range_eq_top.mp
  simpa only [koszulConormalVector, Finsupp.range_linearCombination] using hspan

/-- Equal roofs have the same normalized conormal value on different generators.
Source: Stacks Project, Tags 0BQY and 0BQZ, determinant classes and the map on
Ext induced by A -> A/I (blueprint: lem-sc-koszul-roof-comparison-independence).

Proof: Express each f_i as a linear combination of the g_j, producing t with
linearCombination g composed with t = linearCombination f. Its exterior powers
form a Koszul chain map K(f) -> K(g): contraction commutes with exterior powers
by the equation on the generator functionals. In degree zero it is the identity,
so the normalized augmentations commute with its integer extension. Thus pulling
z_g back along this chain map represents the same roof class as z_g. Equality of
the two displayed derived morphisms first permits cancellation of the common
single shift isomorphism on the right. Precompose with Q(epsilon_f), and use
u followed by epsilon_g = epsilon_f to cancel Q(epsilon_g) with its inverse.
This gives Q(z_f)=Q(u followed by z_g). Each natural-number Koszul term is free
by its finite exterior basis and hence projective. The integer extension is zero
above 0, so CochainComplex.isKProjective_of_projective at bound 0 applies (also
the extension instance in HomotopyCategory/KProjective.lean:126). Naturality of
quotientCompQhIso transfers the equality to Qh of the two homotopy classes.
Injectivity of CochainComplex.IsKProjective.Qh_map_bijective reflects this to
equality of homotopy classes; HomotopyCategory.homotopyOfEq extracts a homotopy.
Equivalently, shift the maps to single(A,0)[r], use Cocycle.equivHomShift and
CohomologyClass.toHom_bijective to obtain equality of their degree-r cocycle
classes. The equations mk_sub and mk_eq_zero_iff say their difference is a
coboundary. Cocycle.toSingleMk_mem_coboundaries_iff extracts its top component
as E_f.d(-r,1-r) followed by a map E_f^(1-r) to A. For r>0, transport this to
precomposition with d_(r,r-1); it is a signed dual boundary after absorbing the
unit (-1)^r. For r=0, E_f^1=0 and the difference is zero. All boundary values lie
in I because contraction with f is a sum of terms multiplied by f_i.
The normalized comparison kills it by reduction modulo I. Finally the two
normalized comparisons agree on pullback of a top functional: c_g composed with
t equals c_f, exterior powers take wedges to wedges of their images, and the
normalization equations coincide on every conormal wedge. The conormal basis
makes the determinant pairing injective, proving equality of the values.
For r=0 the chain map is the identity on A and there are no top coboundaries;
for a zero quotient both conormal determinant values vanish. -/
theorem koszul_roof_comparison_independent
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (ψ : koszulDualComplex A r g ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ)
    (hψ : IsKoszulConormalComparison A I r g hg ψ)
    (εf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (εg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    [QuasiIso εf] [QuasiIso εg]
    (haugf : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εf.f 0 (((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (haugg : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εg.f 0 (((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (zf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (zg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (heq : inv (DerivedCategory.Q.map εf) ≫ DerivedCategory.Q.map zf ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A) =
      inv (DerivedCategory.Q.map εg) ≫ DerivedCategory.Q.map zg ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A)) :
    koszulComparisonValue A I r f φ ((((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zf.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) =
      koszulComparisonValue A I r g ψ ((((koszulComplex A r g).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) := by
  classical
  have hmem (i : Fin r) : f i ∈ Submodule.span A (Set.range g) := by
    change f i ∈ Ideal.span (Set.range g)
    rw [hg, ← hf]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hex (i : Fin r) : ∃ v : Fin r →₀ A, Finsupp.linearCombination A g v = f i := by
    rw [← Finsupp.range_linearCombination] at hmem
    exact hmem i
  choose a ha using hex
  let t := Finsupp.linearCombination A a
  have ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f := by
    apply Finsupp.lhom_ext
    intro i c
    simp [t, ha]
  obtain ⟨U, hU, hUt⟩ := exists_koszul_generator_chain_map A I r f g t ht
    εf εg haugf haugg
  have heq' : inv (DerivedCategory.Q.map εf) ≫ DerivedCategory.Q.map zf =
      inv (DerivedCategory.Q.map εg) ≫ DerivedCategory.Q.map zg := by
    apply (cancel_mono
      (((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
        (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
          (ModuleCat.of A A))).mp
    simpa only [Category.assoc] using heq
  have hz : DerivedCategory.Q.map zf = DerivedCategory.Q.map (U ≫ zg) := by
    have hh := congrArg (fun k ↦ DerivedCategory.Q.map εf ≫ k) heq'
    simp only [IsIso.hom_inv_id_assoc] at hh
    rw [← hU, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc] at hh
    simpa only [Functor.map_comp] using hh
  have hev := koszul_derived_top_evaluation_eq A I r f hf zf (U ≫ zg) hz
  obtain ⟨b, _hb⟩ := exists_koszul_conormal_basis A I r f hregf hf
  apply pairingDual_injective_of_basis b r
  apply exteriorPower.linearMap_ext
  ext v
  choose w hw using fun i ↦ conormalVector_surjective A I r f hf (v i)
  have hc := conormalVector_comp A I r f g hf hg t ht
  have hwv : (fun i ↦ koszulConormalVector A I r f hf (w i)) = v := funext hw
  have hv : (fun i ↦ koszulConormalVector A I r g hg (t (w i))) = v := by
    funext i
    exact (LinearMap.congr_fun hc (w i)).trans (hw i)
  have heval := hev w
  have htop :
      ((koszulComplex A r f).extendXIso ComplexShape.embeddingDownNat
        (i := r) rfl).inv ≫ (U ≫ zg).f (-(r : ℤ)) =
      ModuleCat.ofHom (exteriorPower.map r t) ≫
        ((koszulComplex A r g).extendXIso ComplexShape.embeddingDownNat
          (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, hUt, Category.assoc]
  have heval' :
      Ideal.Quotient.mk I
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom
          (zf.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := r) rfl).inv
              (exteriorPower.ιMulti A r w)))) =
      Ideal.Quotient.mk I
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom
          (zg.f (-(r : ℤ)) (((koszulComplex A r g).extendXIso
            ComplexShape.embeddingDownNat (i := r) rfl).inv
              (exteriorPower.ιMulti A r (fun i ↦ t (w i)))))) := by
    have hh := congrArg (fun k ↦ k (exteriorPower.ιMulti A r w)) htop
    change (U ≫ zg).f (-(r : ℤ))
        (((koszulComplex A r f).extendXIso ComplexShape.embeddingDownNat
          (i := r) rfl).inv (exteriorPower.ιMulti A r w)) =
      zg.f (-(r : ℤ))
        (((koszulComplex A r g).extendXIso ComplexShape.embeddingDownNat
          (i := r) rfl).inv (exteriorPower.map r t (exteriorPower.ιMulti A r w))) at hh
    rw [exteriorPower.map_apply_ιMulti] at hh
    exact heval.trans (congrArg (fun x ↦ Ideal.Quotient.mk I
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
        (ModuleCat.of A A)).hom x)) hh)
  have hp := hφ
    (((koszulComplex A r f).extendXIso ComplexShape.embeddingDownNat
      (i := r) rfl).inv ≫ zf.f (-(r : ℤ)) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
        (ModuleCat.of A A)).hom) w
  have hq := hψ
    (((koszulComplex A r g).extendXIso ComplexShape.embeddingDownNat
      (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
        (ModuleCat.of A A)).hom) (fun i ↦ t (w i))
  rw [hwv] at hp
  rw [hv] at hq
  exact hp.trans ((congrArg (fun x ↦ (-1 : A ⧸ I) ^ (r * (r - 1) / 2) * x)
    heval').trans hq.symm)

end ExteriorAlgebra
