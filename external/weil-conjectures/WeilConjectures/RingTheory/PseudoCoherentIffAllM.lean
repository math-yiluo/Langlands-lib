/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import WeilConjectures.RingTheory.FiniteConeFreeModel

/-!
# Pseudo-coherence and degreewise pseudo-coherence

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U
(blueprint: lem-pc-ring-pseudo-coherent-iff-all-m).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

private theorem truncIndex (m i : ℤ) (hi : m ≤ i) :
    (ComplexShape.embeddingUpIntGE m).f (i - m).toNat = i := by
  simp only [ComplexShape.embeddingUpIntGE_f]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

private noncomputable def brutalInclusion {R : Type u} [CommRing R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (m : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE m) ⟶ E where
  f i := if hi : m ≤ i then (E.stupidTruncXIso _ (truncIndex m i hi)).hom else 0
  comm' i j hij := by
    classical
    by_cases hi : m ≤ i
    · have hj : m ≤ j := by
        simp only [ComplexShape.up_Rel] at hij
        omega
      simp only [dite_eq_left hi, dite_eq_left hj]
      change (E.stupidTruncXIso _ (truncIndex m i hi)).hom ≫ E.d i j = _
      dsimp only [HomologicalComplex.stupidTrunc]
      rw [(E.restriction (ComplexShape.embeddingUpIntGE m)).extend_d_eq _
        (truncIndex m i hi) (truncIndex m j hj)]
      rw [HomologicalComplex.restriction_d_eq _ _
        (truncIndex m i hi) (truncIndex m j hj)]
      simp only [HomologicalComplex.stupidTruncXIso, Iso.trans_hom, Category.assoc,
        Iso.inv_hom_id_assoc, HomologicalComplex.restrictionXIso, Iso.inv_hom_id, Category.comp_id]
    · apply (E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE m) i ?_).eq_of_src
      intro k hk
      simp only [ComplexShape.embeddingUpIntGE_f] at hk
      omega

private theorem brutalInclusion_isIso_f {R : Type u} [CommRing R]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (m i : ℤ) (hi : m ≤ i) :
    IsIso ((brutalInclusion E m).f i) := by
  dsimp [brutalInclusion]
  simp only [dite_eq_left hi]
  infer_instance

private theorem boundedFiniteFree_isMPseudoCoherent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b m : ℤ)
    (ha : E.IsStrictlyGE a) (hb : E.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) :
    IsMPseudoCoherent m (Q.obj E) := by
  refine ⟨E, a, b, ha, hb, hfree, 𝟙 _, ?_, ?_⟩
  · intro i hi
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  · rw [CategoryTheory.Functor.map_id]
    infer_instance

private theorem brutal_isMPseudoCoherent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (b m : ℤ)
    (hb : E.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) :
    IsMPseudoCoherent m (Q.obj E) := by
  let B := E.stupidTrunc (ComplexShape.embeddingUpIntGE m)
  let f := brutalInclusion E m
  have hBfree : ∀ i : ℤ, Module.Free R (B.X i) ∧ Module.Finite R (B.X i) := by
    intro i
    by_cases hi : m ≤ i
    · have := (hfree i).1
      have := (hfree i).2
      let e := (E.stupidTruncXIso _ (truncIndex m i hi)).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
    · have : Subsingleton (B.X i) := ModuleCat.subsingleton_of_isZero
        (E.isZero_stupidTrunc_X _ i (by
          intro k hk
          simp only [ComplexShape.embeddingUpIntGE_f] at hk
          omega))
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨B, m, b, inferInstance, inferInstance, hBfree, Q.map f, ?_, ?_⟩
  · intro i hi
    have hprev : IsIso (f.f ((ComplexShape.up ℤ).prev i)) :=
      brutalInclusion_isIso_f E m _ (by simp; omega)
    have hmid : IsIso (f.f i) := brutalInclusion_isIso_f E m i (by omega)
    have hnext : IsIso (f.f ((ComplexShape.up ℤ).next i)) :=
      brutalInclusion_isIso_f E m _ (by simp; omega)
    have hhom : IsIso (HomologicalComplex.homologyMap f i) := by
      change IsIso (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map f))
      exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
        (show Epi (f.f ((ComplexShape.up ℤ).prev i)) from inferInstance)
        hmid (show Mono (f.f ((ComplexShape.up ℤ).next i)) from inferInstance)
    have := hhom
    have hn := homologyFunctorFactors_hom_naturality f i
    have : IsIso ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map f) ≫
        (homologyFunctorFactors (ModuleCat.{v} R) i).hom.app E) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((homologyFunctorFactors (ModuleCat.{v} R) i).hom.app E)
  · have hmid : IsIso (f.f m) := brutalInclusion_isIso_f E m m le_rfl
    have hnext : IsIso (f.f ((ComplexShape.up ℤ).next m)) :=
      brutalInclusion_isIso_f E m _ (by simp)
    have hhom : Epi (HomologicalComplex.homologyMap f m) := by
      change Epi (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) m).map f))
      apply ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      have hc := ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) m).map f)
        hmid (show Mono (f.f ((ComplexShape.up ℤ).next m)) from inferInstance)
      have := hc
      infer_instance
    have := hhom
    have hn := homologyFunctorFactors_hom_naturality f m
    have : Epi ((homologyFunctor (ModuleCat.{v} R) m).map (Q.map f) ≫
        (homologyFunctorFactors (ModuleCat.{v} R) m).hom.app E) := by
      rw [hn]
      infer_instance
    exact (epi_comp_iff_of_isIso _
      ((homologyFunctorFactors (ModuleCat.{v} R) m).hom.app E)).mp inferInstance


/-- Pseudo-coherence is equivalent to every fixed-degree approximation condition.

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U.
(blueprint: lem-pc-ring-pseudo-coherent-iff-all-m).

Proof: brutally truncate a bounded above finite free representative in degrees at least
`m`. Its inclusion is an isomorphism on cohomology above `m` and an epimorphism at `m`;
compose with the representative's derived isomorphism to obtain the forward implication.
For the converse, the degree-zero witness supplies an upper cohomology bound. A bounded
finite free `F` is `(n + 1)`-pseudo-coherent via its identity. Applied to the cone
triangle of any chain map `F → C`, the distinguished-triangle lemma makes the cone
`n`-pseudo-coherent. If the cone vanishes above `n`, the finite-cohomology lemma makes
its degree-`n` cohomology finite. The descending construction
`exists_finiteFree_model_of_finite_cones` now supplies a bounded above finite free
complex and a quasi-isomorphism to `C`.
If the ring does not fit in the module universe, every free module in that universe is
zero: a nonzero free module has a faithful scalar action, which injects the ring into
its endomorphism type. Each approximation witness is then zero, so the isomorphism
condition at degree `i` in the `(i - 1)` witness forces `H^i(C) = 0`. The zero complex
is the required finite free representative in this case. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) :
    IsPseudoCoherent (Q.obj C) ↔ ∀ m : ℤ, IsMPseudoCoherent m (Q.obj C) := by
  constructor
  · rintro ⟨E, b, hb, hfree, ⟨e⟩⟩ m
    obtain ⟨F, a, c, ha, hc, hFfree, f, hf, hepi⟩ :=
      brutal_isMPseudoCoherent E b m hb hfree
    refine ⟨F, a, c, ha, hc, hFfree, f ≫ e.hom, ?_, ?_⟩
    · intro i hi
      have := hf i hi
      rw [CategoryTheory.Functor.map_comp]
      infer_instance
    · have := hepi
      rw [CategoryTheory.Functor.map_comp]
      infer_instance
  · intro hC
    classical
    by_cases hsmall : Small.{v} R
    · have := hsmall
      obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := hC 0
      have hvan : ∀ i : ℤ, max b 0 < i →
          Limits.IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj C)) := by
        intro i hi
        have := hb
        have := hf i (by omega)
        exact ((Q.obj E).isZero_of_isLE b i (by omega)).of_iso
          (asIso ((homologyFunctor (ModuleCat.{v} R) i).map f)).symm
      have hcone : ∀ (F : CochainComplex (ModuleCat.{v} R) ℤ) (a c : ℤ),
          F.IsStrictlyGE a → F.IsStrictlyLE c →
          (∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i)) →
          ∀ (g : F ⟶ C) (n : ℤ),
            (∀ i : ℤ, n < i → Limits.IsZero
              ((homologyFunctor (ModuleCat.{v} R) i).obj
                (Q.obj (CochainComplex.mappingCone g)))) →
            Module.Finite R ((homologyFunctor (ModuleCat.{v} R) n).obj
              (Q.obj (CochainComplex.mappingCone g))) := by
        intro F a c ha hc hFfree g n hzero
        have hF := boundedFiniteFree_isMPseudoCoherent F a c (n + 1) ha hc hFfree
        have htri := (CategoryTheory.isMPseudoCoherent_of_distinguished_triangle R n
          (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g))
          (mappingCone_triangle_distinguished g)).1 hF (hC n)
        exact finite_homology_of_isMPseudoCoherent n (CochainComplex.mappingCone g)
          htri hzero
      obtain ⟨F, hF, hfree, g, hg⟩ :=
        exists_finiteFree_model_of_finite_cones R C (max b 0) hvan hcone
      have := (isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) g).mpr hg
      exact ⟨F, max b 0, hF, hfree, ⟨asIso (Q.map g)⟩⟩
    · have hzero : ∀ i : ℤ,
          Limits.IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj C)) := by
        intro i
        obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := hC (i - 1)
        have hE : Limits.IsZero E := by
          apply (Limits.IsZero.iff_id_eq_zero _).mpr
          apply HomologicalComplex.hom_ext
          intro j
          have := (hfree j).1
          have : Subsingleton (E.X j) := by
            by_contra hsub
            have : Nontrivial (E.X j) := not_subsingleton_iff_nontrivial.mp hsub
            exact hsmall (small_of_injective
              (smul_left_injective' (M := R) (α := E.X j)))
          exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).eq_of_src _ _
        have := hf i (by omega)
        exact ((homologyFunctor (ModuleCat.{v} R) i).map_isZero (Q.map_isZero hE)).of_iso
          (asIso ((homologyFunctor (ModuleCat.{v} R) i).map f)).symm
      let Z : CochainComplex (ModuleCat.{v} R) ℤ := HomologicalComplex.zero
      have hZ : Limits.IsZero Z := HomologicalComplex.isZero_zero
      have hZfree : ∀ i : ℤ, Module.Free R (Z.X i) ∧ Module.Finite R (Z.X i) := by
        intro i
        have : Subsingleton (Z.X i) := ModuleCat.subsingleton_of_isZero
          ((HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero hZ)
        exact ⟨inferInstance, inferInstance⟩
      have hg : QuasiIso (0 : Z ⟶ C) := by
        rw [quasiIso_iff]
        intro i
        rw [quasiIsoAt_iff_isIso_homologyMap]
        have hsource : Limits.IsZero (Z.homology i) :=
          (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero hZ
        have htarget : Limits.IsZero (C.homology i) :=
          (hzero i).of_iso ((homologyFunctorFactors (ModuleCat.{v} R) i).symm.app C)
        exact Limits.IsZero.isIso hsource htarget _
      have := (isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) (0 : Z ⟶ C)).mpr hg
      refine ⟨Z, 0, ?_, hZfree, ⟨asIso (Q.map (0 : Z ⟶ C))⟩⟩
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero hZ

end DerivedCategory
