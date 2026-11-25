/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import all WeilConjectures.RingTheory.KoszulProjectiveResolution

/-! # The Koszul resolution with its specified quotient augmentation

Source: Stacks Project, Tags 0623, 062E and 0BQZ.
(blueprint: new-d3-koszul-normalized-projective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The Koszul complex of a Koszul-regular sequence resolves its quotient.
Source: Stacks Project, Tag 0623 (the Koszul complex), Tag 062E (Koszul
regularity), and Tag 0BQZ (the finite free resolution used in the Ext calculation).
(blueprint: new-d3-koszul-normalized-projective-resolution).

Proof: In degree zero use the exterior-power isomorphism wedge^0(A^r) = A
and the quotient map A -> A/I; in higher degrees use zero. Contraction in degree
one sends the standard basis vector e_i to f_i, so its image in degree zero is
span(range f) = I. The quotient map therefore kills d_1 and defines the chain
augmentation. Its degree-zero homology map is an isomorphism by the cokernel
universal property. In positive degrees source homology is zero by hreg and
homology of the single complex is zero, so the augmentation is a
quasi-isomorphism in every degree. Finally, the exterior basis induced by the
standard basis of Fin r ->_0 A makes every term free, hence projective. Bundle
these data as a ProjectiveResolution with exactly the original chain complex.
For r = 0 the augmentation is the isomorphism A -> A/(0); no properness of I
is needed, so the construction also applies when A/I is zero. -/
theorem exists_koszul_normalized_projective_resolution
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)),
      ∃ a : koszulComplex A r f ≅ P.complex,
        a.hom.f 0 ≫ P.π.f 0 =
          ModuleCat.ofHom (I.mkQ.comp
            (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) := by
  let K := koszulComplex A r f
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) :=
    ModuleCat.ofHom (I.mkQ.comp (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)
  have hq (x : K.X 0) : q x =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := rfl
  have hmem (v : Fin r →₀ A) : Finsupp.linearCombination A f v ∈ I := by
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
  have hz : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change I.mkQ (exteriorPower.zeroEquiv A (Fin r →₀ A)
      (koszulBoundary A r f 0 x)) = 0
    rw [koszulBoundary_zero_quotient_formula]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hmem _)
  let ε₀ := (ChainComplex.toSingle₀Equiv K (ModuleCat.of A (A ⧸ I))).symm ⟨q, hz⟩
  have hε₀ : ε₀.f 0 = q := ChainComplex.toSingle₀Equiv_symm_apply_f_zero q hz
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(exteriorPower.zeroEquiv A (Fin r →₀ A)).symm a, by simp [hq, ha]⟩
  have hex : (ShortComplex.mk (K.d 1 0) q hz).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hxI : exteriorPower.zeroEquiv A (Fin r →₀ A) x ∈ I :=
      (Submodule.Quotient.mk_eq_zero I).mp hx
    rw [← hf, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination] at hxI
    obtain ⟨v, hv⟩ := hxI
    refine ⟨(exteriorPower.oneEquiv A (Fin r →₀ A)).symm v, ?_⟩
    apply (exteriorPower.zeroEquiv A (Fin r →₀ A)).injective
    change exteriorPower.zeroEquiv A (Fin r →₀ A)
      (koszulBoundary A r f 0 _) = _
    rw [koszulBoundary_zero_quotient_formula, LinearEquiv.apply_symm_apply, hv]
  have hqi : QuasiIso ε₀ := by
    constructor
    intro n
    by_cases hn : n = 0
    · subst n
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_isIso_descOpcycles _ (by simp) (by simp) (by simp)]
      let S := K.sc' 1 0 0
      have : Epi q := (ModuleCat.epi_iff_surjective q).mpr hsurj
      let ei := S.isoOpcyclesOfIsColimit hex.gIsCokernel
      have heq : S.descOpcycles
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat A)
            (ComplexShape.down ℕ) 1 0 0).map ε₀).τ₂
          (by change K.d 1 0 ≫ ε₀.f 0 = 0; rw [hε₀]; exact hz) = ei.inv := by
        apply (cancel_epi S.pOpcycles).mp
        simp only [ShortComplex.p_descOpcycles,
          ShortComplex.pOpcycles_π_isoOpcyclesOfIsColimit_inv, ei]
        exact hε₀
      rw [heq]
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hn
      · exact (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr (hreg n hn)
  refine ⟨{ complex := K, π := ε₀, quasiIso := hqi, projective := ?_ }, Iso.refl K, ?_⟩
  · intro n
    change Projective (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)))
    exact ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n)
  · change 𝟙 _ ≫ ε₀.f 0 = q
    rw [Category.id_comp]
    exact hε₀

end ExteriorAlgebra
