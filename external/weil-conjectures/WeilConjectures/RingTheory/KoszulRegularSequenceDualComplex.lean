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
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.KoszulCoefficientExtension
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.KoszulExtRoofRepresentatives
import WeilConjectures.RingTheory.KoszulRoofComparisonIndependence
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulConormalComparisonExistence
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Duality for a Koszul-regular quotient

Source: Stacks Project, duality.tex, Tag 0BQZ, lemma-regular-immersion-ext, local
Koszul computation (blueprint: lem-sc-koszul-regular-sequence-dual-complex).

The comparison is normalized by the determinant pairing on the conormal module,
with the sign `(-1)^(r*(r-1)/2)` from the ordered contraction composition in Stacks.
A complex supported in degree `r` represents `⋀^r N[-r]`. The Ext comparison is
specified on roofs from the Koszul resolution, so it is independent of generators.

## Main statements

* `exists_unique_koszul_conormal_comparison`: the canonical quasi-isomorphism.
* `koszul_conormal_comparison_cohomology`: the derived and cohomological conclusions.
* `exists_koszul_quotient_augmentation`: the Koszul resolution of the quotient.
* `exists_intrinsic_koszul_ext_determinant`: the generator-independent Ext identification.
* `koszul_conormal_comparison_change_generators`: change-of-resolution compatibility.
* `koszul_conormal_comparison_localization`: compatibility with arbitrary localization.
-/

@[expose] public section

universe uT

open CategoryTheory CategoryTheory.Limits

namespace ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem pairingDual_injective_of_basis
    {R M : Type uT} [CommRing R] [AddCommGroup M] [Module R M]
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
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f g : Fin r → A)
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
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
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

/-- The uniquely normalized comparison is a quasi-isomorphism.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: (1) Koszul-regularity makes the finite free Koszul complex a resolution of
`A/I`, using `def-weil-pbc-koszul-complex` and `def-weil-pbc-koszul-regular-sequence`.
(2) The determinant pairing of `lem-sc-exterior-power-dual-pairing` identifies the
complementary exterior-power duals. (3) Evaluation on the top wedge identifies the
signed dual complex with the shifted Koszul complex; correct an anticommuting map
by a degreewise sign when the length is even. Thus only degree `r` survives.
(4) Reduction modulo `I` identifies the surviving classes with the determinant of
the dual conormal module. Ordered contractions on the top wedge contribute
`(-1)^(r*(r-1)/2)`; this evaluation formula fixes the comparison uniquely.
The formulas commute with localization and determinant changes of generators. -/
theorem exists_unique_koszul_conormal_comparison
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃! φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ ∧ QuasiIso φ := by
  obtain ⟨ψ, hψ⟩ := exists_koszul_conormal_comparison A I r f hreg hf
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
    (koszulNormalDeterminant A I r)).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨b, _hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  apply pairingDual_injective_of_basis b r
  apply exteriorPower.linearMap_ext
  ext v
  choose w hw using fun i ↦ conormalVector_surjective A I r f hf (v i)
  have hwv : (fun i ↦ koszulConormalVector A I r f hf (w i)) = v := funext hw
  have hh := (hψ'.1 x w).trans (hψ.1 x w).symm
  rw [hwv] at hh
  convert hh using 1 <;> rfl

/-- The canonical comparison `φ`, extended by zero to integer degrees, becomes an
isomorphism in `D(A)` onto the determinant placed in degree `r`; all cohomology
vanishing outside degree `r`, and the degree-`r` identification as a `B`-module.
The restricted module `M` realizes the induced `B = A/I` action on cohomology;
the last equality ties its isomorphism to the actual canonical comparison.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Steps 1--3 of the node identify the dual with the shifted Koszul resolution,
so the only cohomology is in degree `r`. Step 4 identifies that cohomology with the
dual conormal determinant by reduction modulo `I` and the determinant pairing.
The normalized comparison is an `A`-linear quasi-isomorphism to the restriction
of this `B`-module; its localization in `D(A)` is the asserted isomorphism. -/
theorem koszul_conormal_comparison_cohomology
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ) :
    IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) ∧
    (∀ i : ℤ, i ≠ (r : ℤ) → IsZero ((koszulDualCochainComplex A r f).homology i)) ∧
    ∃ (M : ModuleCat.{uT} (A ⧸ I))
      (ι : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M ≅
        (koszulDualComplex A r f).homology r)
      (e : M ≅ ModuleCat.of (A ⧸ I)
        (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))),
      ∀ z : (koszulDualComplex A r f).cycles r,
        e.hom (ι.inv ((koszulDualComplex A r f).homologyπ r z)) =
          koszulComparisonValue A I r f φ ((koszulDualComplex A r f).iCycles r z) := by
  obtain ⟨ψ, hψ, _huniq⟩ := exists_unique_koszul_conormal_comparison A I r f hreg hf
  obtain ⟨b, _hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  have hsame : φ = ψ := by
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
      (koszulNormalDeterminant A I r)).hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply pairingDual_injective_of_basis b r
    apply exteriorPower.linearMap_ext
    ext v
    choose w hw using fun i ↦ conormalVector_surjective A I r f hf (v i)
    have hwv : (fun i ↦ koszulConormalVector A I r f hf (w i)) = v := funext hw
    have hh := (hφ x w).trans (hψ.1 x w).symm
    rw [hwv] at hh
    convert hh using 1 <;> rfl
  have hq : QuasiIso φ := hsame ▸ hψ.2
  let := hq
  have : QuasiIso (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff φ ComplexShape.embeddingUpNat).mpr hq
  refine ⟨by infer_instance, ?_, ?_⟩
  · intro i hi
    let η := HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat
    let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (koszulNormalDeterminant A I r) r (r : ℤ) rfl
    let : QuasiIso η := inferInstance
    let : QuasiIso (η ≫ e.hom) := inferInstance
    exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (r : ℤ)
      (koszulNormalDeterminant A I r) i hi).of_iso
        (asIso (HomologicalComplex.homologyMap (η ≫ e.hom) i))
  · let e := asIso (HomologicalComplex.homologyMap φ r) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) r
        (koszulNormalDeterminant A I r)
    refine ⟨ModuleCat.of (A ⧸ I)
      (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent)), e.symm, Iso.refl _, ?_⟩
    intro z
    change e.hom ((koszulDualComplex A r f).homologyπ r z) = _
    have hh : (koszulDualComplex A r f).homologyπ r ≫ e.hom =
        (koszulDualComplex A r f).iCycles r ≫ φ.f r ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
            (koszulNormalDeterminant A I r)).hom := by
      simp only [e, Iso.trans_hom, asIso_hom, HomologicalComplex.homologyπ_naturality_assoc,
        HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom,
        HomologicalComplex.cyclesMap_i_assoc]
    exact congrArg (fun k ↦ k z) hh

private theorem koszulBoundary_zero_formula
    (A : Type uT) [CommRing A] (r : ℕ) (f : Fin r → A)
    (x : ⋀[A]^1 (Fin r →₀ A)) :
    exteriorPower.zeroEquiv A (Fin r →₀ A) (koszulBoundary A r f 0 x) =
      Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) := by
  have he : (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (koszulBoundary A r f 0) = (Finsupp.linearCombination A f).comp
        (exteriorPower.oneEquiv A (Fin r →₀ A)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    have hg : koszulBoundary A r f 0 (exteriorPower.ιMulti A 1 v) =
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm
          (Finsupp.linearCombination A f (v 0)) := by
      apply Subtype.ext
      simp [koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
        Algebra.algebraMap_eq_smul_one]
    simp [hg]
  exact LinearMap.congr_fun he x

set_option backward.isDefEq.respectTransparency false in
/-- The Koszul augmentation is a quasi-isomorphism to the quotient in degree zero.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Step 1 uses Koszul-regularity to kill positive homology. Degree zero is the
cokernel of `d₁`, whose image is the ideal generated by `f`; the augmentation is
therefore the quotient map. Extension along `embeddingDownNat` puts degree `n`
in cohomological degree `-n`, with zero terms outside the image. -/
theorem exists_koszul_quotient_augmentation
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
        (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)),
      QuasiIso ε ∧
      ∀ x : ⋀[A]^0 (Fin r →₀ A),
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of A (A ⧸ I))).hom
          (ε.f 0 (((koszulComplex A r f).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
        Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x) := by
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
    rw [koszulBoundary_zero_formula]
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
    rw [koszulBoundary_zero_formula, LinearEquiv.apply_symm_apply, hv]
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
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
    (ModuleCat.of A (A ⧸ I)) 0 (0 : ℤ) rfl
  let ε := HomologicalComplex.extendMap ε₀ ComplexShape.embeddingDownNat ≫ e.hom
  have : QuasiIso ε₀ := hqi
  refine ⟨ε, by dsimp [ε]; infer_instance, ?_⟩
  intro x
  simp only [ε, e, K, HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ (show
    ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl),
    HomologicalComplex.extendSingleIso_hom_f, hε₀, ModuleCat.comp_apply,
    Iso.inv_hom_id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp]
  have hi (X Y : ModuleCat A) (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl
  change q ((HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
    (i := 0) rfl).hom
      ((HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat
        (i := 0) rfl).inv x)) = _
  rw [hi]
  exact hq x

/-- The intrinsic Ext determinant satisfies the normalized Koszul roof formula.
Source: Stacks Project, Tag 0BQZ.
(blueprint: lem-sc-koszul-ext-determinant-roof).
Proof: choose one generating sequence and a roof-normalized Ext/dual-homology
comparison. Compose it with the normalized conormal homology isomorphism.
Represent an arbitrary Ext class on this fixed resolution. Independence of
normalized roof values compares it with any other generating sequence, and the
conormal comparison formula gives the required determinant evaluation. -/
theorem intrinsic_ext_determinant_roof
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I) :
    ∃ e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
      koszulNormalDeterminant A I r,
    ∀ (f : Fin r → A) (_hreg : RingTheory.Sequence.IsKoszulRegular f)
        (hf : Ideal.span (Set.range f) = I)
        (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
            (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
          (v : Fin r → (Fin r →₀ A)),
          exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
            (e ((Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A))))
            (exteriorPower.ιMulti (A ⧸ I) r
              (fun i ↦ koszulConormalVector A I r f hf (v i))) =
            (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
            Ideal.Quotient.mk I
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                (ModuleCat.of A A)).hom
                (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
                  ComplexShape.embeddingDownNat (i := r) rfl).inv
                (exteriorPower.ιMulti A r v)))) := by
  obtain ⟨f₀, hreg₀, hf₀⟩ := hex
  obtain ⟨φ₀, hφ₀⟩ := exists_koszul_conormal_comparison A I r f₀ hreg₀ hf₀
  have : QuasiIso φ₀ := hφ₀.2
  obtain ⟨ε₀, hε₀, haug₀⟩ := exists_koszul_quotient_augmentation A I r f₀ hreg₀ hf₀
  have : QuasiIso ε₀ := hε₀
  obtain ⟨d, hd⟩ := exists_koszul_ext_roof_representatives A I r f₀ hreg₀ hf₀
  let c := asIso (HomologicalComplex.homologyMap φ₀ r) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) r
      (koszulNormalDeterminant A I r)
  let e := d.trans (CategoryTheory.Iso.toLinearEquiv c)
  refine ⟨e, ?_⟩
  intro f hreg hf ε hε haug z v
  obtain ⟨φ, hφ⟩ := exists_koszul_conormal_comparison A I r f hreg hf
  let x := (Abelian.Ext.homLinearEquiv (R := A)).symm
    (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
      ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
        (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
          (ModuleCat.of A A))
  obtain ⟨z₀, y, hx, hy, hz⟩ := hd ε₀ haug₀ x
  have hc : e x = koszulComparisonValue A I r f₀ φ₀
      (((koszulComplex A r f₀).extendXIso
        ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z₀.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom) := by
    change c.hom (d x) = _
    rw [hy]
    have hh : (koszulDualComplex A r f₀).homologyπ r ≫ c.hom =
        (koszulDualComplex A r f₀).iCycles r ≫ φ₀.f r ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
            (koszulNormalDeterminant A I r)).hom := by
      simp only [c, Iso.trans_hom, asIso_hom, HomologicalComplex.homologyπ_naturality_assoc,
        HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom,
        HomologicalComplex.cyclesMap_i_assoc]
    have hh' := congrArg (fun k ↦ k y) hh
    simpa only [ModuleCat.comp_apply, hz, koszulComparisonValue] using hh'
  have htransport := koszul_roof_comparison_independent A I r f₀ f hreg₀ hf₀ hf
    φ₀ φ hφ₀.1 hφ.1 ε₀ ε haug₀ haug z₀ z
    (by simpa only [x, LinearEquiv.apply_symm_apply] using
      congrArg (Abelian.Ext.homLinearEquiv (R := A)) hx.symm)
  rw [hc, htransport]
  exact hφ.1 (((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom) v

/-- The intrinsic Ext determinant is linear for the quotient action.
Source: Stacks Project, Tag 0BQZ.
(blueprint: lem-sc-koszul-ext-determinant-multiplication).
Proof: take the roof-normalized equivalence. Lift a quotient scalar to A;
its multiplication endomorphism is the lift times the identity. Ext scalar
composition and A-linearity give the restricted quotient action on the target. -/
theorem intrinsic_ext_determinant_multiplication
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I) :
    ∃ e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
        koszulNormalDeterminant A I r,
      ∀ (b : A ⧸ I)
        (x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r),
        e ((Abelian.Ext.mk₀ (ModuleCat.ofHom
          (b • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))))).comp x (zero_add r)) =
          @SMul.smul (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))
            inferInstance b (e x) := by
  obtain ⟨e, _⟩ := intrinsic_ext_determinant_roof A I r hex
  refine ⟨e, ?_⟩
  intro b x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hm : ModuleCat.ofHom
      (Ideal.Quotient.mk I c • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))) =
      c • 𝟙 (ModuleCat.of A (A ⧸ I)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  rw [hm, Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp,
    Abelian.Ext.mk₀_id_comp, map_smul]
  rfl

/-- The intrinsic Ext determinant isomorphism, normalized on every Koszul roof.
Source: Stacks Project, Tag 0BQZ.
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).
The proof takes the roof-normalized equivalence and proves its quotient linearity
by lifting quotient scalars to A and applying the Ext scalar-composition formulas.
-/
theorem exists_intrinsic_koszul_ext_determinant
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I) :
    ∃ e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
        koszulNormalDeterminant A I r,
      (∀ (b : A ⧸ I) (x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r),
        e ((Abelian.Ext.mk₀ (ModuleCat.ofHom
          (b • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))))).comp x (zero_add r)) =
          @SMul.smul (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))
            inferInstance b (e x)) ∧
    ∀ (f : Fin r → A) (_hreg : RingTheory.Sequence.IsKoszulRegular f)
        (hf : Ideal.span (Set.range f) = I)
        (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
            (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
          (v : Fin r → (Fin r →₀ A)),
          exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
            (e ((Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A))))
            (exteriorPower.ιMulti (A ⧸ I) r
              (fun i ↦ koszulConormalVector A I r f hf (v i))) =
            (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
            Ideal.Quotient.mk I
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                (ModuleCat.of A A)).hom
                (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
                  ComplexShape.embeddingDownNat (i := r) rfl).inv
                (exteriorPower.ιMulti A r v)))) := by
  obtain ⟨e, he⟩ := intrinsic_ext_determinant_roof A I r hex
  refine ⟨e, ?_, he⟩
  intro b x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hm : ModuleCat.ofHom
      (Ideal.Quotient.mk I a • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))) =
      a • 𝟙 (ModuleCat.of A (A ⧸ I)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  rw [hm, Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp,
    Abelian.Ext.mk₀_id_comp, map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The normalized comparisons commute with a change of Koszul generators.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Step 4 uses the determinant change-of-generators identity. A map `t` lifting
identity on the quotient induces the identity on conormal classes. Evaluating the
two composites on wedges gives the same determinant pairing, hence the same value.
This is the comparison of resolutions used in the intrinsic Ext isomorphism. -/
theorem koszul_conormal_comparison_change_generators
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f g : Fin r → A)
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
    (t : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (ht : (Finsupp.linearCombination A g).comp t = Finsupp.linearCombination A f) :
    ∀ x : (koszulComplex A r g).X r ⟶ ModuleCat.of A A,
      koszulComparisonValue A I r f φ
          (ModuleCat.ofHom (x.hom.comp (exteriorPower.map r t))) =
        koszulComparisonValue A I r g ψ x := by
  obtain ⟨b, _hb⟩ := exists_koszul_conormal_basis A I r f hregf hf
  intro x
  apply pairingDual_injective_of_basis b r
  apply exteriorPower.linearMap_ext
  ext v
  choose w hw using fun i ↦ conormalVector_surjective A I r f hf (v i)
  have hc := conormalVector_comp A I r f g hf hg t ht
  have hwv : (fun i ↦ koszulConormalVector A I r f hf (w i)) = v := funext hw
  have hv : (fun i ↦ koszulConormalVector A I r g hg (t (w i))) = v := by
    funext i
    exact (LinearMap.congr_fun hc (w i)).trans (hw i)
  calc
    _ = (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
        Ideal.Quotient.mk I ((x.hom.comp (exteriorPower.map r t))
          (exteriorPower.ιMulti A r w)) := by
      have hh := hφ (ModuleCat.ofHom (x.hom.comp (exteriorPower.map r t))) w
      rw [hwv] at hh
      convert hh using 1
      rfl
    _ = (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
        Ideal.Quotient.mk I (x.hom (exteriorPower.ιMulti A r (fun i ↦ t (w i)))) := by
      congr 2
      exact congrArg x.hom (exteriorPower.map_apply_ιMulti t w)
    _ = _ := by
      simpa only [LinearMap.compAlternatingMap_apply, hv] using
        (hψ x (fun i ↦ t (w i))).symm

set_option backward.isDefEq.respectTransparency false in
/-- Localization preserves regularity and the determinant-normalized comparison.
The maps `χ` and `ν` are the coefficient-extension maps on the degree-`r` dual
and normal determinant. Their evaluation equations specify the canonical maps,
and the last equation is the commutative comparison square. Since the comparison
target has only degree `r`, this is the complete complex-level compatibility.
Source: Stacks Project, Tag 0BQZ
(blueprint: lem-sc-koszul-regular-sequence-dual-complex).

Proof: Steps 1--3 use exact localization on the Koszul resolution, giving regularity
of the localized sequence. Step 4 localizes the conormal determinant pairing.
Its evaluation matrix is obtained by applying the localization ring map entrywise,
so the determinant and top dual evaluations commute with that map. The two
normalized comparison maps therefore give the asserted commutative square. -/
theorem koszul_conormal_comparison_localization
    (A : Type uT) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type uT) [CommRing S] [Algebra A S]
    [IsLocalization T S] :
    RingTheory.Sequence.IsKoszulRegular (algebraMap A S ∘ f) ∧
    ∃ hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S),
      ∃ q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)),
        (∀ b : A, q (Ideal.Quotient.mk I b) =
          Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) ∧
        ∀ (φ : koszulDualComplex A r f ⟶
            (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
              (koszulNormalDeterminant A I r))
          (ψ : koszulDualComplex S r (algebraMap A S ∘ f) ⟶
            (HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℕ) r).obj
              (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
          IsKoszulConormalComparison A I r f hf φ →
          IsKoszulConormalComparison S (I.map (algebraMap A S)) r
            (algebraMap A S ∘ f) hs ψ →
          ∃ (χ : koszulDualComplex A r f ⟶
              ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f)))
            (ν : koszulNormalDeterminant A I r →ₗ[A]
              (ModuleCat.restrictScalars (algebraMap A S)).obj
                (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
            (∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
              (v : Fin n → (Fin r →₀ A)),
              (χ.f n x).hom (exteriorPower.ιMulti S n
                (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
              algebraMap A S (x.hom (exteriorPower.ιMulti A n v))) ∧
            (∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
              exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
                (I.map (algebraMap A S)).Cotangent r (ν w)
                (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
                  (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
                    (algebraMap A S ∘ f) hs
                    ((v i).mapRange (algebraMap A S) (map_zero _)))) =
              q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
                (exteriorPower.ιMulti (A ⧸ I) r
                  (fun i ↦ koszulConormalVector A I r f hf (v i))))) ∧
            (∀ x : (koszulComplex A r f).X r ⟶ ModuleCat.of A A,
              koszulComparisonValue S (I.map (algebraMap A S)) r
                (algebraMap A S ∘ f) ψ (χ.f r x) =
              ν (koszulComparisonValue A I r f φ x)) := by
  classical
  have : Module.Flat A S := IsLocalization.flat S T
  have hregs := RingTheory.Sequence.isKoszulRegular_of_flat A S r f hreg
  have hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S) := by
    rw [← hf, Ideal.map_span, Set.range_comp]
  let q := Ideal.quotientMap (I.map (algebraMap A S)) (algebraMap A S)
    Ideal.le_comap_map
  have hq (a : A) : q (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S a) := rfl
  refine ⟨hregs, hs, q, hq, ?_⟩
  intro φ ψ hφ hψ
  obtain ⟨χ, ν, hχ, hν⟩ := exists_koszul_coefficient_extension A I r f hreg hf
    T S hs q hq
  refine ⟨χ, ν, hχ, hν, ?_⟩
  intro x
  obtain ⟨b, hb⟩ := exists_koszul_conormal_basis S (I.map (algebraMap A S)) r
    (algebraMap A S ∘ f) hregs hs
  apply pairingDual_injective_of_basis b r
  apply (b.exteriorPower r).ext
  intro t
  let k : Fin r → Fin r := fun i ↦ Set.powersetCard.ofFinEmbEquiv.symm t i
  let v : Fin r → (Fin r →₀ A) := fun i ↦ Finsupp.single (k i) 1
  have hv : (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
      (algebraMap A S ∘ f) hs ((v i).mapRange (algebraMap A S) (map_zero _))) =
      fun i ↦ b (k i) := by
    funext i
    rw [hb]
    simp only [v, Finsupp.mapRange_single, map_one]
  rw [exteriorPower.basis_apply]
  change exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r
      (koszulComparisonValue S (I.map (algebraMap A S)) r
        (algebraMap A S ∘ f) ψ (χ.f r x))
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r (fun i ↦ b (k i))) =
      exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
        (I.map (algebraMap A S)).Cotangent r
        (ν (koszulComparisonValue A I r f φ x))
        (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r (fun i ↦ b (k i)))
  rw [← hv, hψ, hχ, hν, hφ]
  simp only [map_mul, map_pow, map_neg, map_one, hq]

end ExteriorAlgebra
